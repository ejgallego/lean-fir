import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function expectTrap(action, label, errorType = WebAssembly.RuntimeError) {
  try {
    action();
  } catch (error) {
    expect(error instanceof errorType,
      `${label} raised the wrong error type: ${error}`);
    return;
  }
  throw new Error(`${label} did not trap`);
}

function writeHeader(view, address, {
  kind,
  flags,
  allocationBytes,
  aux0 = 0,
}) {
  view.setUint32(address + 0, kind, true);
  view.setUint32(address + 4, flags, true);
  view.setUint32(address + 8, 1, true);
  view.setUint32(address + 12, allocationBytes, true);
  view.setUint32(address + 16, aux0, true);
  view.setUint32(address + 20, 0, true);
  view.setUint32(address + 24, 0, true);
  view.setUint32(address + 28, 0, true);
}

function allocateConstructor(host, tag) {
  return host.allocCtor({
    fields: ["tobject"],
    size: 1,
    usize: 0,
    ssize: 0,
    tag,
  }, [host.encodeTagged(0n)]) >>> 0;
}

async function checkConcreteHostAttachment(module, entry, memoryExport) {
  const dirtyMemory = new WebAssembly.Memory({ initial: 1 });
  new Uint8Array(dirtyMemory.buffer)[1024] = 1;
  expectTrap(
    () => new ConcreteHost().attachMemory(dirtyMemory),
    "concrete host dirty-memory attachment",
    Error,
  );

  const beforeAttach = new ConcreteHost();
  const beforeConstructor = allocateConstructor(beforeAttach, 11);
  const beforePromoted = beforeAttach.encodeTagged(0x80000000n);
  const beforeInstance = await WebAssembly.instantiate(module, {});
  beforeAttach.attachMemory(beforeInstance.exports[memoryExport]);
  expect(beforeAttach.buffer === beforeInstance.exports[memoryExport].buffer,
    "prebuilt concrete heap did not attach to the module memory");
  expect((beforeInstance.exports[entry](beforeConstructor) >>> 0) === 11,
    "resident getTag cannot read a constructor copied during attachment");
  expect((beforeInstance.exports[entry](beforePromoted) >>> 0) === 0x80000000,
    "resident getTag cannot read a promoted tag copied during attachment");
  beforeAttach.attachMemory(beforeInstance.exports[memoryExport]);
  expectTrap(
    () => beforeAttach.attachMemory(new WebAssembly.Memory({ initial: 1 })),
    "concrete host memory rebinding",
    Error,
  );

  const afterAttach = new ConcreteHost();
  const afterInstance = await WebAssembly.instantiate(module, {});
  const memory = afterInstance.exports[memoryExport];
  afterAttach.attachMemory(memory);
  const afterConstructor = allocateConstructor(afterAttach, 13);
  const afterPromoted = afterAttach.encodeTagged(0x80000001n);
  expect((afterInstance.exports[entry](afterConstructor) >>> 0) === 13,
    "resident getTag cannot read a constructor allocated after attachment");
  expect((afterInstance.exports[entry](afterPromoted) >>> 0) === 0x80000001,
    "resident getTag cannot read a promoted tag allocated after attachment");

  afterAttach.allocateString("x".repeat(70000));
  expect(memory.buffer.byteLength >= 2 * 65536,
    "concrete host did not grow the module-owned memory");
  expect(afterAttach.buffer === memory.buffer,
    "concrete host lost the module memory after growth");
}

export async function checkResidentGetTag(bytes, manifest) {
  expect(WebAssembly.validate(bytes), "resident getTag failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  const imports = WebAssembly.Module.imports(module);
  expect(imports.length === 0,
    `resident getTag retained ${imports.length} import(s)`);
  expect(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "resident getTag descriptor retained imports");
  expect(manifest.entry === "fir_getTag", "resident getTag entry drifted");
  expect(manifest.memory === "memory", "resident getTag memory export drifted");
  expect(manifest.result === "uint32", "resident getTag result ABI drifted");
  expect(JSON.stringify(manifest.params) === JSON.stringify(["tobject"]),
    "resident getTag parameter ABI drifted");

  const exports = WebAssembly.Module.exports(module);
  expect(exports.some(({ name, kind }) => name === manifest.entry && kind === "function"),
    "resident getTag function export is missing");
  expect(exports.some(({ name, kind }) => name === manifest.memory && kind === "memory"),
    "resident getTag memory export is missing");

  const instance = await WebAssembly.instantiate(module, {});
  const getTag = instance.exports[manifest.entry];
  const memory = instance.exports[manifest.memory];
  expect(typeof getTag === "function", "resident getTag export is not callable");
  expect(memory instanceof WebAssembly.Memory, "resident memory export is not a memory");
  const view = new DataView(memory.buffer);

  expect((getTag(42 * 2 + 1) >>> 0) === 42,
    "resident getTag failed the immediate path");

  const constructor = 1024;
  writeHeader(view, constructor, {
    kind: 1,
    flags: 2,
    allocationBytes: 32,
    aux0: 7,
  });
  expect((getTag(constructor) >>> 0) === 7,
    "resident getTag failed the constructor path");

  const promoted = 2048;
  const promotedPayload = 0x80000000n;
  writeHeader(view, promoted, {
    kind: 5,
    flags: 3,
    allocationBytes: 40,
    aux0: 1,
  });
  view.setBigUint64(promoted + 32, promotedPayload, true);
  expect((getTag(promoted) >>> 0) === Number(promotedPayload),
    "resident getTag failed the promoted-tag path");

  const dead = 3072;
  writeHeader(view, dead, {
    kind: 1,
    flags: 0,
    allocationBytes: 32,
    aux0: 9,
  });
  expectTrap(() => getTag(0), "resident getTag zero sentinel");
  expectTrap(() => getTag(6), "resident getTag misaligned word");
  expectTrap(() => getTag(dead), "resident getTag dead object");

  await checkConcreteHostAttachment(module, manifest.entry, manifest.memory);
  return "PASS import-free Wasm-resident getTag\n" +
    "PASS concrete host uses module-exported memory";
}

export async function checkFetchedResidentGetTag(path) {
  const [wasmResponse, manifestResponse] = await Promise.all([
    fetch(path),
    fetch(`${path}.json`),
  ]);
  expect(wasmResponse.ok, `failed to fetch resident getTag Wasm: ${wasmResponse.status}`);
  expect(manifestResponse.ok,
    `failed to fetch resident getTag descriptor: ${manifestResponse.status}`);
  return checkResidentGetTag(
    new Uint8Array(await wasmResponse.arrayBuffer()),
    await manifestResponse.json(),
  );
}
