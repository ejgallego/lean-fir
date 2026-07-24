import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function expectTrap(action, label) {
  try {
    action();
  } catch (error) {
    expect(error instanceof WebAssembly.RuntimeError,
      `${label} raised the wrong error type: ${error}`);
    return;
  }
  throw new Error(`${label} did not trap`);
}

function writeHeader(view, address, {
  kind = 1,
  flags,
  refCount,
  allocationBytes = 32,
  aux0 = 0,
}) {
  view.setUint32(address + 0, kind, true);
  view.setUint32(address + 4, flags, true);
  view.setUint32(address + 8, refCount, true);
  view.setUint32(address + 12, allocationBytes, true);
  view.setUint32(address + 16, aux0, true);
  view.setUint32(address + 20, 0, true);
  view.setUint32(address + 24, 0, true);
  view.setUint32(address + 28, 0, true);
}

function allocateConstructor(host) {
  return host.allocCtor({
    fields: ["tobject"],
    size: 1,
    usize: 0,
    ssize: 0,
    tag: "7",
  }, [host.encodeTagged(0n)]);
}

async function checkConcreteHost(module, entry, memoryExport) {
  const host = new ConcreteHost();
  const instance = await WebAssembly.instantiate(module, {});
  host.attachMemory(instance.exports[memoryExport]);
  const isShared = instance.exports[entry];

  const constructor = allocateConstructor(host);
  expect((isShared(constructor) >>> 0) === 0,
    "resident isShared did not recognize a unique concrete allocation");
  host.inc({ kind: "inc", amount: 1, check: false }, [constructor]);
  expect((isShared(constructor) >>> 0) === 1,
    "resident isShared did not recognize a non-unique concrete allocation");

  const promoted = host.encodeTagged(0x80000000n);
  expect((isShared(promoted) >>> 0) === 1,
    "resident isShared did not recognize a persistent promoted tag");
}

export async function checkResidentIsShared(bytes, manifest) {
  expect(WebAssembly.validate(bytes),
    "resident isShared failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  const imports = WebAssembly.Module.imports(module);
  expect(imports.length === 0,
    `resident isShared retained ${imports.length} import(s)`);
  expect(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "resident isShared descriptor retained imports");
  expect(manifest.entry === "fir_isShared", "resident isShared entry drifted");
  expect(manifest.memory === "memory", "resident isShared memory export drifted");
  expect(manifest.result === "uint8", "resident isShared result ABI drifted");
  expect(JSON.stringify(manifest.params) === JSON.stringify(["tobject"]),
    "resident isShared parameter ABI drifted");

  const exports = WebAssembly.Module.exports(module);
  expect(exports.some(({ name, kind }) => name === manifest.entry && kind === "function"),
    "resident isShared function export is missing");
  expect(exports.some(({ name, kind }) => name === manifest.memory && kind === "memory"),
    "resident isShared memory export is missing");

  const instance = await WebAssembly.instantiate(module, {});
  const isShared = instance.exports[manifest.entry];
  const memory = instance.exports[manifest.memory];
  expect(typeof isShared === "function", "resident isShared export is not callable");
  expect(memory instanceof WebAssembly.Memory, "resident memory export is not a memory");
  const view = new DataView(memory.buffer);

  expect((isShared(42 * 2 + 1) >>> 0) === 1,
    "resident isShared failed the immediate path");

  const unique = 1024;
  writeHeader(view, unique, { flags: 2, refCount: 1 });
  expect((isShared(unique) >>> 0) === 0,
    "resident isShared failed the unique-object path");

  const aliased = 2048;
  writeHeader(view, aliased, { flags: 2, refCount: 2 });
  expect((isShared(aliased) >>> 0) === 1,
    "resident isShared failed the non-unique-object path");

  const persistent = 3072;
  writeHeader(view, persistent, { flags: 3, refCount: 1 });
  expect((isShared(persistent) >>> 0) === 1,
    "resident isShared failed the persistent-object path");

  const dead = 4096;
  writeHeader(view, dead, { flags: 0, refCount: 1 });
  expectTrap(() => isShared(0), "resident isShared zero sentinel");
  expectTrap(() => isShared(6), "resident isShared misaligned word");
  expectTrap(() => isShared(dead), "resident isShared dead object");

  await checkConcreteHost(module, manifest.entry, manifest.memory);
  return "PASS import-free Wasm-resident isShared\n" +
    "PASS resident isShared reads the concrete host heap";
}

export async function checkFetchedResidentIsShared(path) {
  const [wasmResponse, manifestResponse] = await Promise.all([
    fetch(path),
    fetch(`${path}.json`),
  ]);
  expect(wasmResponse.ok,
    `failed to fetch resident isShared Wasm: ${wasmResponse.status}`);
  expect(manifestResponse.ok,
    `failed to fetch resident isShared descriptor: ${manifestResponse.status}`);
  return checkResidentIsShared(
    new Uint8Array(await wasmResponse.arrayBuffer()),
    await manifestResponse.json(),
  );
}
