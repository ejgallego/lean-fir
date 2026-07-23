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
      `${label} raised a non-WebAssembly error: ${error}`);
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

  return "PASS import-free Wasm-resident getTag";
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
