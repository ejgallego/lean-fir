import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function prepareConstructor(memory, address) {
  const view = new DataView(memory.buffer);
  const header = [1, 2, 1, 64, 7, 2, 0, 16];
  header.forEach((value, index) =>
    view.setUint32(address + 4 * index, value, true));
  view.setUint32(address + 32, 11, true);
  view.setUint32(address + 36, 0, true);
  view.setUint32(address + 40, 13, true);
  view.setUint32(address + 44, 0, true);
  view.setUint8(address + 48, 17);
  view.setUint8(address + 49, 19);
}

/**
 * Check zero-import direct constructor setters against raw W6 bytes and the
 * independent ConcreteHost decoder.
 */
export async function checkResidentSetters(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident setter module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident setter memory export is missing");
  equal(typeof exports.resident_set_object, "function",
    "resident object-set export is missing");
  equal(typeof exports.resident_set_scalar, "function",
    "resident scalar-set export is missing");
  equal(typeof exports.resident_set_float32, "function",
    "resident Float32-set export is missing");
  equal(typeof exports.resident_set_float, "function",
    "resident Float-set export is missing");

  const address = 1024;
  prepareConstructor(exports.memory, address);
  const view = new DataView(exports.memory.buffer);
  view.setUint32(0, 0xdecafbad, true);
  exports.resident_set_object(address, 43);
  equal(view.getUint32(address + 40, true), 43,
    "resident object setter wrote the wrong slot");
  equal(view.getUint32(address + 44, true), 0,
    "resident object setter changed slot padding");
  equal(view.getUint32(0, true), 0xdecafbad,
    "resident object setter failed to restore scratch");
  exports.resident_set_scalar(address, 255);
  equal(view.getUint8(address + 48), 17,
    "resident scalar setter changed the preceding byte");
  equal(view.getUint8(address + 49), 255,
    "resident scalar setter wrote the wrong byte");
  equal(view.getUint32(0, true), 0xdecafbad,
    "resident scalar setter failed to restore scratch");
  exports.resident_set_float32(address, -13.25);
  equal(view.getFloat32(address + 52, true), -13.25,
    "resident Float32 setter changed the physical value");
  equal(view.getUint32(0, true), 0xdecafbad,
    "resident Float32 setter failed to restore scratch");
  exports.resident_set_float(address, -0);
  equal(view.getBigUint64(address + 56, true), 0x8000000000000000n,
    "resident Float setter did not preserve negative-zero bits");
  equal(view.getUint32(0, true), 0xdecafbad,
    "resident Float setter failed to restore scratch");

  const host = new ConcreteHost();
  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  host.attachMemory(concrete.memory);
  prepareConstructor(concrete.memory, address);
  concrete.resident_set_object(address, 47);
  concrete.resident_set_scalar(address, 251);
  equal(host.objectProj(
    { kind: "objectProj", index: 1, result: "tobject" },
    [address],
  ), 47, "ConcreteHost object projection disagrees with resident setter");
  equal(host.scalarProj(
    { kind: "scalarProj", width: 2, offset: 1, result: "uint8" },
    [address],
  ), 251, "ConcreteHost scalar projection disagrees with resident setter");

  const invalid = async (prepare, invoke, label) => {
    const { exports: candidate } = await WebAssembly.instantiate(module, {});
    prepare(candidate.memory);
    let trapped = false;
    try {
      invoke(candidate);
    } catch (error) {
      trapped = error instanceof WebAssembly.RuntimeError;
    }
    expect(trapped, `${label} did not trap`);
  };
  await invalid(
    () => {},
    (candidate) => candidate.resident_set_object(0, 1),
    "zero object setter",
  );
  await invalid(
    (memory) => prepareConstructor(memory, address),
    (candidate) => candidate.resident_set_object(address + 4, 1),
    "misaligned object setter",
  );
  await invalid(
    (memory) => {
      prepareConstructor(memory, address);
      new DataView(memory.buffer).setUint32(address + 4, 0, true);
    },
    (candidate) => candidate.resident_set_scalar(address, 1),
    "dead scalar setter",
  );
  await invalid(
    (memory) => {
      prepareConstructor(memory, address);
      new DataView(memory.buffer).setUint32(address + 20, 1, true);
    },
    (candidate) => candidate.resident_set_object(address, 1),
    "out-of-bounds object setter",
  );
  await invalid(
    (memory) => {
      prepareConstructor(memory, address);
      new DataView(memory.buffer).setUint32(address + 24, 1, true);
    },
    (candidate) => candidate.resident_set_scalar(address, 1),
    "wrong-width scalar setter",
  );

  return "PASS zero-import resident constructor setters";
}

export async function checkFetchedResidentSetters(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentSetters(await response.arrayBuffer());
}
