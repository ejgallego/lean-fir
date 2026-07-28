import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function prepareConstructor(memory, address, { kind = 1, flags = 2 } = {}) {
  const view = new DataView(memory.buffer);
  const header = [kind, flags, 1, 32, 7, 0, 0, 0];
  header.forEach((value, index) =>
    view.setUint32(address + 4 * index, value, true));
}

/**
 * Check the zero-import fixed-tag writer against raw W6 bytes and the
 * independent ConcreteHost decoder.
 */
export async function checkResidentTagSetter(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident tag-setter module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident tag-setter memory export is missing");
  equal(typeof exports.resident_set_tag, "function",
    "resident tag-setter entry export is missing");
  equal(typeof exports.fir_set_tag_0, "function",
    "resident tag-setter helper export is missing");

  const address = 1024;
  prepareConstructor(exports.memory, address);
  const view = new DataView(exports.memory.buffer);
  view.setUint32(0, 0xdecafbad, true);
  exports.resident_set_tag(address);
  equal(view.getUint32(address + 16, true), 14,
    "resident tag setter wrote the wrong header lane");
  equal(view.getUint32(address, true), 1,
    "resident tag setter changed the object kind");
  equal(view.getUint32(address + 4, true), 2,
    "resident tag setter changed the live flags");
  equal(view.getUint32(0, true), 0xdecafbad,
    "resident tag setter failed to restore scratch");

  const host = new ConcreteHost();
  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  host.attachMemory(concrete.memory);
  prepareConstructor(concrete.memory, address);
  concrete.resident_set_tag(address);
  equal(host.getTag([address]), 14,
    "ConcreteHost getTag disagrees with resident tag setter");

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
    (candidate) => candidate.resident_set_tag(0),
    "zero tag setter",
  );
  await invalid(
    (memory) => prepareConstructor(memory, address),
    (candidate) => candidate.resident_set_tag(address + 4),
    "misaligned tag setter",
  );
  await invalid(
    (memory) => prepareConstructor(memory, address, { flags: 0 }),
    (candidate) => candidate.resident_set_tag(address),
    "dead tag setter",
  );
  await invalid(
    (memory) => prepareConstructor(memory, address, { kind: 2 }),
    (candidate) => candidate.resident_set_tag(address),
    "non-constructor tag setter",
  );

  return "PASS zero-import resident fixed constructor-tag mutation";
}

export async function checkFetchedResidentTagSetter(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentTagSetter(await response.arrayBuffer());
}
