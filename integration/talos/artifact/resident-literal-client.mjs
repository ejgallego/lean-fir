import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function u32(memory, address) {
  return new DataView(memory.buffer).getUint32(address, true);
}

function header(memory, address) {
  return Array.from({ length: 8 }, (_unused, index) =>
    u32(memory, address + 4 * index));
}

/**
 * Exercise immediate Naturals and concrete UTF-8 String allocation with no
 * host imports. The raw checks freeze the current W6 header bytes; the second
 * instance verifies that ConcreteHost decodes the resident String directly.
 */
export async function checkResidentLiterals(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident literal module retained an import");

  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident literal memory export is missing");
  for (const name of [
    "resident_literal_nat_zero",
    "resident_literal_nat_one",
    "resident_literal_empty_string",
    "resident_literal_unicode_string",
    "fir_heap_frontier",
  ]) {
    equal(typeof exports[name], "function",
      `resident literal export ${name} is missing`);
  }

  const view = new DataView(exports.memory.buffer);
  view.setUint32(0, 0xdecafbad, true);
  equal(exports.resident_literal_nat_zero(), 1,
    "zero natural immediate encoding drifted");
  equal(exports.resident_literal_nat_one(), 3,
    "one natural immediate encoding drifted");
  equal(exports.fir_heap_frontier(), 1024,
    "immediate naturals unexpectedly allocated");

  const empty = exports.resident_literal_empty_string() >>> 0;
  equal(empty, 1024, "empty string returned the wrong address");
  equal(exports.fir_heap_frontier() >>> 0, 1056,
    "empty string advanced the wrong allocation extent");
  expect(header(exports.memory, empty).every((value, index) =>
    value === [4, 2, 1, 32, 1, 0, 0, 0][index]),
  `empty string header drifted: ${header(exports.memory, empty)}`);

  const unicode = exports.resident_literal_unicode_string() >>> 0;
  equal(unicode, 1056, "Unicode string returned the wrong address");
  equal(exports.fir_heap_frontier() >>> 0, 1096,
    "Unicode string advanced the wrong allocation extent");
  expect(header(exports.memory, unicode).every((value, index) =>
    value === [4, 2, 1, 40, 1, 3, 0, 0][index]),
  `Unicode string header drifted: ${header(exports.memory, unicode)}`);
  const payload = new Uint8Array(exports.memory.buffer, unicode + 32, 3);
  expect(payload[0] === 0xce && payload[1] === 0xbb && payload[2] === 0x0a,
    `Unicode string UTF-8 bytes drifted: ${Array.from(payload)}`);
  for (let address = unicode + 35; address < unicode + 40; address += 1) {
    equal(new Uint8Array(exports.memory.buffer)[address], 0,
      `Unicode string padding is nonzero at ${address}`);
  }
  equal(u32(exports.memory, 0), 0xdecafbad,
    "resident string allocation failed to restore the scratch word");

  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  const host = new ConcreteHost();
  host.attachMemory(concrete.memory);
  host.attachResidentFrontier(
    concrete.fir_heap_frontier,
    concrete.fir_heap_set_frontier,
  );
  const concreteString = concrete.resident_literal_unicode_string() >>> 0;
  host.synchronizeResidentFrontierBeforeImport();
  equal(host.readString(concreteString), "λ\n",
    "ConcreteHost did not decode the resident UTF-8 string");
  equal(host.heapCursor, concrete.fir_heap_frontier() >>> 0,
    "ConcreteHost did not consume the resident literal frontier");

  return "PASS zero-import resident immediate Natural and UTF-8 String literals";
}

export async function checkFetchedResidentLiterals(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentLiterals(await response.arrayBuffer());
}
