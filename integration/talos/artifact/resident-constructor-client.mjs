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

/**
 * Exercise the generation-only resident constructor family without any host
 * imports. The fixture covers an immediate constructor, a heap constructor,
 * exact header/object-slot layout, zeroed packed storage, frontier movement,
 * and preservation of the temporary retag word below the heap base.
 */
export async function checkResidentConstructors(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident constructor module retained an import");

  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident constructor memory export is missing");
  equal(typeof exports.resident_ctor_empty, "function",
    "resident empty-constructor export is missing");
  equal(typeof exports.resident_ctor_pair, "function",
    "resident heap-constructor export is missing");
  equal(typeof exports.fir_heap_frontier, "function",
    "resident constructor frontier export is missing");

  const view = new DataView(exports.memory.buffer);
  view.setUint32(0, 0xdecafbad, true);

  equal(exports.resident_ctor_empty(), 1,
    "empty constructor immediate encoding drifted");
  equal(exports.fir_heap_frontier(), 1024,
    "empty constructor unexpectedly allocated");
  equal(u32(exports.memory, 0), 0xdecafbad,
    "empty constructor changed the scratch word");

  const first = exports.resident_ctor_pair(23, 27);
  equal(first, 1024, "first heap constructor returned the wrong address");
  equal(exports.fir_heap_frontier(), 1088,
    "first heap constructor advanced the wrong extent");
  equal(u32(exports.memory, 0), 0xdecafbad,
    "heap constructor failed to restore the scratch word");

  const header = [
    u32(exports.memory, first + 0),
    u32(exports.memory, first + 4),
    u32(exports.memory, first + 8),
    u32(exports.memory, first + 12),
    u32(exports.memory, first + 16),
    u32(exports.memory, first + 20),
    u32(exports.memory, first + 24),
    u32(exports.memory, first + 28),
  ];
  const expectedHeader = [1, 2, 1, 64, 7, 2, 1, 3];
  expect(header.every((value, index) => value === expectedHeader[index]),
    `resident constructor header drifted: ${header}`);

  equal(u32(exports.memory, first + 32), 23,
    "first object field drifted");
  equal(u32(exports.memory, first + 36), 0,
    "first object-field high padding is nonzero");
  equal(u32(exports.memory, first + 40), 27,
    "second object field drifted");
  equal(u32(exports.memory, first + 44), 0,
    "second object-field high padding is nonzero");
  for (let address = first + 48; address < first + 64; address += 4) {
    equal(u32(exports.memory, address), 0,
      `constructor packed storage is nonzero at ${address}`);
  }

  const second = exports.resident_ctor_pair(31, 35);
  equal(second, 1088, "second heap constructor returned the wrong address");
  equal(exports.fir_heap_frontier(), 1152,
    "second heap constructor advanced the wrong extent");
  equal(u32(exports.memory, second + 32), 31,
    "second allocation first field drifted");
  equal(u32(exports.memory, second + 40), 35,
    "second allocation second field drifted");
  equal(u32(exports.memory, 0), 0xdecafbad,
    "second allocation failed to restore the scratch word");

  const { exports: growing } = await WebAssembly.instantiate(module, {});
  const host = new ConcreteHost();
  host.attachMemory(growing.memory);
  host.attachResidentFrontier(
    growing.fir_heap_frontier,
    growing.fir_heap_set_frontier,
  );
  const firstBuffer = host.buffer;
  while ((growing.fir_heap_frontier() >>> 0) <= 65536) {
    growing.resident_ctor_pair(1, 3);
  }
  equal(growing.memory.buffer.byteLength, 2 * 65536,
    "resident constructor did not grow memory by one page");
  host.synchronizeResidentFrontierBeforeImport();
  expect(host.buffer !== firstBuffer,
    "concrete host retained the detached pre-growth buffer");
  expect(host.buffer === growing.memory.buffer,
    "concrete host did not refresh the resident memory buffer");
  equal(host.heapCursor, growing.fir_heap_frontier() >>> 0,
    "concrete host did not import the post-growth frontier");

  return "PASS zero-import resident immediate/heap constructor allocation";
}

export async function checkFetchedResidentConstructors(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentConstructors(await response.arrayBuffer());
}
