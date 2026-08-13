import assert from "node:assert/strict";
import fs from "node:fs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-materialized-cache.mjs PATH.wasm");
}

const bytes = fs.readFileSync(path);
const module = await WebAssembly.compile(bytes);
assert.equal(WebAssembly.Module.imports(module).length, 0,
  "materialized cache retained imports");

for (let instanceIndex = 0; instanceIndex < 2; ++instanceIndex) {
  const { exports } = await WebAssembly.instantiate(module, {});
  const view = new DataView(exports.memory.buffer);

  assert.equal(exports.resident_lazy_object_initialized(), 0,
    "static image made the lazy cache observable before first access");
  assert.equal(exports.fir_heap_frontier() >>> 0, 1064,
    "allocator frontier overlaps the static image");
  assert.deepEqual(
    Array.from({ length: 8 }, (_, index) =>
      view.getUint32(1024 + 4 * index, true)),
    [1, 3, 0, 40, 0, 1, 0, 0],
    "materialized constructor header");
  assert.equal(view.getUint32(1056, true), 1,
    "materialized immediate field");
  assert.equal(view.getUint32(1060, true), 0,
    "materialized slot padding");

  const before = exports.fir_heap_frontier() >>> 0;
  assert.equal(exports.resident_lazy_object() >>> 0, 1024,
    "cold access returned the wrong image address");
  assert.equal(exports.resident_lazy_object_initialized(), 1,
    "cold access did not publish the lazy cache");
  assert.equal(exports.fir_heap_frontier() >>> 0, before,
    "cold materialized access allocated at run time");
  assert.equal(exports.resident_lazy_object() >>> 0, 1024,
    "warm access changed the image address");
  assert.equal(exports.fir_heap_frontier() >>> 0, before,
    "warm materialized access grew the heap");

  assert.equal(exports.fir_heap_alloc(40) >>> 0, before,
    "scratch allocation did not start after the static image");
  exports.fir_heap_rewind(before);
  assert.equal(exports.fir_heap_frontier() >>> 0, before,
    "scratch rewind changed the persistent image floor");
  assert.equal(exports.resident_lazy_object() >>> 0, 1024,
    "scratch rewind invalidated the materialized cache");
}

console.log("PASS lazy publication of a persistent closed-constructor image");
