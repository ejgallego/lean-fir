import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { createArrayProbe } from "./adapter.mjs";

const path = process.argv[2] ?? "_build/array-probe.raw.wasm";
const toolchain = readFileSync(new URL("../../lean-toolchain", import.meta.url),
  "utf8").trim();
assert.ok(["leanprover/lean4:v4.33.0", "leanprover/lean4:v4.34.0-rc2"]
  .includes(toolchain), `unsupported Array-probe toolchain ${toolchain}`);
const values = Array.from({ length: 32 }, (_, index) => 3 * index + 1);
let tick = 0;
const probe = await createArrayProbe({
  bytes: readFileSync(path),
  values,
  now: () => ++tick,
});

for (const index of [0, 1, 8, 16, 31]) {
  const result = probe.readRepeated(index, 17);
  assert.equal(result.value, values[index] * 17);
  assert.equal(result.memory.allocatedBytes, 0,
    `read at ${index} allocated scratch memory`);
  assert.deepEqual(result.timings, {
    executeMs: 1,
    rewindMs: 1,
    totalMs: 2,
  });
}

const size = 16;
const allocationBytes = 32 + 8 * size;
const built = probe.buildOnly(size, 7);
assert.equal(built.memory.allocatedBytes, allocationBytes);
for (const rounds of [0, 1, 64]) {
  const unique = probe.updateUnique(size, 7, rounds);
  assert.equal(unique.memory.allocatedBytes, allocationBytes,
    `unique update allocated for ${rounds} rounds`);
}
for (const rounds of [0, 1, 4, 16]) {
  const shared = probe.updateShared(size, 7, rounds);
  const expectedCopies = toolchain === "leanprover/lean4:v4.33.0"
    ? rounds + 1 : rounds === 0 ? 1 : 2;
  assert.equal(shared.memory.allocatedBytes, allocationBytes * expectedCopies,
    `shared update copy growth for ${rounds} rounds on ${toolchain}`);
}

assert.throws(() => probe.updateUnique(0x7fffffff, 0, 1),
  WebAssembly.RuntimeError);
assert.equal(probe.readRepeated(3, 2).value, values[3] * 2,
  "probe did not recover after a trapped call");
probe.dispose();
assert.throws(() => probe.readRepeated(0, 1), /disposed/);

console.log("PASS ordinary compiled Array mechanism probe");
