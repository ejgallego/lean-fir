import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

import { createArrayProbe } from "./adapter.mjs";

const wasmPath = process.argv[2] ?? "_build/package/array-probe.wasm";
const wasm = readFileSync(wasmPath);
const module = await WebAssembly.compile(wasm);
const sha256 = (value) => createHash("sha256").update(value).digest("hex");
const identity = {
  evidenceClass: "scaling-diagnostic",
  wasmSha256: sha256(wasm),
  driverSha256: sha256(readFileSync(fileURLToPath(import.meta.url))),
  node: process.version,
  v8: process.versions.v8,
};

async function collect(probe, configuration, action) {
  const firstCall = action();
  const warmup = [action(), action()];
  for (let sample = 0; sample < 7; sample += 1) {
    const result = action();
    console.log(JSON.stringify({
      schemaVersion: "fir.array-probe-sample/v1",
      ...identity,
      ...configuration,
      sample,
      firstCall: firstCall.timings,
      warmup: warmup.map(({ timings }) => timings),
      timings: result.timings,
      result: result.value,
      memory: result.memory,
    }));
  }
}

const readSize = 65536;
const values = Array.from({ length: readSize }, (_, index) =>
  (17 * index + 3) & 0x7fff);
for (const index of [0, readSize / 4, readSize / 2, readSize - 1]) {
  const readProbe = await createArrayProbe({ module, values });
  await collect(readProbe, {
    mechanism: "read-index",
    size: readSize,
    index,
    rounds: 100000,
  }, () => readProbe.readRepeated(index, 100000));
  readProbe.dispose();
}

for (const size of [64, 256, 1024]) {
  const uniqueProbe = await createArrayProbe({ module, values: [1] });
  await collect(uniqueProbe, {
    mechanism: "unique-update",
    size,
    index: size - 1,
    rounds: 4096,
  }, () => uniqueProbe.updateUnique(size, size - 1, 4096));
  uniqueProbe.dispose();
  const sharedProbe = await createArrayProbe({ module, values: [1] });
  await collect(sharedProbe, {
    mechanism: "shared-copy-update",
    size,
    index: size - 1,
    rounds: 16,
  }, () => sharedProbe.updateShared(size, size - 1, 16));
  sharedProbe.dispose();
}
