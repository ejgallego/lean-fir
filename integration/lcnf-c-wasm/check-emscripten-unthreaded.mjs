import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

import { loadEmscriptenModule } from "./emscripten-loader.mjs";
import { asUInt64, expectedMix } from "./reference.mjs";

const manifestPath = process.argv[2];
if (manifestPath === undefined) {
  throw new Error(
    "usage: node check-emscripten-unthreaded.mjs <Smoke.manifest.json>",
  );
}

const loaded = await loadEmscriptenModule(
  pathToFileURL(resolve(manifestPath)),
);
const { build, runtime } = loaded.manifest;
if (build?.runtimeProfile !== "unthreaded") {
  throw new Error(`unexpected runtime profile: ${build?.runtimeProfile}`);
}
if (runtime?.threads !== false || runtime.crossOriginIsolated !== false) {
  throw new Error(`untruthful unthreaded metadata: ${JSON.stringify(runtime)}`);
}
if (build.compileFlags.includes("-pthread")) {
  throw new Error("unthreaded compile flags contain -pthread");
}
if (build.linkFlags.includes("-pthread")) {
  throw new Error("unthreaded link flags contain -pthread");
}
if (loaded.module.HEAPU8.buffer instanceof SharedArrayBuffer) {
  throw new Error("unthreaded module unexpectedly uses shared memory");
}

const affine = asUInt64(loaded.exports.fir_lcnf_c_affine(7n));
const rounds = 10_000n;
const seed = 0x123456789abcdef0n;
const mixed = asUInt64(loaded.exports.fir_lcnf_c_mix(rounds, seed));
const expected = expectedMix(rounds, seed);
if (affine !== 22n) {
  throw new Error(`affine mismatch: expected 22, got ${affine}`);
}
if (mixed !== expected) {
  throw new Error(`mix mismatch: expected ${expected}, got ${mixed}`);
}

console.log(
  JSON.stringify(
    {
      profile: "emscripten-unthreaded",
      manifest: manifestPath,
      threads: runtime.threads,
      crossOriginIsolated: runtime.crossOriginIsolated,
      sharedMemory: false,
      wasmByteLength: loaded.wasmByteLength,
      affine: affine.toString(),
      mix: mixed.toString(),
    },
    null,
    2,
  ),
);

