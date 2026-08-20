import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  copyFileSync,
  mkdirSync,
  readFileSync,
  writeFileSync,
} from "node:fs";
import { basename, join, resolve } from "node:path";

const binaryen = process.env.FIR_BINARYEN_DIR;
assert(binaryen, "set FIR_BINARYEN_DIR to Binaryen's bin directory");
const root = resolve(import.meta.dirname, "../..");
const functionTool = join(root, "tooling/wasm/function-index.mjs");
const output = resolve(import.meta.dirname, "_build/package");
mkdirSync(output, { recursive: true });

const raw = resolve(import.meta.dirname, "_build/array-probe.raw.wasm");
const inventory = `${raw}.inventory.json`;
const descriptor = `${raw}.json`;
const named = join(output, "array-probe.named.wasm");
const capture = join(output, "array-probe.capture.json");
const optimizerArgs = join(output, "wasm-opt-args.json");
const release = join(output, "array-probe.wasm");
const control = join(output, "array-probe.control.wasm");
const sidecar = join(output, "array-probe.wasm.functions.json");
const optimization = ["--all-features", "-O3", "--closed-world",
  "--remove-unused-module-elements", "--vacuum", "--strip-debug",
  "--strip-dwarf"];

function run(command, args) {
  return execFileSync(command, args, { stdio: "inherit" });
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

run(process.execPath, [functionTool, "prepare", "--wasm", raw,
  "--inventory", inventory, "--named-wasm", named, "--capture", capture]);
writeFileSync(optimizerArgs, `${JSON.stringify(optimization, null, 2)}\n`);
run(process.execPath, [functionTool, "optimize", "--binaryen-dir", binaryen,
  "--input", named, "--wasm", release, "--capture", capture,
  "--wasm-opt-args", optimizerArgs, "--output", sidecar]);
run(join(binaryen, "wasm-opt"), [...optimization, raw, "-o", control]);
assert.deepEqual(readFileSync(release), readFileSync(control),
  "function identity capture changed optimized release bytes");
copyFileSync(descriptor, join(output, "array-probe.wasm.json"));

const wasm = readFileSync(release);
const functions = readFileSync(sidecar);
const module = new WebAssembly.Module(wasm);
const sourcePaths = ["FirArrayProbe.lean", "FirArrayProbe/Compile.lean",
  "Emit.lean", "adapter.mjs", "check.mjs", "benchmark.mjs", "build.mjs",
  "lakefile.toml", "lake-manifest.json", "lean-toolchain"];
const gitHead = execFileSync("git", ["rev-parse", "HEAD"], {
  cwd: root, encoding: "utf8",
}).trim();
const dirty = execFileSync("git", ["status", "--porcelain", "--",
  "tooling/array-probe"], { cwd: root, encoding: "utf8" }).trim() !== "";
const build = {
  schemaVersion: "fir.array-probe-build/v1",
  evidenceClass: "scaling-diagnostic",
  fir: { commit: gitHead, dirty },
  lean: execFileSync("lean", ["--version"], {
    cwd: import.meta.dirname, encoding: "utf8",
  }).trim(),
  inputLayout: "lean-4.33-Array-UInt32/v1",
  ownership: {
    memoryOwner: "module",
    input: "one adapter-owned persistent Array per instance",
    scratch: "instance checkpoint rewound after every call, including traps",
  },
  wasm: { file: basename(release), byteLength: wasm.length, sha256: sha256(wasm) },
  sidecar: {
    file: basename(sidecar),
    byteLength: functions.length,
    sha256: sha256(functions),
  },
  imports: WebAssembly.Module.imports(module),
  exports: WebAssembly.Module.exports(module),
  optimizerArgs: optimization,
  sources: sourcePaths.map((path) => ({
    path,
    sha256: sha256(readFileSync(resolve(import.meta.dirname, path))),
  })),
};
writeFileSync(join(output, "BUILD.json"),
  `${JSON.stringify(build, null, 2)}\n`);
console.log(`wrote ${release} (${wasm.length} bytes, ${build.wasm.sha256})`);
