import assert from "node:assert/strict";
import { execFileSync, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  mkdirSync, readFileSync, realpathSync, renameSync, rmSync, statSync, writeFileSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const sourceRoot = realpathSync(process.env.ILLUMINATE_ROOT ?? join(directory, ".illuminate"));
const build = join(directory, "_build");
const binary = join(directory, ".lake/build/bin/illuminatePlayerArtifact");
const optimizer = join(directory, "../wasm-runtime/optimize-closed-module.mjs");
const lakeArgs = ["--keep-toolchain", "--reconfigure", `-KilluminateRoot=${sourceRoot}`];
const variants = [
  { mode: "full", capture: "CapturedFull", key: "full",
    stem: "illuminate-player", frontend: "Emit.lean" },
  { mode: "selection", capture: "CapturedSelection", key: "selection",
    stem: "illuminate-selection-player", frontend: "SelectionEmit.lean" },
];

function run(command, args, options = {}) {
  return execFileSync(command, args, { cwd: directory, stdio: "pipe",
    env: process.env, ...options });
}

function capturePaths(variant) {
  const stem = join(directory, ".lake/build/lib/lean/IlluminateFirNative", variant.capture);
  return { olean: `${stem}.olean`, trace: `${stem}.trace` };
}

function stamp(path) {
  return { mtime: statSync(path, { bigint: true }).mtimeNs,
    sha256: createHash("sha256").update(readFileSync(path)).digest("hex") };
}

function buildCapture(variant) {
  // These controls must actually elaborate changed captures, not restore CAS
  // artifacts. Normal production builds continue using the accepted Lake cache.
  run("lake", [...lakeArgs, "--no-cache", "build",
    `+IlluminateFirNative.${variant.capture}:olean`], { env: {
      ...process.env, LAKE_ARTIFACT_CACHE: "false", LAKE_RESTORE_ARTIFACTS: "false",
    } });
}

function outputs(variant) {
  const raw = ["base.wasm", "base.wasm.json", "base.wasm.lcnf",
    "resident.wasm", "resident.wasm.json", "resident.wasm.lcnf",
    "resident.wasm.inventory.json", "complete.wasm"];
  return new Map(raw.map(suffix => [suffix, readFileSync(join(build,
    `${variant.stem}-${suffix}`))]));
}

function generate(variant, interpreted = false) {
  const args = [variant.mode, `IlluminateFirNative.${variant.capture}`, variant.key];
  if (interpreted) run("lake", [...lakeArgs, "env", "lean", "--run",
    "NativeArtifactMain.lean", ...args]);
  else run(binary, args);
  run(process.execPath, [optimizer, join(build, `${variant.stem}-resident.wasm`),
    join(build, `${variant.stem}-complete.wasm`)]);
  return outputs(variant);
}

function equalOutputs(actual, expected, label) {
  for (const [name, bytes] of expected) {
    assert(actual.get(name).equals(bytes), `${label}: ${name}`);
  }
}

function definitions(bytes) {
  return new Map(bytes.toString().split(/(?=^def )/m).filter(Boolean)
    .map(definition => [definition.match(/^def (\S+)/)[1], definition]));
}

function reject(args, message, variant) {
  const before = outputs(variant);
  const result = spawnSync(binary, args, { cwd: directory, encoding: "utf8" });
  assert.equal(result.error, undefined);
  assert.equal(result.signal, null);
  assert.notEqual(result.status, 0, `unexpected success: ${args.join(" ")}`);
  assert.match(result.stderr, message);
  for (const [name, bytes] of before) {
    assert.deepEqual(outputs(variant).get(name), bytes,
      `failure wrote stale/partial output: ${name}`);
  }
}

mkdirSync(build, { recursive: true });
const comparisonDirectory = join(build, "native-comparison");
mkdirSync(comparisonDirectory, { recursive: true });
const comparisons = [];
for (const variant of variants) {
  const paths = capturePaths(variant);
  // Remove only disposable outputs of this selected capture, never source,
  // dependency trees, another package or its current pointer.
  rmSync(paths.olean, { force: true });
  rmSync(paths.trace, { force: true });
  buildCapture(variant);
  const cold = { olean: stamp(paths.olean), trace: stamp(paths.trace) };
  const firstCold = generate(variant);
  buildCapture(variant);
  assert.deepEqual({ olean: stamp(paths.olean), trace: stamp(paths.trace) }, cold,
    `${variant.mode} warm capture was rebuilt`);
  equalOutputs(generate(variant), firstCold, `${variant.mode} warm replay`);
  rmSync(paths.olean);
  rmSync(paths.trace);
  buildCapture(variant);
  assert.equal(stamp(paths.olean).sha256, cold.olean.sha256,
    `${variant.mode} independent cold capture changed its olean`);
  equalOutputs(generate(variant), firstCold, `${variant.mode} independent cold replay`);

  // A reversible source edit tests the real owned capture target's dependency
  // tracking. Run this check serially, without Beam/other builds in this recipe.
  const source = join(directory, "IlluminateFirNative", `${variant.capture}.lean`);
  const original = readFileSync(source);
  try {
    writeFileSync(source, Buffer.concat([original,
      Buffer.from("\n-- Native capture invalidation regression.\n")]));
    buildCapture(variant);
    assert.notEqual(stamp(paths.trace).sha256, cold.trace.sha256,
      `${variant.mode} source change did not invalidate capture`);
    assert.notEqual(stamp(paths.olean).mtime, cold.olean.mtime);
  } finally {
    writeFileSync(source, original);
    buildCapture(variant);
  }

  run("lake", [...lakeArgs, "env", "lean", variant.frontend]);
  run(process.execPath, [optimizer, join(build, `${variant.stem}-resident.wasm`),
    join(build, `${variant.stem}-complete.wasm`)]);
  const frontend = outputs(variant);
  const native = generate(variant);
  equalOutputs(native, firstCold, `${variant.mode} restored source replay`);
  const differences = [];
  for (const [name, bytes] of frontend) {
    writeFileSync(join(comparisonDirectory, `${variant.mode}-frontend-${name}`), bytes);
    writeFileSync(join(comparisonDirectory, `${variant.mode}-capture-${name}`), native.get(name));
    if (!native.get(name).equals(bytes)) differences.push({ mode: variant.mode, name,
      frontend: createHash("sha256").update(bytes).digest("hex"),
      native: createHash("sha256").update(native.get(name)).digest("hex") });
  }
  // Capture contexts can change join-point order. Descriptors and inventories
  // must nevertheless match exactly; no closure/runtime/export delta is allowed.
  for (const name of ["base.wasm.json", "resident.wasm.json", "resident.wasm.inventory.json"]) {
    assert(native.get(name).equals(frontend.get(name)),
      `${variant.mode} frontend/capture interface or inventory changed: ${name}`);
  }
  const oldDefinitions = definitions(frontend.get("base.wasm.lcnf"));
  const newDefinitions = definitions(native.get("base.wasm.lcnf"));
  assert.deepEqual([...newDefinitions.keys()], [...oldDefinitions.keys()]);
  const changedDefinitions = [...oldDefinitions.keys()].filter(name =>
    oldDefinitions.get(name) !== newDefinitions.get(name));
  assert.deepEqual(changedDefinitions.slice().sort(), ["advance", "tick", "tickTowardTarget"]
    .map(name => `_private.Illuminate.Animation.Player.0.Illuminate.AnimationPlayer.${name}`).sort(),
  `${variant.mode} capture-context delta escaped its audited definitions`);
  const diff = spawnSync("diff", ["-u",
    join(comparisonDirectory, `${variant.mode}-frontend-base.wasm.lcnf`),
    join(comparisonDirectory, `${variant.mode}-capture-base.wasm.lcnf`)], { encoding: "utf8" });
  assert.equal(diff.error, undefined);
  assert.equal(diff.status, 1);
  writeFileSync(join(comparisonDirectory, `${variant.mode}-context.diff`), diff.stdout);
  comparisons.push({ mode: variant.mode, changedDefinitions, differences });
  // Isolate backend execution from capture context using one identical olean.
  equalOutputs(generate(variant, true), native,
    `${variant.mode} interpreted/native checkpoint consumer`);

  reject([variant.mode, `IlluminateFirNative.${variant.capture}`, "missing"],
    /missing player checkpoint/, variant);
  reject([variant.mode, "IlluminateFirNative.Entries", variant.key],
    /missing player checkpoint/, variant);
  reject([variant.mode, "IlluminateFirNative.MissingCapture", variant.key],
    /MissingCapture/, variant);
  // A valid checkpoint for the other entry set must not be accepted.
  const other = variants.find(item => item.mode !== variant.mode);
  buildCapture(other);
  reject([variant.mode, `IlluminateFirNative.${other.capture}`, other.key],
    /does not contain the selected source entries/, variant);

  // Direct invocation must not repair a missing olean by spawning Lake/capture.
  const hidden = `${paths.olean}.native-check-hidden`;
  renameSync(paths.olean, hidden);
  try {
    reject([variant.mode, `IlluminateFirNative.${variant.capture}`, variant.key],
      new RegExp(variant.capture), variant);
    assert.throws(() => statSync(paths.olean), { code: "ENOENT" });
  } finally {
    renameSync(hidden, paths.olean);
  }
  console.log(`${variant.mode}: cold/warm/invalidation, eight byte-exact checkpoint-consumer outputs, ` +
    "missing module/checkpoint/key/olean and wrong-entry controls pass");
}

reject(["unknown", "IlluminateFirNative.CapturedFull", "full"], /usage:/, variants[0]);
reject([], /usage:/, variants[0]);
writeFileSync(join(comparisonDirectory, "context-delta.json"),
  `${JSON.stringify(comparisons, null, 2)}\n`);
console.log("native capture checks pass (no publication)");
