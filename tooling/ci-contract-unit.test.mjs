import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
  copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync,
} from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";

import {
  inspectToolingRuntime,
  parseNodeMajor,
  toolingCiContract,
} from "./ci-contract.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const workflow = name => readFileSync(join(root, ".github/workflows", name), "utf8");
function runBlock(name, title) {
  const step = workflow(name).split(`      - name: ${title}\n`)[1];
  assert(step, `missing workflow step: ${title}`);
  const block = step.split("        run: |\n")[1];
  assert(block, `missing script: ${title}`);
  const lines = [];
  for (const line of block.split("\n")) {
    if (!line.startsWith("          ")) break;
    lines.push(line.slice(10));
  }
  return lines.join("\n");
}
function withCiFixture(run) {
  const scratch = process.env.FIR_TOOLING_TMPDIR ?? join(root, ".deps/tooling-tmp");
  mkdirSync(scratch, { recursive: true });
  const directory = mkdtempSync(join(scratch, "ci-prerequisites-"));
  try { run(directory); }
  finally { rmSync(directory, { recursive: true, force: true }); }
}

test("declares the supported LTS matrix and provider-neutral command", () => {
  assert.deepEqual(toolingCiContract.supportedNodeMajors, [22, 24]);
  assert.equal(toolingCiContract.baselineNodeMajor, 24);
  assert.equal(toolingCiContract.externalCommand, "make tooling-check");
  assert.ok(Object.isFrozen(toolingCiContract));
  assert.ok(Object.isFrozen(toolingCiContract.supportedNodeMajors));
});

test("parses complete and major-only Node versions", () => {
  assert.equal(parseNodeMajor("v24.19.0"), 24);
  assert.equal(parseNodeMajor("22.23.1"), 22);
  assert.equal(parseNodeMajor("v24"), 24);
});

test("accepts every supported Node major with an explicit V8 identity", () => {
  for (const major of toolingCiContract.supportedNodeMajors) {
    const receipt = inspectToolingRuntime({
      nodeVersion: `v${major}.1.2`,
      v8Version: `v8-for-node-${major}`,
    });
    assert.equal(receipt.status, "supported");
    assert.equal(receipt.nodeMajor, major);
    assert.equal(receipt.externalCommand, "make tooling-check");
    assert.ok(Object.isFrozen(receipt));
  }
});

test("rejects EOL, current non-LTS, and malformed runtimes", () => {
  assert.throws(
    () => inspectToolingRuntime({ nodeVersion: "v20.19.0", v8Version: "11" }),
    /unsupported Node major 20/u,
  );
  assert.throws(
    () => inspectToolingRuntime({ nodeVersion: "v26.1.0", v8Version: "14" }),
    /unsupported Node major 26/u,
  );
  assert.throws(() => parseNodeMajor("development"), /invalid Node version/u);
  assert.throws(
    () => inspectToolingRuntime({ nodeVersion: "v24.1.0", v8Version: "" }),
    /did not report a V8 version/u,
  );
});

test("artifact receipt regeneration provisions recorder and replay isolator", () => {
  assert.match(workflow("wasm-artifact.yml"),
    /sudo apt-get install -y ripgrep strace bubblewrap/u);
});

test("failure diagnostics expose bounded backend stderr/stdout without broad uploads", () => {
  for (const [name, title, output] of [
    ["ci.yml", "Report bounded check failure logs", "check.log"],
    ["wasm-artifact.yml", "Report bounded artifact failure logs", "artifact.log"],
  ]) withCiFixture(directory => {
    const backend = join(directory, "_build/validation-v8/lean-wasm-semantic/build");
    mkdirSync(backend, { recursive: true });
    writeFileSync(join(backend, "stderr.log"), "specific backend failure\n");
    writeFileSync(join(backend, "stdout.jsonl"), "x".repeat(20_000) + "stdout tail\n");
    writeFileSync(join(directory, "private.log"), "UNRELATED_PRIVATE_SENTINEL\n");
    const otherBuild = join(dirname(backend), "build-2");
    mkdirSync(otherBuild, { recursive: true });
    symlinkSync(join(directory, "private.log"), join(otherBuild, "stderr.log"));
    const result = spawnSync("bash", ["-e", "-o", "pipefail", "-c", runBlock(name, title)],
      { cwd: directory, encoding: "utf8" });
    assert.equal(result.status, 0, result.stderr);
    const receipt = readFileSync(join(directory, ".deps/ci-failure", output), "utf8");
    assert.equal(receipt, result.stdout);
    assert.match(receipt, /specific backend failure/u);
    assert.match(receipt, /stdout tail/u);
    assert(receipt.length < 9000, "single long stdout line was not bounded");
    assert.doesNotMatch(receipt, /UNRELATED_PRIVATE_SENTINEL/u);
    const yaml = workflow(name);
    assert(yaml.includes(`path: .deps/ci-failure/${output}`));
    assert.match(yaml, /include-hidden-files: true/u);
    assert.match(yaml, /retention-days: 7/u);
    assert.match(yaml, /if: failure\(\)/u);
    assert.doesNotMatch(yaml, /continue-on-error/u);
  });
});

test("authenticated SDK selection exports a matched pair and fails if linker is absent", () =>
  withCiFixture(directory => {
    const lane = join(directory, "integration/lcnf-c-wasm");
    mkdirSync(lane, { recursive: true });
    copyFileSync(join(root, "integration/lcnf-c-wasm/toolchain-pins.sh"),
      join(lane, "toolchain-pins.sh"));
    const asset = spawnSync("bash", ["-c",
      'source "$1"; fir_lcnf_c_wasi_sdk_asset', "fixture", join(lane, "toolchain-pins.sh")],
    { encoding: "utf8" });
    assert.equal(asset.status, 0, asset.stderr);
    const sdk = join(directory, ".deps/lcnf-c-wasm",
      asset.stdout.trim().split(" ")[0].replace(/\.tar\.gz$/u, ""));
    mkdirSync(join(sdk, "bin"), { recursive: true });
    for (const tool of ["clang", "wasm-ld"]) writeFileSync(join(sdk, "bin", tool),
      `#!/usr/bin/env bash\nprintf 'fixture ${tool} identity\\n'\n`, { mode: 0o755 });
    const environmentFile = join(directory, "github-env");
    const args = ["-e", "-o", "pipefail", "-c", runBlock("lcnf-c-wasm.yml",
      "Select the authenticated WASI SDK compiler and linker pair")];
    const options = { cwd: directory, encoding: "utf8", env: {
      ...process.env, GITHUB_WORKSPACE: directory, GITHUB_ENV: environmentFile,
    } };
    const result = spawnSync("bash", args, options);
    assert.equal(result.status, 0, result.stderr);
    assert.equal(readFileSync(environmentFile, "utf8"),
      `FIR_WASM_CLANG=${sdk}/bin/clang\nFIR_WASM_LD=${sdk}/bin/wasm-ld\n`);
    rmSync(join(sdk, "bin/wasm-ld"));
    writeFileSync(environmentFile, "");
    assert.notEqual(spawnSync("bash", args, options).status, 0);
    assert.equal(readFileSync(environmentFile, "utf8"), "",
      "missing SDK linker must not select a system fallback");
  }));
