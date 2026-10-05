// Current-tree installed-toolchain replay; never downloads or changes FIR's pin.
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { prepareSource } from "./source-prepare.mjs";
import { makeToolingTemporaryDirectory } from "./worktree-temp.mjs";

const repositoryRoot = fileURLToPath(new URL("../", import.meta.url));
const currentPin = readFileSync(new URL("../lean-toolchain", import.meta.url), "utf8").trim();

export function currentSmokeToolchain(args, run = execFileSync) {
  assert.equal(args.length, 0, "usage: node tooling/source-prepare-smoke.mjs (no arguments)");
  const options = { cwd: repositoryRoot, encoding: "utf8" };
  const lean = run("elan", ["which", "lean"], options).trim();
  const version = run(lean, ["--short-version"], options).trim();
  assert.equal(`leanprover/lean4:v${version}`, currentPin,
    "source-preparation smoke must use FIR's current Lean toolchain");
  const leanCommit = run(lean, ["--githash"], options).trim();
  assert.match(leanCommit, /^[0-9a-f]{40}$/, "selected Lean must report its exact commit");
  return { toolchainDirectory: dirname(dirname(lean)), leanCommit };
}

function main(args) {
  const { toolchainDirectory, leanCommit } = currentSmokeToolchain(args);
  const root = makeToolingTemporaryDirectory("source-prepare-smoke-");
  const source = join(root, "source");
  const dep = join(root, "dep");
  for (const path of [source, dep]) mkdirSync(path);
  writeFileSync(join(source, "lakefile.toml"), 'name = "prepareFixture"\n[[require]]\nname = "prepareDep"\ngit = "https://unavailable.invalid/prepareDep"\nrev = "never-fetch"\n[[lean_lib]]\nname = "Main"\n');
  writeFileSync(join(source, "lake-manifest.json"), JSON.stringify({ version: "1.2.0", name: "prepareFixture", lakeDir: ".lake", packagesDir: ".lake/packages", packages: [{ type: "git", name: "prepareDep", scope: "", url: "https://unavailable.invalid/prepareDep", rev: "a".repeat(40), inputRev: "never-fetch", inherited: false, manifestFile: "lake-manifest.json", configFile: "lakefile.toml", subDir: null }] }));
  writeFileSync(join(source, "Main.lean"), "import PrepareDep\ndef selectedEntry := PrepareDep.value + 1\n");
  writeFileSync(join(dep, "lakefile.toml"), 'name = "prepareDep"\n[[lean_lib]]\nname = "PrepareDep"\n');
  writeFileSync(join(dep, "PrepareDep.lean"), "def PrepareDep.value : Nat := 7\n");
  writeFileSync(join(dep, "lake-manifest.json"), JSON.stringify({ version: "1.2.0", name: "prepareDep", lakeDir: ".lake", packagesDir: ".lake/packages", packages: [] }));
  const packages = join(root, "paths.json");
  writeFileSync(packages, JSON.stringify({ prepareDep: dep }));
  const result = prepareSource({ source, packages, toolchainDirectory, leanCommit, modules: ["Main"], entries: ["selectedEntry"] });
  assert(result.setups[0].artifacts.length > 0);
  console.log(`PASS source-prepare installed Lake supplied-Git-dependency replay ${result.workspace}`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv.slice(2));
}
