import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  copyFileSync,
  existsSync,
  lstatSync,
  readFileSync,
  writeFileSync,
} from "node:fs";
import { basename, dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import {
  checksumManifest,
  publishImmutablePackage,
  sha256,
} from "../package-tools/immutable-package.mjs";
import { verifyBrowserPackage } from "../package-tools/verified-package.mjs";
import { checkComparatorBuild } from "./check-current-prettyM-comparator.mjs";
import {
  PRETTY_M_PACKAGE_FILES,
  prettyMPackagePolicy,
} from "./prettyM-package-policy.mjs";

const BRIDGE_EXPORTS = [
  "fir_lcnf_c_pretty_input_alloc",
  "fir_lcnf_c_pretty_render",
  "fir_lcnf_c_pretty_result_ptr",
  "fir_lcnf_c_pretty_result_len",
  "fir_lcnf_c_pretty_release",
];

function readJson(path) {
  return JSON.parse(readFileSync(path, "utf8"));
}

function artifactRecord(directory, record) {
  const bytes = readFileSync(join(directory, record.file));
  assert.equal(bytes.byteLength, record.byteLength,
    `${record.file} length differs from its generated manifest`);
  assert.equal(sha256(bytes), record.sha256,
    `${record.file} digest differs from its generated manifest`);
  return bytes;
}

function currentFirIdentity(repoRoot) {
  const sourceCommit = execFileSync("git",
    ["-C", repoRoot, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
  const dirty = execFileSync("git",
    ["-C", repoRoot, "status", "--porcelain"], { encoding: "utf8" }).trim();
  assert.equal(dirty, "", "immutable C prettyM publication requires a clean FIR tree");
  assert.equal(readFileSync(join(repoRoot, "lean-toolchain"), "utf8").trim(),
    "leanprover/lean4:v4.34.1", "C prettyM package needs reviewed Lean 4.34.1");
  return sourceCommit;
}

function writeBuild({ builtDirectory, repoRoot, comparatorBuildPath }) {
  const sourceCommit = currentFirIdentity(repoRoot);
  const comparator = readJson(comparatorBuildPath);
  checkComparatorBuild(comparator, { sourceCommit, sourceDirty: false });
  const manifest = readJson(join(builtDirectory, "prettyM.manifest.json"));
  assert.equal(manifest.artifactName, "prettyM");
  assert.equal(manifest.pipeline, "lean-final-impure-lcnf-to-c-to-wasm");
  assert.equal(manifest.sources.entry, "PrettyM.lean");
  assert.equal(manifest.toolchain.lean.version, "4.34.1");
  assert.equal(manifest.build.runtimeProfile, "threaded");
  assert.equal(manifest.runtime.threads, true);
  assert.deepEqual(manifest.abi.exports, BRIDGE_EXPORTS);
  const wasm = artifactRecord(builtDirectory, manifest.artifacts.wasm);
  artifactRecord(builtDirectory, manifest.artifacts.module);
  const module = new WebAssembly.Module(wasm);
  const imports = WebAssembly.Module.imports(module);
  const exports = WebAssembly.Module.exports(module);
  const functionImportCount = imports.filter(({ kind }) => kind === "function").length;
  const memoryImportCount = imports.filter(({ kind }) => kind === "memory").length;
  assert.equal(memoryImportCount, 1,
    "threaded Emscripten package must import loader-owned memory");
  assert.equal(exports.some(({ kind }) => kind === "memory"), false,
    "threaded Emscripten package must not export a second memory");
  const build = {
    schemaVersion: 1,
    format: "fir.prettyM.emscripten.package/v1",
    sources: {
      fir: { commit: sourceCommit, dirty: false },
      entry: manifest.sources.entry,
      additional: manifest.sources.additional,
      c: manifest.sources.c,
    },
    toolchain: manifest.toolchain,
    entry: {
      name: "Fir.LCNFC.PrettyM.renderWire",
      params: ["ByteArray"],
      result: "ByteArray",
    },
    abi: {
      browserApi: "fir.prettyM.browser/v1",
      inputLayout: "lean-4.33-Std.Format.compact/v1",
      wire: "fir.prettyM.emscripten-wire/v1",
      output: "PrettyTrace",
      bridgeExports: BRIDGE_EXPORTS,
    },
    ownership: {
      memoryOwner: "emscripten-loader",
      input: "copied-wire-buffer",
      output: "copied-javascript-PrettyTrace",
      reclamation: "bridge-release-on-adapter-dispose",
    },
    runtime: {
      ...manifest.runtime,
      archives: manifest.build.runtimeArchives,
    },
    wasm: {
      ...manifest.artifacts.wasm,
      memoryOwner: "emscripten-loader",
      functionImportCount,
      memoryImportCount,
      functionExportCount: exports.filter(({ kind }) => kind === "function").length,
      memoryExports: exports.filter(({ kind }) => kind === "memory").map(({ name }) => name),
      imports,
      exports,
    },
    loader: manifest.artifacts.module,
    differentialComparator: {
      sourceCommit: comparator.sourceCommit,
      sourceDirty: comparator.sourceDirty,
      wasmSha256: comparator.artifact.sha256,
    },
    test: "node smoke.mjs",
  };
  writeFileSync(join(builtDirectory, "BUILD.json"),
    `${JSON.stringify(build, null, 2)}\n`);
}

function verifyPrettyMPackage(directory) {
  const result = verifyBrowserPackage(directory, prettyMPackagePolicy);
  assert.deepEqual(result.metadata.imports, result.imports,
    "BUILD.json Wasm import inventory changed");
  assert.deepEqual(result.build.abi.bridgeExports, BRIDGE_EXPORTS);
  const manifest = readJson(join(directory, "prettyM.manifest.json"));
  assert.deepEqual(result.build.toolchain, manifest.toolchain);
  assert.deepEqual(result.build.loader, manifest.artifacts.module);
  assert.equal(result.build.wasm.sha256, manifest.artifacts.wasm.sha256);
  execFileSync(process.execPath, ["smoke.mjs"], {
    cwd: directory,
    stdio: "pipe",
  });
}

export function publishPreparedPrettyM({ builtDirectory, currentLink }) {
  const current = resolve(currentLink);
  const currentName = basename(current);
  assert.ok(currentName.endsWith("-current"),
    "package current link must end with -current");
  if (existsSync(current) && !lstatSync(current).isSymbolicLink()) {
    throw new Error(`refusing to replace a legacy package directory: ${current}`);
  }
  const packagesDirectory = join(dirname(current),
    currentName.slice(0, -"-current".length) + "-releases");
  const packageId = sha256(checksumManifest(builtDirectory, PRETTY_M_PACKAGE_FILES));
  const result = publishImmutablePackage({
    packagesDirectory,
    packageId,
    outputNames: PRETTY_M_PACKAGE_FILES,
    populate: (stage) => {
      for (const name of PRETTY_M_PACKAGE_FILES) {
        copyFileSync(join(builtDirectory, name), join(stage, name));
      }
    },
    currentLink: current,
    validate: verifyPrettyMPackage,
  });
  verifyPrettyMPackage(result.directory);
  assert.equal(sha256(readFileSync(join(result.directory, "SHA256SUMS"))),
    packageId, "release identity differs from its checksums");
  return result.directory;
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const [builtDirectory, currentLink, repoRoot, comparatorBuildPath] =
    process.argv.slice(2);
  assert.ok(builtDirectory && currentLink && repoRoot && comparatorBuildPath &&
    process.argv.length === 6,
  "usage: node publish-prettyM-emscripten.mjs <build-dir> <current-link> <FIR-root> <comparator-BUILD.json>");
  writeBuild({ builtDirectory, repoRoot, comparatorBuildPath });
  const directory = publishPreparedPrettyM({ builtDirectory, currentLink });
  console.log(`published immutable C/Emscripten prettyM package: ${directory}`);
}
