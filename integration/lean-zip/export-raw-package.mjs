#!/usr/bin/env node

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  realpathSync,
  renameSync,
  rmSync,
} from "node:fs";
import { basename, dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));

export const sourceContract = Object.freeze(JSON.parse(readFileSync(
  join(directory, "raw-source-contract.json"), "utf8")));

export const payloadFiles = Object.freeze([
  "BUILD.json",
  "lean-zip-byte-array-browser-adapter.mjs",
  "lean-zip-raw-browser-adapter.mjs",
  "standard-math-runtime-contract.mjs",
  "lean-zip-raw.wasm",
  "lean-zip-raw.wasm.functions.json",
  "lean-zip-raw.wasm.json",
  "smoke.mjs",
]);

export const packageFiles = Object.freeze([
  ...payloadFiles,
  "SHA256SUMS",
]);

const usage = `usage:
  export-raw-package.mjs \\
    --output OUTPUT \\
    --checkout producer=EXACT_CLEAN_FIR_CHECKOUT \\
    --checkout client=EXACT_CLEAN_LEAN_ZIP_CHECKOUT \\
    --checkout zip-common=EXACT_CLEAN_ZIP_COMMON_CHECKOUT
`;

function requireValue(argv, index, option) {
  const value = argv[index + 1];
  if (value === undefined || value.startsWith("--")) {
    throw new Error(`${option} requires one value`);
  }
  return value;
}

export function parseExportArguments(argv) {
  let output = null;
  const checkouts = new Map();
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === "--package" || argument.startsWith("--package=")) {
      throw new Error("the FIR-native lean-zip exporter accepts no dependency packages");
    }
    if (argument === "--output") {
      if (output !== null) throw new Error("--output was provided more than once");
      output = requireValue(argv, index, argument);
      index += 1;
      continue;
    }
    if (argument === "--checkout") {
      const checkout = requireValue(argv, index, argument);
      index += 1;
      const separator = checkout.indexOf("=");
      if (separator <= 0 || separator === checkout.length - 1) {
        throw new Error(`invalid --checkout value: ${checkout}`);
      }
      const role = checkout.slice(0, separator);
      const path = checkout.slice(separator + 1);
      if (!["producer", "client", "zip-common"].includes(role)) {
        throw new Error(`unknown checkout role: ${role}`);
      }
      if (checkouts.has(role)) {
        throw new Error(`checkout role was provided more than once: ${role}`);
      }
      checkouts.set(role, path);
      continue;
    }
    throw new Error(`unknown argument: ${argument}`);
  }

  if (output === null) throw new Error("--output is required");
  for (const role of ["producer", "client", "zip-common"]) {
    if (!checkouts.has(role)) throw new Error(`--checkout ${role}=... is required`);
  }
  return { output, checkouts: Object.fromEntries(checkouts) };
}

function captureGit(root, args) {
  return execFileSync("git", ["-C", root, ...args], {
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
  }).trim();
}

function cleanCheckout(path, label) {
  let root;
  try {
    root = realpathSync(path);
  } catch {
    throw new Error(`${label} checkout does not exist: ${path}`);
  }
  let topLevel;
  try {
    topLevel = realpathSync(captureGit(root, ["rev-parse", "--show-toplevel"]));
  } catch {
    throw new Error(`${label} checkout is not a Git worktree: ${root}`);
  }
  if (topLevel !== root) {
    throw new Error(`${label} checkout must name its exact Git worktree root: ${root}`);
  }
  if (captureGit(root, ["status", "--porcelain"]) !== "") {
    throw new Error(`${label} checkout must be clean: ${root}`);
  }
  return { root, commit: captureGit(root, ["rev-parse", "HEAD"]) };
}

export function validateSourceCheckouts({
  producer,
  client,
  zipCommon,
  expectedProducerRoot = firRoot,
  expectedClientRevision = sourceContract.clientRevision,
  expectedZipCommonRevision = sourceContract.zipCommonRevision,
}) {
  assert.equal(sourceContract.schemaVersion, "fir.lean-zip.raw-source/v1");
  const producerState = cleanCheckout(producer, "producer");
  const exactProducerRoot = realpathSync(expectedProducerRoot);
  if (producerState.root !== exactProducerRoot) {
    throw new Error(
      `producer checkout must contain this exporter: expected ${exactProducerRoot}, found ${producerState.root}`,
    );
  }
  const clientState = cleanCheckout(client, "client");
  if (clientState.commit !== expectedClientRevision) {
    throw new Error(
      `client revision mismatch: expected ${expectedClientRevision}, found ${clientState.commit}`,
    );
  }
  const zipCommonState = cleanCheckout(zipCommon, "zip-common");
  if (zipCommonState.commit !== expectedZipCommonRevision) {
    throw new Error(
      `zip-common revision mismatch: expected ${expectedZipCommonRevision}, found ${zipCommonState.commit}`,
    );
  }
  return {
    producer: producerState,
    client: clientState,
    zipCommon: zipCommonState,
  };
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function pathExists(path) {
  try {
    lstatSync(path);
    return true;
  } catch (error) {
    if (error?.code === "ENOENT") return false;
    throw error;
  }
}

function freshOutput(value) {
  assert.equal(typeof value, "string", "output path must be a string");
  assert.notEqual(value, "", "output path must not be empty");
  const absolute = resolve(value);
  const finalComponent = basename(absolute);
  assert.notEqual(finalComponent, ".", "output path must not end in .");
  assert.notEqual(finalComponent, "..", "output path must not end in ..");
  if (pathExists(absolute)) {
    throw new Error(`output directory must be fresh: ${absolute}`);
  }
  mkdirSync(dirname(absolute), { recursive: true });
  return join(realpathSync(dirname(absolute)), finalComponent);
}

export function verifyPackageDirectory(path, sources = null) {
  assert.deepEqual(readdirSync(path).sort(), [...packageFiles].sort(),
    "FIR-native lean-zip package file inventory changed");
  for (const name of packageFiles) {
    const state = lstatSync(join(path, name));
    assert.equal(state.isFile(), true, `${name} must be a regular file`);
    assert.equal(state.isSymbolicLink(), false, `${name} must not be a symbolic link`);
  }

  const manifest = readFileSync(join(path, "SHA256SUMS"), "utf8");
  assert.ok(manifest.endsWith("\n"), "SHA256SUMS must end with a newline");
  const entries = manifest.slice(0, -1).split("\n").map((line, index) => {
    const match = /^([0-9a-f]{64})  ([^/\\\0]+)$/.exec(line);
    assert.ok(match, `invalid SHA256SUMS line ${index + 1}`);
    return { digest: match[1], name: match[2] };
  });
  assert.deepEqual(entries.map(({ name }) => name), payloadFiles,
    "SHA256SUMS must cover the exact ordered payload inventory");
  for (const { digest, name } of entries) {
    assert.equal(sha256(readFileSync(join(path, name))), digest,
      `checksum mismatch for ${name}`);
  }

  const build = JSON.parse(readFileSync(join(path, "BUILD.json"), "utf8"));
  assert.equal(build.schemaVersion, "fir.lean-zip.raw.build/v3");
  assert.equal(build.entry.sourceName, "Zip.Wasm.compressRaw");
  assert.deepEqual(build.entry.levels, Array.from({ length: 10 }, (_, i) => i + 1));
  assert.equal(build.wasm.functionImportCount, 0);
  assert.equal(build.wasm.memoryImportCount, 0);
  assert.equal(build.wasm.memoryOwner, "module");
  if (sources !== null) {
    for (const [buildRole, sourceRole] of [
      ["fir", "producer"],
      ["leanZip", "client"],
      ["zipCommon", "zipCommon"],
    ]) {
      assert.equal(build.sources[buildRole].commit, sources[sourceRole].commit,
        `${buildRole} BUILD revision does not match selected checkout`);
      assert.equal(build.sources[buildRole].dirty, false,
        `${buildRole} BUILD source must be clean`);
    }
  }
  return build;
}

function defaultProducer({ destination, sources }) {
  execFileSync(process.execPath, [join(directory, "package-raw.mjs")], {
    cwd: directory,
    env: {
      ...process.env,
      LEAN_ZIP_ROOT: sources.client.root,
      ZIP_COMMON_ROOT: sources.zipCommon.root,
      FIR_RAW_PACKAGE_PREVIEW_DIR: destination,
    },
    stdio: "inherit",
  });
}

function defaultSmoke(path) {
  execFileSync(process.execPath, ["smoke.mjs"], {
    cwd: path,
    stdio: "inherit",
  });
}

export function publishCatalogPackage({
  outputDirectory,
  sources,
  runProducer = defaultProducer,
  runSmoke = defaultSmoke,
}) {
  const output = freshOutput(outputDirectory);
  const workspace = mkdtempSync(join(dirname(output),
    `.${basename(output)}.catalog.`));
  const stagedPackage = join(workspace, "package");
  let published = false;
  try {
    runProducer({ destination: stagedPackage, sources, workspace });
    verifyPackageDirectory(stagedPackage, sources);
    runSmoke(stagedPackage);
    renameSync(stagedPackage, output);
    published = true;
    verifyPackageDirectory(output, sources);
    runSmoke(output);
    return output;
  } catch (error) {
    if (published) rmSync(output, { recursive: true, force: true });
    throw error;
  } finally {
    rmSync(workspace, { recursive: true, force: true });
  }
}

function runMain() {
  if (process.argv.length === 3 && process.argv[2] === "--help") {
    process.stdout.write(usage);
    return;
  }
  const options = parseExportArguments(process.argv.slice(2));
  const sources = validateSourceCheckouts({
    producer: options.checkouts.producer,
    client: options.checkouts.client,
    zipCommon: options.checkouts["zip-common"],
  });
  const published = publishCatalogPackage({
    outputDirectory: options.output,
    sources,
  });
  process.stdout.write(`FIR-native lean-zip package exported to ${published}\n`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  try {
    runMain();
  } catch (error) {
    process.stderr.write(`FIR-native lean-zip export failed: ${error.message}\n`);
    process.stderr.write(usage);
    process.exitCode = 1;
  }
}
