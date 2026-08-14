#!/usr/bin/env node

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  chmodSync,
  copyFileSync,
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

export const payloadFiles = Object.freeze([
  "BUILD.json",
  "illuminate-selection-player-browser-adapter.mjs",
  "illuminate-selection-player.wasm",
  "illuminate-selection-player.wasm.json",
  "smoke.mjs",
]);

export const packageFiles = Object.freeze([
  ...payloadFiles,
  "SHA256SUMS",
]);

const usage = `usage:
  export-selection-package.mjs \\
    --output OUTPUT \\
    --checkout producer=EXACT_CLEAN_FIR_CHECKOUT \\
    --checkout illuminate=EXACT_CLEAN_ILLUMINATE_CHECKOUT

Direct-use compatibility alias:
  ILLUMINATE_ROOT=EXACT_CLEAN_ILLUMINATE_CHECKOUT \\
    export-selection-package.mjs OUTPUT
`;

function requireValue(argv, index, option) {
  const value = argv[index + 1];
  if (value === undefined || value.startsWith("--")) {
    throw new Error(`${option} requires one value`);
  }
  return value;
}

export function parseExportArguments(argv, environment = process.env) {
  if (argv.length === 1 && !argv[0].startsWith("-")) {
    if (!environment.ILLUMINATE_ROOT) {
      throw new Error(
        "ILLUMINATE_ROOT is required by the positional-output compatibility alias",
      );
    }
    return {
      mode: "direct-alias",
      output: argv[0],
      checkouts: {
        producer: null,
        illuminate: environment.ILLUMINATE_ROOT,
      },
    };
  }

  let output = null;
  const checkouts = new Map();
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === "--package" || argument.startsWith("--package=")) {
      throw new Error("the selection exporter accepts no dependency packages");
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
      if (role !== "producer" && role !== "illuminate") {
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
  for (const role of ["producer", "illuminate"]) {
    if (!checkouts.has(role)) throw new Error(`--checkout ${role}=... is required`);
  }
  return {
    mode: "catalog",
    output,
    checkouts: Object.fromEntries(checkouts),
  };
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
  return {
    root,
    commit: captureGit(root, ["rev-parse", "HEAD"]),
  };
}

export function validateSourceCheckouts({
  producer,
  illuminate,
  expectedProducerRoot,
  expectedIlluminateRevision,
}) {
  const producerState = cleanCheckout(producer, "producer");
  const exactProducerRoot = realpathSync(expectedProducerRoot);
  if (producerState.root !== exactProducerRoot) {
    throw new Error(
      `producer checkout must contain this exporter: expected ${exactProducerRoot}, found ${producerState.root}`,
    );
  }
  const illuminateState = cleanCheckout(illuminate, "illuminate");
  if (illuminateState.commit !== expectedIlluminateRevision) {
    throw new Error(
      `illuminate revision mismatch: expected ${expectedIlluminateRevision}, found ${illuminateState.commit}`,
    );
  }
  return { producer: producerState, illuminate: illuminateState };
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

function outputPath(value) {
  assert.equal(typeof value, "string", "output path must be a string");
  assert.notEqual(value, "", "output path must not be empty");
  const finalComponent = basename(value);
  assert.notEqual(finalComponent, ".", "output path must not end in .");
  assert.notEqual(finalComponent, "..", "output path must not end in ..");
  assert.notEqual(finalComponent, "/", "output path must have a final component");
  const absolute = resolve(value);
  if (pathExists(absolute)) {
    throw new Error(`output directory must be fresh: ${absolute}`);
  }
  mkdirSync(dirname(absolute), { recursive: true });
  return join(realpathSync(dirname(absolute)), basename(absolute));
}

export function verifyPackageDirectory(path) {
  const expectedNames = [...packageFiles].sort();
  assert.deepEqual(readdirSync(path).sort(), expectedNames,
    "selection package must contain exactly the six public files");
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
}

function defaultSmoke(path) {
  execFileSync(process.execPath, ["smoke.mjs"], {
    cwd: path,
    stdio: "inherit",
  });
}

export function publishAcceptedPackage({
  sourceDirectory,
  outputDirectory,
  runSmoke = defaultSmoke,
}) {
  const source = realpathSync(sourceDirectory);
  verifyPackageDirectory(source);
  const output = outputPath(outputDirectory);
  const staging = mkdtempSync(join(dirname(output), `.${basename(output)}.stage.`));
  let published = false;
  try {
    for (const name of packageFiles) {
      copyFileSync(join(source, name), join(staging, name));
      chmodSync(join(staging, name), 0o644);
    }
    verifyPackageDirectory(staging);
    runSmoke(staging);
    renameSync(staging, output);
    published = true;
    verifyPackageDirectory(output);
    runSmoke(output);
    return output;
  } catch (error) {
    if (published) rmSync(output, { recursive: true, force: true });
    throw error;
  } finally {
    if (!published) rmSync(staging, { recursive: true, force: true });
  }
}

function runMain() {
  if (process.argv.length === 3 && process.argv[2] === "--help") {
    process.stdout.write(usage);
    return;
  }
  const options = parseExportArguments(process.argv.slice(2));
  const producer = options.checkouts.producer ?? firRoot;
  const expectedSource = JSON.parse(readFileSync(
    join(directory, "illuminate-source.json"), "utf8"));
  const sources = validateSourceCheckouts({
    producer,
    illuminate: options.checkouts.illuminate,
    expectedProducerRoot: firRoot,
    expectedIlluminateRevision: expectedSource.revision,
  });
  const output = outputPath(options.output);

  execFileSync(join(directory, "check.sh"), [], {
    cwd: directory,
    env: { ...process.env, ILLUMINATE_ROOT: sources.illuminate.root },
    stdio: "inherit",
  });
  const acceptedPackage = realpathSync(join(
    directory, "_build/illuminate-selection-player-current"));
  const published = publishAcceptedPackage({
    sourceDirectory: acceptedPackage,
    outputDirectory: output,
  });
  process.stdout.write(`Illuminate selection package exported to ${published}\n`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  try {
    runMain();
  } catch (error) {
    process.stderr.write(`selection package export failed: ${error.message}\n`);
    process.stderr.write(usage);
    process.exitCode = 1;
  }
}
