#!/usr/bin/env node

import { execFileSync } from "node:child_process";
import {
  readFileSync,
  realpathSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

import {
  installVerifiedPackage,
  resolveFreshOutputPath,
  verifyBrowserPackage,
} from "../package-tools/verified-package.mjs";
import {
  selectionPackagePolicy,
  selectionPayloadFiles,
} from "./selection-package-policy.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const firRoot = realpathSync(join(directory, "../.."));

export const payloadFiles = selectionPayloadFiles;

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

export function verifyPackageDirectory(path) {
  return verifyBrowserPackage(path, selectionPackagePolicy);
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
  return installVerifiedPackage({
    sourceDirectory,
    outputDirectory,
    policy: selectionPackagePolicy,
    runSmoke,
  });
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
  const output = resolveFreshOutputPath(options.output);

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
