#!/usr/bin/env node

import assert from "node:assert/strict";
import { resolve } from "node:path";

import { runNodeProfile } from "./node-profile-lib.mjs";

function usage() {
  return "usage: node-profile.mjs --wasm FILE --sidecar FILE --workload FILE " +
    "--out-dir DIR [--workload-receipt FILE] [--metadata FILE] " +
    "[--sampling-interval-micros N]";
}

function arguments_(items) {
  const result = new Map();
  const allowed = new Set(["--wasm", "--sidecar", "--workload",
    "--workload-receipt", "--out-dir", "--metadata",
    "--sampling-interval-micros"]);
  for (let index = 0; index < items.length; index += 2) {
    const name = items[index];
    assert(name?.startsWith("--"), usage());
    assert(allowed.has(name), `unknown argument ${name}\n${usage()}`);
    assert(index + 1 < items.length, `missing value for ${name}\n${usage()}`);
    assert(!result.has(name), `duplicate argument ${name}`);
    result.set(name, items[index + 1]);
  }
  return result;
}

function required(args, name) {
  const value = args.get(name);
  assert.equal(typeof value, "string", `missing ${name}\n${usage()}`);
  return resolve(value);
}

const args = arguments_(process.argv.slice(2));
const metadataPath = args.get("--metadata");
const interval = args.get("--sampling-interval-micros");
const result = await runNodeProfile({
  wasmPath: required(args, "--wasm"),
  sidecarPath: required(args, "--sidecar"),
  workloadPath: required(args, "--workload"),
  workloadReceiptPath: args.get("--workload-receipt") === undefined ?
    undefined : resolve(args.get("--workload-receipt")),
  outputDirectory: required(args, "--out-dir"),
  metadataPath: metadataPath === undefined ? undefined : resolve(metadataPath),
  samplingIntervalMicros: interval === undefined ? 1000 : Number(interval),
});
process.stdout.write(`${result.evidencePath}\n`);
