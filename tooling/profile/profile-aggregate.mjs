#!/usr/bin/env node

import assert from "node:assert/strict";
import { resolve } from "node:path";

import {
  aggregateProfileEvidence,
  writeAggregateReport,
} from "./profile-aggregate-lib.mjs";

function usage() {
  return "usage: profile-aggregate.mjs --wasm FILE --sidecar FILE " +
    "[--evidence FILE ...] [--profile FILE ...] --out FILE";
}

function arguments_(items) {
  const result = { evidence: [], profile: [] };
  for (let index = 0; index < items.length; index += 2) {
    const name = items[index];
    const value = items[index + 1];
    assert(name?.startsWith("--") && value !== undefined,
      `invalid arguments\n${usage()}`);
    if (name === "--evidence" || name === "--profile") {
      result[name.slice(2)].push(resolve(value));
    } else {
      assert(["--wasm", "--sidecar", "--out"].includes(name),
        `unknown argument ${name}\n${usage()}`);
      assert(result[name] === undefined, `duplicate argument ${name}`);
      result[name] = resolve(value);
    }
  }
  for (const name of ["--wasm", "--sidecar", "--out"]) {
    assert.equal(typeof result[name], "string", `missing ${name}\n${usage()}`);
  }
  assert(result.evidence.length + result.profile.length !== 0,
    `missing --evidence or --profile\n${usage()}`);
  return result;
}

const args = arguments_(process.argv.slice(2));
const report = aggregateProfileEvidence({
  wasmPath: args["--wasm"],
  sidecarPath: args["--sidecar"],
  evidencePaths: args.evidence,
  profilePaths: args.profile,
});
const output = writeAggregateReport(args["--out"], report);
process.stdout.write(`${output.path}\n`);
