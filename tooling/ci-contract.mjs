#!/usr/bin/env node

import { pathToFileURL } from "node:url";

export const toolingCiContract = Object.freeze({
  schemaVersion: "fir.tooling-ci/v1",
  supportedNodeMajors: Object.freeze([22, 24]),
  baselineNodeMajor: 24,
  externalCommand: "make tooling-check",
});

export function parseNodeMajor(version) {
  const match = /^v?([1-9][0-9]*)(?:[.]|$)/u.exec(version);
  if (match === null) {
    throw new Error(`invalid Node version: ${JSON.stringify(version)}`);
  }
  return Number.parseInt(match[1], 10);
}

export function inspectToolingRuntime({
  nodeVersion = process.version,
  v8Version = process.versions.v8,
} = {}) {
  const nodeMajor = parseNodeMajor(nodeVersion);
  if (!toolingCiContract.supportedNodeMajors.includes(nodeMajor)) {
    throw new Error(
      `unsupported Node major ${nodeMajor}; ` +
      `tooling CI requires one of ${toolingCiContract.supportedNodeMajors.join(", ")}`,
    );
  }
  if (typeof v8Version !== "string" || v8Version.length === 0) {
    throw new Error("Node runtime did not report a V8 version");
  }
  return Object.freeze({
    schemaVersion: toolingCiContract.schemaVersion,
    status: "supported",
    nodeVersion,
    nodeMajor,
    v8Version,
    baselineNodeMajor: toolingCiContract.baselineNodeMajor,
    supportedNodeMajors: toolingCiContract.supportedNodeMajors,
    externalCommand: toolingCiContract.externalCommand,
  });
}

function main(args) {
  if (args.length > 1 || (args.length === 1 && args[0] !== "--json")) {
    throw new Error("usage: node tooling/ci-contract.mjs [--json]");
  }
  const receipt = inspectToolingRuntime();
  if (args[0] === "--json") {
    process.stdout.write(`${JSON.stringify(receipt)}\n`);
  } else {
    process.stdout.write(
      `tooling CI runtime: Node ${receipt.nodeVersion} / V8 ${receipt.v8Version}\n`,
    );
  }
}

const invokedPath = process.argv[1];
if (invokedPath !== undefined && import.meta.url === pathToFileURL(invokedPath).href) {
  main(process.argv.slice(2));
}
