import assert from "node:assert/strict";
import test from "node:test";

import {
  inspectToolingRuntime,
  parseNodeMajor,
  toolingCiContract,
} from "./ci-contract.mjs";

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
