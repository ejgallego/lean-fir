import assert from "node:assert/strict";
import test from "node:test";

import {
  describeSourcePackage,
  SOURCE_PACKAGE_DESCRIPTOR_VERSION,
} from "./source-package.mjs";

const build = {
  schemaVersion: "fixture.build/v2",
  sources: {
    upstream: {
      commit: "2".repeat(40),
      dirty: true,
      relevantFiles: [{ path: "Source.lean", sha256: "3".repeat(64),
        status: "modified" }],
    },
    fir: {
      repository: "https://example.invalid/fir.git",
      commit: "1".repeat(40),
      dirty: false,
    },
  },
  capabilities: {
    browserAdapter: {
      apiVersion: "fixture.browser/v1",
      operations: ["execute", "executeTimed", "dispose"],
    },
    ownership: { version: "fixture.ownership/v1" },
  },
};
const policy = {
  version: "fir.browser-package-policy/v1",
  name: "fixture package",
  payloadFiles: ["BUILD.json", "adapter.mjs", "module.wasm", "smoke.mjs"],
  smokeFile: "smoke.mjs",
  build: { schemaVersion: "fixture.build/v2" },
  sourcePackage: {
    producer: { project: "fir", backend: "fir-native-wasm" },
    adapter: {
      file: "adapter.mjs",
      apiVersionPath: ["capabilities", "browserAdapter", "apiVersion"],
      operationInventoryPath: ["capabilities", "browserAdapter", "operations"],
    },
    operations: [
      { name: "execute", mode: "production", phases: [] },
      { name: "executeTimed", mode: "diagnostic",
        phases: ["executeMs", "decodeMs"] },
      { name: "dispose", mode: "production", phases: [] },
    ],
    ownership: {
      capabilityPath: ["capabilities", "ownership"],
      model: "persistent-checkpoint-per-instance",
      arena: "persistent-prefix-with-rewound-scratch",
      reclamation: "drop-instance",
      rawAddressesExposed: false,
    },
  },
};
const verification = {
  build,
  metadata: {
    file: "module.wasm",
    byteLength: 8,
    sha256: "4".repeat(64),
    memoryOwner: "module",
  },
  imports: [],
  exports: [{ name: "memory", kind: "memory" }],
};

test("normalizes producer facts without importing workload semantics", () => {
  const descriptor = describeSourcePackage(verification, policy);
  assert.equal(descriptor.schemaVersion, SOURCE_PACKAGE_DESCRIPTOR_VERSION);
  assert.deepEqual(descriptor.provenance.sources, [
    {
      role: "fir",
      repository: "https://example.invalid/fir.git",
      commit: "1".repeat(40),
      dirty: false,
      relevantFiles: [],
    },
    {
      role: "upstream",
      repository: null,
      commit: "2".repeat(40),
      dirty: true,
      relevantFiles: [{ path: "Source.lean", sha256: "3".repeat(64) }],
    },
  ]);
  assert.deepEqual(descriptor.producer, {
    project: "fir",
    backend: "fir-native-wasm",
    artifact: {
      file: "module.wasm",
      byteLength: 8,
      sha256: "4".repeat(64),
      imports: [],
      exports: [{ name: "memory", kind: "memory" }],
    },
    adapter: { file: "adapter.mjs", apiVersion: "fixture.browser/v1" },
  });
  assert.deepEqual(descriptor.operations, policy.sourcePackage.operations);
  assert.deepEqual(descriptor.ownership, {
    capabilityVersion: "fixture.ownership/v1",
    memoryOwner: "module",
    model: "persistent-checkpoint-per-instance",
    arena: "persistent-prefix-with-rewound-scratch",
    reclamation: "drop-instance",
    rawAddressesExposed: false,
  });
  assert.equal(Object.hasOwn(descriptor, "benchmark"), false);
  assert.equal(Object.hasOwn(descriptor, "oracle"), false);
});

test("rejects operation drift and remains optional", () => {
  assert.throws(() => describeSourcePackage({
    ...verification,
    build: {
      ...build,
      capabilities: {
        ...build.capabilities,
        browserAdapter: {
          ...build.capabilities.browserAdapter,
          operations: ["execute", "dispose"],
        },
      },
    },
  }, policy), /operations differ from BUILD\.json/);
  assert.equal(describeSourcePackage(verification, {
    ...policy, sourcePackage: undefined,
  }), null);
});
