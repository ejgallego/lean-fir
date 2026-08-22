import assert from "node:assert/strict";
import test from "node:test";

import {
  describeSourcePackage,
  SOURCE_PACKAGE_DESCRIPTOR_VERSION,
} from "./source-package.mjs";

const build = {
  schemaVersion: "fixture.build/v2",
  toolchain: {
    leanToolchain: "leanprover/lean4:v4.33.0",
    leanVersion: "Lean (version 4.33.0, fixture-target, commit " +
      `${"5".repeat(40)}, Release)`,
  },
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
  payloadFiles: ["BUILD.json", "adapter.mjs", "module.wasm",
    "module.wasm.json", "smoke.mjs"],
  smokeFile: "smoke.mjs",
  build: { schemaVersion: "fixture.build/v2" },
  sourcePackage: {
    producer: {
      project: "fir",
      backend: "fir-native-wasm",
      lean: {
        toolchainPath: ["toolchain", "leanToolchain"],
        versionPath: ["toolchain", "leanVersion"],
      },
    },
    acceptance: { status: "accepted", authority: "verifier-policy" },
    evidenceFiles: ["module.wasm.json"],
    adapter: {
      file: "adapter.mjs",
      apiVersionPath: ["capabilities", "browserAdapter", "apiVersion"],
      operationInventoryPath: ["capabilities", "browserAdapter", "operations"],
      startupFields: ["fetchMs", "compileMs"],
      initializationFields: ["frontier", "pages"],
    },
    operations: [
      { name: "execute", mode: "production",
        inputContract: "fixture.browser/v1#execute/input",
        resultContract: "fixture.browser/v1#execute/result", phases: [] },
      { name: "executeTimed", mode: "diagnostic",
        inputContract: "fixture.browser/v1#executeTimed/input",
        resultContract: "fixture.browser/v1#executeTimed/result",
        phases: ["executeMs", "decodeMs"] },
      { name: "dispose", mode: "production",
        inputContract: "fixture.browser/v1#dispose/input",
        resultContract: "fixture.browser/v1#dispose/result", phases: [] },
    ],
    ownership: {
      capabilityPath: ["capabilities", "ownership"],
      model: "persistent-checkpoint-per-instance",
      arena: "persistent-prefix-with-rewound-scratch",
      reclamation: "drop-instance",
      rawAddressesExposed: false,
      transfer: {
        publicInput: "borrowed-immutable-javascript-values",
        encodedInput: "fresh-transferred-lean-graph",
        output: "decoded-javascript-copy",
      },
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
  assert.deepEqual(descriptor.package.acceptance,
    { status: "accepted", authority: "verifier-policy" });
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
    toolchain: { lean: {
      toolchain: "leanprover/lean4:v4.33.0",
      version: "4.33.0",
      commit: "5".repeat(40),
    } },
    artifact: {
      file: "module.wasm",
      byteLength: 8,
      sha256: "4".repeat(64),
      imports: [],
      exports: [{ name: "memory", kind: "memory" }],
    },
    adapter: {
      file: "adapter.mjs",
      apiVersion: "fixture.browser/v1",
      startupFields: ["fetchMs", "compileMs"],
      initializationFields: ["frontier", "pages"],
    },
  });
  assert.deepEqual(descriptor.verifier.evidenceFiles, ["module.wasm.json"]);
  assert.deepEqual(descriptor.operations, policy.sourcePackage.operations);
  assert.deepEqual(descriptor.ownership, {
    capabilityVersion: "fixture.ownership/v1",
    memoryOwner: "module",
    model: "persistent-checkpoint-per-instance",
    arena: "persistent-prefix-with-rewound-scratch",
    reclamation: "drop-instance",
    rawAddressesExposed: false,
    transfer: {
      publicInput: "borrowed-immutable-javascript-values",
      encodedInput: "fresh-transferred-lean-graph",
      output: "decoded-javascript-copy",
    },
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

test("rejects unbound discovery contracts", () => {
  assert.throws(() => describeSourcePackage(verification, {
    ...policy,
    sourcePackage: {
      ...policy.sourcePackage,
      evidenceFiles: ["unchecksummed.json"],
    },
  }), /evidence file is not checksummed/);
  assert.throws(() => describeSourcePackage({
    ...verification,
    build: {
      ...build,
      toolchain: { ...build.toolchain, leanVersion: "Lean 4.33.0" },
    },
  }, policy), /must contain normalized version and full commit/);
  assert.throws(() => describeSourcePackage(verification, {
    ...policy,
    sourcePackage: {
      ...policy.sourcePackage,
      operations: policy.sourcePackage.operations.map((operation, index) =>
        index === 0 ? { ...operation, inputContract: "" } : operation),
    },
  }), /input contract must not be empty/);
  assert.throws(() => describeSourcePackage(verification, {
    ...policy,
    sourcePackage: {
      ...policy.sourcePackage,
      adapter: {
        ...policy.sourcePackage.adapter,
        startupFields: ["compileMs", "compileMs"],
      },
    },
  }), /startup fields repeats a value/);
  assert.throws(() => describeSourcePackage(verification, {
    ...policy,
    sourcePackage: {
      ...policy.sourcePackage,
      ownership: {
        ...policy.sourcePackage.ownership,
        transfer: {
          ...policy.sourcePackage.ownership.transfer,
          output: "",
        },
      },
    },
  }), /output transfer must not be empty/);
});
