import assert from "node:assert/strict";
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";

import {
  checksumManifest,
  sha256,
} from "./immutable-package.mjs";
import {
  BROWSER_PACKAGE_POLICY_VERSION,
  installVerifiedPackage,
  verifyBrowserPackage,
} from "./verified-package.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const scratchRoot = join(directory, "../../.deps/package-tools-tests");
const payloadFiles = ["BUILD.json", "module.wasm", "module.wasm.json",
  "smoke.mjs"];
const wasm = Buffer.from([
  0, 0x61, 0x73, 0x6d, 1, 0, 0, 0,
  5, 3, 1, 0, 1,
  7, 10, 1, 6, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 2, 0,
]);
const policy = Object.freeze({
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "module-owned fixture",
  payloadFiles,
  smokeFile: "smoke.mjs",
  build: {
    schemaVersion: "fixture.build/v1",
    requiredValues: [
      { path: ["capabilities", "inputLayout", "version"],
        equals: "fixture.input/v2" },
      { path: ["capabilities", "completeRuntime", "selfContained"],
        equals: true },
    ],
  },
  wasm: {
    file: "module.wasm",
    descriptorFile: "module.wasm.json",
    requireCompleteRuntime: true,
    requireZeroImports: true,
    memoryOwner: "module",
    expectedExports: [{ name: "memory", kind: "memory" }],
  },
});

function withDirectory(run) {
  mkdirSync(scratchRoot, { recursive: true });
  const root = mkdtempSync(join(scratchRoot, "verified-package-"));
  try {
    return run(root);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

function buildMetadata(inputLayout = "fixture.input/v2") {
  return {
    schemaVersion: "fixture.build/v1",
    wasm: {
      file: "module.wasm",
      byteLength: wasm.byteLength,
      sha256: sha256(wasm),
      functionImportCount: 0,
      memoryImportCount: 0,
      memoryOwner: "module",
      exports: [{ name: "memory", kind: "memory" }],
    },
    capabilities: {
      inputLayout: { version: inputLayout },
      completeRuntime: { selfContained: true },
    },
  };
}

function packageFixture(root, build = buildMetadata(), smoke = "export {};\n") {
  mkdirSync(root);
  writeFileSync(join(root, "BUILD.json"), `${JSON.stringify(build)}\n`);
  writeFileSync(join(root, "module.wasm"), wasm);
  writeFileSync(join(root, "module.wasm.json"),
    "{\"imports\":[],\"completeRuntime\":true}\n");
  writeFileSync(join(root, "smoke.mjs"), smoke);
  writeFileSync(join(root, "SHA256SUMS"),
    checksumManifest(root, payloadFiles));
}

test("verifies exact checksums, capabilities, and the public Wasm surface", () =>
  withDirectory((root) => {
    const source = join(root, "source");
    packageFixture(source);
    const result = verifyBrowserPackage(source, policy);
    assert.equal(result.wasm.byteLength, wasm.byteLength);
    assert.deepEqual(result.imports, []);
    assert.deepEqual(result.exports, [{ name: "memory", kind: "memory" }]);

    writeFileSync(join(source, "BUILD.json"),
      `${JSON.stringify(buildMetadata("fixture.input/v3"))}\n`);
    writeFileSync(join(source, "SHA256SUMS"),
      checksumManifest(source, payloadFiles));
    assert.throws(() => verifyBrowserPackage(source, policy),
      /inputLayout\.version changed/);
  }));

test("installs only a verified and smoked package into a fresh directory", () =>
  withDirectory((root) => {
    const source = join(root, "source");
    const output = join(root, "accepted");
    packageFixture(source);
    let smokes = 0;
    assert.equal(installVerifiedPackage({
      sourceDirectory: source,
      outputDirectory: output,
      policy,
      runSmoke(directory) {
        assert.equal(readFileSync(join(directory, "smoke.mjs"), "utf8"),
          "export {};\n");
        smokes += 1;
      },
    }), output);
    assert.equal(smokes, 2);
    assert.throws(() => installVerifiedPackage({
      sourceDirectory: source,
      outputDirectory: output,
      policy,
    }), /output directory must be fresh/);

    const rejected = join(root, "rejected");
    assert.throws(() => installVerifiedPackage({
      sourceDirectory: source,
      outputDirectory: rejected,
      policy,
      runSmoke() { throw new Error("smoke rejected package"); },
    }), /smoke rejected package/);
    assert.equal(existsSync(rejected), false);
  }));
