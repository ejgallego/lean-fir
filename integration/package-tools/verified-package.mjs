import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  chmodSync,
  copyFileSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  renameSync,
  rmSync,
} from "node:fs";
import { basename, dirname, join, resolve } from "node:path";

import { sha256, verifyChecksumManifest } from "./immutable-package.mjs";
import { describeSourcePackage } from "./source-package.mjs";

export const BROWSER_PACKAGE_POLICY_VERSION =
  "fir.browser-package-policy/v1";

function pathExists(path) {
  try {
    lstatSync(path);
    return true;
  } catch (error) {
    if (error?.code === "ENOENT") return false;
    throw error;
  }
}

function valueAt(root, path, label) {
  assert.ok(Array.isArray(path) && path.length > 0,
    `${label} path must be a nonempty Array`);
  let value = root;
  for (const component of path) {
    assert.equal(typeof component, "string", `${label} path is invalid`);
    assert.notEqual(component, "", `${label} path is invalid`);
    assert.ok(value !== null && typeof value === "object" &&
      Object.hasOwn(value, component),
    `${label} is missing ${path.join(".")}`);
    value = value[component];
  }
  return value;
}

function requirePolicy(policy) {
  assert.ok(policy !== null && typeof policy === "object",
    "package policy must be an object");
  assert.equal(policy.version, BROWSER_PACKAGE_POLICY_VERSION,
    "package policy version changed");
  assert.equal(typeof policy.name, "string", "package policy needs a name");
  assert.ok(Array.isArray(policy.payloadFiles) && policy.payloadFiles.length > 0,
    "package policy needs payloadFiles");
  assert.ok(policy.build !== null && typeof policy.build === "object",
    "package policy needs a build contract");
  assert.ok(policy.wasm !== null && typeof policy.wasm === "object",
    "package policy needs a Wasm contract");
  return policy;
}

function readJson(path, label) {
  try {
    const value = JSON.parse(readFileSync(path, "utf8"));
    assert.ok(value !== null && typeof value === "object" &&
      !Array.isArray(value), `${label} must contain a JSON object`);
    return value;
  } catch (error) {
    throw new Error(`${label} is invalid: ${error.message}`, { cause: error });
  }
}

function verifyRequiredValues(build, requirements = []) {
  assert.ok(Array.isArray(requirements),
    "build requirements must be an Array");
  for (const [index, requirement] of requirements.entries()) {
    assert.ok(requirement !== null && typeof requirement === "object",
      `build requirement ${index} must be an object`);
    const label = requirement.label ?? requirement.path?.join(".") ??
      `build requirement ${index}`;
    assert.deepEqual(valueAt(build, requirement.path, label),
      requirement.equals, `${label} changed`);
  }
}

/**
 * Verify the package's exact checksum inventory and its public Wasm contract.
 * Workload semantics and memory-growth assertions intentionally remain local.
 */
export function verifyBrowserPackage(directory, packagePolicy) {
  const policy = requirePolicy(packagePolicy);
  const root = realpathSync(directory);
  verifyChecksumManifest(root, policy.payloadFiles);

  const buildFile = policy.build.file ?? "BUILD.json";
  assert.ok(policy.payloadFiles.includes(buildFile),
    "BUILD.json must be part of the checksummed payload");
  const build = readJson(join(root, buildFile), buildFile);
  const schemaField = policy.build.schemaField ?? "schemaVersion";
  assert.equal(build[schemaField], policy.build.schemaVersion,
    `${buildFile} ${schemaField} changed`);
  verifyRequiredValues(build, policy.build.requiredValues);

  const wasmFile = policy.wasm.file;
  assert.equal(typeof wasmFile, "string", "Wasm policy needs a file");
  assert.ok(policy.payloadFiles.includes(wasmFile),
    "Wasm file must be part of the checksummed payload");
  const wasm = readFileSync(join(root, wasmFile));
  const metadata = valueAt(build, policy.wasm.metadataPath ?? ["wasm"],
    "Wasm metadata");
  assert.equal(metadata.file, wasmFile, "BUILD.json Wasm file changed");
  assert.equal(metadata.byteLength, wasm.byteLength,
    "BUILD.json Wasm byte length changed");
  assert.equal(metadata.sha256, sha256(wasm),
    "BUILD.json Wasm SHA-256 changed");

  const module = new WebAssembly.Module(wasm);
  const imports = WebAssembly.Module.imports(module);
  const exports = WebAssembly.Module.exports(module);
  const functionImports = imports.filter(({ kind }) => kind === "function");
  const memoryImports = imports.filter(({ kind }) => kind === "memory");
  assert.equal(metadata.functionImportCount, functionImports.length,
    "BUILD.json function-import count changed");
  assert.equal(metadata.memoryImportCount, memoryImports.length,
    "BUILD.json memory-import count changed");
  if (policy.wasm.requireZeroImports) {
    assert.deepEqual(imports, [], "package must have zero Wasm imports");
  }
  if (policy.wasm.memoryOwner !== undefined) {
    assert.equal(metadata.memoryOwner, policy.wasm.memoryOwner,
      "BUILD.json memory owner changed");
  }

  const expectedExports = policy.wasm.expectedExports ?? metadata.exports;
  assert.ok(Array.isArray(expectedExports),
    "Wasm policy or BUILD.json must declare exact exports");
  assert.deepEqual(exports, expectedExports, "public Wasm exports changed");
  if (metadata.functionExportCount !== undefined) {
    assert.equal(metadata.functionExportCount,
      exports.filter(({ kind }) => kind === "function").length,
    "BUILD.json function-export count changed");
  }
  if (metadata.memoryExports !== undefined) {
    assert.deepEqual(metadata.memoryExports,
      exports.filter(({ kind }) => kind === "memory").map(({ name }) => name),
    "BUILD.json memory-export inventory changed");
  }

  let descriptor = null;
  if (policy.wasm.descriptorFile !== undefined) {
    const descriptorFile = policy.wasm.descriptorFile;
    assert.ok(policy.payloadFiles.includes(descriptorFile),
      "Wasm descriptor must be part of the checksummed payload");
    descriptor = readJson(join(root, descriptorFile), descriptorFile);
    assert.deepEqual(descriptor.imports, imports,
      "Wasm descriptor import inventory changed");
    if (policy.wasm.requireCompleteRuntime) {
      assert.equal(descriptor.completeRuntime, true,
        "Wasm descriptor must declare a complete runtime");
    }
  }

  const verification = {
    root, build, descriptor, wasm, metadata, module, imports, exports,
  };
  return {
    ...verification,
    sourcePackage: describeSourcePackage(verification, policy),
  };
}

export function resolveFreshOutputPath(value) {
  assert.equal(typeof value, "string", "output path must be a string");
  assert.notEqual(value, "", "output path must not be empty");
  const component = basename(value);
  assert.notEqual(component, "", "output path must have a final component");
  assert.notEqual(component, ".", "output path must not end in .");
  assert.notEqual(component, "..", "output path must not end in ..");
  const absolute = resolve(value);
  if (pathExists(absolute)) {
    throw new Error(`output directory must be fresh: ${absolute}`);
  }
  mkdirSync(dirname(absolute), { recursive: true });
  return join(realpathSync(dirname(absolute)), component);
}

function runPackagedSmoke(directory, policy) {
  assert.equal(typeof policy.smokeFile, "string",
    "package policy needs a smokeFile or the installer needs runSmoke");
  execFileSync(process.execPath, [policy.smokeFile], {
    cwd: directory,
    stdio: "inherit",
  });
}

/** Copy, verify, smoke, and atomically install a package into a fresh path. */
export function installVerifiedPackage({
  sourceDirectory,
  outputDirectory,
  policy: packagePolicy,
  runSmoke = null,
}) {
  const policy = requirePolicy(packagePolicy);
  const source = realpathSync(sourceDirectory);
  verifyBrowserPackage(source, policy);
  const output = resolveFreshOutputPath(outputDirectory);
  const staging = mkdtempSync(join(dirname(output),
    `.${basename(output)}.stage.`));
  const packageFiles = [...policy.payloadFiles, "SHA256SUMS"];
  const smoke = runSmoke ?? ((directory) => runPackagedSmoke(directory, policy));
  let published = false;
  try {
    for (const name of packageFiles) {
      copyFileSync(join(source, name), join(staging, name));
      chmodSync(join(staging, name), 0o644);
    }
    verifyBrowserPackage(staging, policy);
    smoke(staging);
    renameSync(staging, output);
    published = true;
    verifyBrowserPackage(output, policy);
    smoke(output);
    return output;
  } catch (error) {
    if (published) rmSync(output, { recursive: true, force: true });
    throw error;
  } finally {
    if (!published) rmSync(staging, { recursive: true, force: true });
  }
}
