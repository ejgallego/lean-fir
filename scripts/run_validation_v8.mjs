import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";

const CASE_SPECS = new Map([
  ["uint8-max", {
    manifestResult: "uint8",
    resultSchema: { bits: { width: 8 } },
    lane: "i32",
    width: 8,
    maximum: "255",
  }],
  ["uint16-max", {
    manifestResult: "uint16",
    resultSchema: { bits: { width: 16 } },
    lane: "i32",
    width: 16,
    maximum: "65535",
  }],
  ["uint32-max", {
    manifestResult: "uint32",
    resultSchema: { bits: { width: 32 } },
    lane: "i32",
    width: 32,
    maximum: "4294967295",
  }],
  ["uint64-max", {
    manifestResult: "uint64",
    resultSchema: { bits: { width: 64 } },
    lane: "i64",
    width: 64,
    maximum: "18446744073709551615",
  }],
  ["usize-max", {
    manifestResult: "usize",
    resultSchema: "usize",
    lane: "i64",
    maximum: "18446744073709551615",
  }],
]);
const CASE_IDS = [...CASE_SPECS.keys()];

function requiredEnvironment(name) {
  const value = process.env[name];
  assert.ok(value, `${name} is not set`);
  return value;
}

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

assert.equal(requiredEnvironment("FIR_VALIDATION_PROTOCOL_VERSION"), "1");
assert.equal(requiredEnvironment("FIR_VALIDATION_BACKEND"), "v8");

const selectedCases = JSON.parse(requiredEnvironment("FIR_VALIDATION_CASES"));
assert.ok(Array.isArray(selectedCases) && selectedCases.length > 0,
  "the V8 adapter selection must be a nonempty array");
assert.equal(new Set(selectedCases).size, selectedCases.length,
  "the V8 adapter selection contains duplicates");
assert.ok(selectedCases.every((caseId) => CASE_SPECS.has(caseId)),
  "the V8 adapter selection contains an unsupported case");

const corpus = JSON.parse(
  await readFile(requiredEnvironment("FIR_VALIDATION_CORPUS"), "utf8"),
);
assert.equal(corpus.version, 1, "unsupported validation corpus version");
assert.ok(Array.isArray(corpus.cases), "validation corpus cases must be an array");

const products = JSON.parse(requiredEnvironment("FIR_VALIDATION_PRODUCTS"));
assert.equal(products.length, selectedCases.length * 2 + 1,
  "the V8 adapter requires its product inventory and two products per case");

const inventoryMatches = products.filter((product) =>
  product.kind === "product-manifest" && product.name === "products.json");
assert.equal(inventoryMatches.length, 1, "missing or duplicate product inventory");
const inventoryProduct = inventoryMatches[0];
assert.equal(inventoryProduct.backend, "v8");
assert.match(inventoryProduct.sha256, /^[0-9a-f]{64}$/);
const inventoryBytes = await readFile(inventoryProduct.path);
const consumedInventorySha256 = sha256(inventoryBytes);
assert.equal(consumedInventorySha256, inventoryProduct.sha256,
  "loaded product inventory disagrees with the captured product");
const inventory = JSON.parse(inventoryBytes.toString("utf8"));
const expectedInventoryProducts = products
  .filter((product) => product !== inventoryProduct)
  .map((product) => ({ kind: product.kind, path: product.name }))
  .sort((left, right) =>
    left.kind.localeCompare(right.kind) || left.path.localeCompare(right.path));
assert.equal(inventory.version, 1, "unsupported product inventory version");
assert.deepStrictEqual(
  [...inventory.products].sort((left, right) =>
    left.kind.localeCompare(right.kind) || left.path.localeCompare(right.path)),
  expectedInventoryProducts,
  "product inventory disagrees with captured products",
);

function caseProduct(caseId, kind, suffix) {
  const name = `modules/${caseId}.wasm${suffix}`;
  const matches = products.filter((product) =>
    product.kind === kind && product.name === name);
  assert.equal(matches.length, 1, `missing or duplicate ${kind} product for ${caseId}`);
  const product = matches[0];
  assert.equal(product.backend, "v8");
  assert.match(product.sha256, /^[0-9a-f]{64}$/);
  return product;
}

for (const caseId of selectedCases) {
  const spec = CASE_SPECS.get(caseId);
  assert.ok(spec, `unsupported V8 validation case ${caseId}`);
  const descriptor = corpus.cases.find((item) => item.id === caseId);
  assert.ok(descriptor, `validation corpus does not contain ${caseId}`);
  assert.deepStrictEqual(descriptor.args, [], `${caseId} must not take arguments`);
  assert.deepStrictEqual(descriptor.argSchemas, [], `${caseId} must not take arguments`);
  assert.deepStrictEqual(descriptor.resultSchema, spec.resultSchema,
    `${caseId} result schema mismatch`);
  assert.deepStrictEqual(descriptor.effectProjections, [],
    `${caseId} must not project host effects`);

  const manifestProduct = caseProduct(
    caseId, "wasm-manifest", ".json");
  const moduleProduct = caseProduct(caseId, "wasm-module", "");
  const manifestBytes = await readFile(manifestProduct.path);
  const consumedManifestSha256 = sha256(manifestBytes);
  assert.equal(consumedManifestSha256, manifestProduct.sha256,
    `loaded compiler manifest for ${caseId} disagrees with the captured product`);
  const compilerManifest = JSON.parse(manifestBytes.toString("utf8"));
  assert.deepStrictEqual(compilerManifest, {
    fixture: descriptor.entry,
    sourceEntry: descriptor.entry,
    entry: descriptor.entry,
    result: spec.manifestResult,
    params: [],
    arguments: [],
    imports: [],
  });

  const bytes = await readFile(moduleProduct.path);
  const consumedModuleSha256 = sha256(bytes);
  assert.equal(consumedModuleSha256, moduleProduct.sha256,
    `loaded Wasm bytes for ${caseId} disagree with the captured product`);
  assert.ok(WebAssembly.validate(bytes),
    `V8 rejected the generated WebAssembly module for ${caseId}`);
  const wasmModule = await WebAssembly.compile(bytes);
  assert.deepStrictEqual(WebAssembly.Module.imports(wasmModule), [],
    `${caseId} unexpectedly requires a semantic host`);
  assert.deepStrictEqual(WebAssembly.Module.exports(wasmModule), [
    { name: descriptor.entry, kind: "function" },
  ]);
  const instance = await WebAssembly.instantiate(wasmModule, {});
  const entry = instance.exports[descriptor.entry];
  assert.equal(typeof entry, "function", `missing Wasm export ${descriptor.entry}`);
  const physicalResult = entry();
  let value;
  if (spec.lane === "i32") {
    assert.equal(typeof physicalResult, "number", `${caseId} must use V8's i32 lane`);
    value = (physicalResult >>> 0).toString();
  } else {
    assert.equal(typeof physicalResult, "bigint", `${caseId} must use V8's i64 lane`);
    value = BigInt.asUintN(64, physicalResult).toString();
  }
  assert.equal(value, spec.maximum, `${caseId} did not return its scalar maximum`);
  const datum = spec.width === undefined
    ? { usize: { value } }
    : { bits: { width: spec.width, value } };
  const receipt = JSON.stringify([
    {
      kind: inventoryProduct.kind,
      name: inventoryProduct.name,
      sha256: consumedInventorySha256,
    },
    {
      kind: manifestProduct.kind,
      name: manifestProduct.name,
      sha256: consumedManifestSha256,
    },
    {
      kind: moduleProduct.kind,
      name: moduleProduct.name,
      sha256: consumedModuleSha256,
    },
  ]);
  const result = {
    version: 1,
    caseId,
    backend: "v8",
    diagnostics: [{ key: "validation-products", value: receipt }],
    outcome: {
      success: {
        observation: {
          termination: {
            returned: { value: datum },
          },
          stdout: "",
          stderr: "",
          effects: [],
        },
      },
    },
  };
  console.log(JSON.stringify(result));
}
