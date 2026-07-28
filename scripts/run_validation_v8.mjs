import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { pathToFileURL } from "node:url";

const semanticHostPath = process.argv[2];
const validationExternalsPath = process.argv[3];
const validationCasePath = process.argv[4];
assert.ok(semanticHostPath && validationExternalsPath && validationCasePath,
  "usage: node run_validation_v8.mjs " +
  "<semantic-host> <validation-externals> <validation-case-runner>");
const semanticRuntime = await import(pathToFileURL(semanticHostPath).href);
const validationExternals = await import(pathToFileURL(validationExternalsPath).href);
const {
  executeSemanticWasmCase,
  SEMANTIC_WASM_CONTRACT,
  VALIDATION_PROTOCOL_VERSION,
} = await import(pathToFileURL(validationCasePath).href);

const PROTOCOL_VERSION = VALIDATION_PROTOCOL_VERSION;

function requiredEnvironment(name) {
  const value = process.env[name];
  assert.ok(value, `${name} is not set`);
  return value;
}

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function compareProtocolStrings(left, right) {
  return left < right ? -1 : left > right ? 1 : 0;
}

assert.equal(requiredEnvironment("FIR_VALIDATION_PROTOCOL_VERSION"),
  String(PROTOCOL_VERSION));
assert.equal(requiredEnvironment("FIR_VALIDATION_BACKEND"), "v8");

const executionInput = JSON.parse(
  await readFile(requiredEnvironment("FIR_VALIDATION_EXECUTION_INPUT"), "utf8"),
);
assert.deepStrictEqual(Object.keys(executionInput).sort(), [
  "version", "backend", "selectedCases", "products", "productBundle",
].sort(), "malformed V8 execution input");
assert.equal(executionInput.version, PROTOCOL_VERSION,
  "unsupported V8 execution-input version");
assert.equal(executionInput.backend, "v8",
  "the V8 execution input names the wrong backend");

const selectedCases = executionInput.selectedCases;
assert.ok(Array.isArray(selectedCases) && selectedCases.length > 0,
  "the V8 adapter selection must be a nonempty array");
assert.equal(new Set(selectedCases).size, selectedCases.length,
  "the V8 adapter selection contains duplicates");

const corpus = JSON.parse(
  await readFile(requiredEnvironment("FIR_VALIDATION_CORPUS"), "utf8"),
);
assert.equal(corpus.version, PROTOCOL_VERSION, "unsupported validation corpus version");
assert.ok(Array.isArray(corpus.cases), "validation corpus cases must be an array");

const products = executionInput.products;
assert.ok(Array.isArray(products) && products.length > 0,
  "the V8 adapter requires a nonempty provider product inventory");

const productBundle = executionInput.productBundle;
assert.deepStrictEqual(Object.keys(productBundle).sort(), [
  "version", "provider", "contract", "bundleSha256", "products", "cases",
].sort(), "malformed semantic Wasm product bundle");
assert.equal(productBundle.version, PROTOCOL_VERSION,
  "unsupported semantic Wasm product bundle version");
assert.equal(productBundle.provider, "lean-wasm-semantic",
  "the V8 adapter received the wrong semantic Wasm provider");
assert.deepStrictEqual(productBundle.contract, SEMANTIC_WASM_CONTRACT,
  "the V8 adapter received the wrong semantic Wasm contract");
assert.match(productBundle.bundleSha256, /^[0-9a-f]{64}$/,
  "malformed semantic Wasm bundle identity");
assert.ok(Array.isArray(productBundle.products) && productBundle.products.length > 0,
  "the semantic Wasm bundle must contain products");
assert.ok(Array.isArray(productBundle.cases),
  "the semantic Wasm bundle cases must be an array");

function checkedProduct(product, context, withPath) {
  const fields = ["backend", "kind", "name", "sha256"];
  if (withPath) {
    fields.push("path");
  }
  assert.ok(product && typeof product === "object" && !Array.isArray(product),
    `${context} must be an object`);
  assert.deepStrictEqual(Object.keys(product).sort(), fields.sort(),
    `${context} has malformed fields`);
  assert.equal(product.backend, productBundle.provider,
    `${context} has the wrong provider`);
  assert.ok(typeof product.kind === "string" && product.kind.length > 0,
    `${context} has a malformed kind`);
  assert.ok(typeof product.name === "string" && product.name.length > 0,
    `${context} has a malformed name`);
  assert.match(product.sha256, /^[0-9a-f]{64}$/,
    `${context} has a malformed digest`);
  if (withPath) {
    assert.ok(typeof product.path === "string" && product.path.length > 0,
      `${context} has a malformed path`);
  }
  return product;
}

const exposedProducts = products.map((product, index) =>
  checkedProduct(product, `provider product ${index}`, true));
const bundleProducts = productBundle.products.map((product, index) =>
  checkedProduct(product, `bundle product ${index}`, false));
assert.deepStrictEqual(
  bundleProducts,
  exposedProducts.map(({ path: _path, ...product }) => product),
  "the exposed products disagree with the semantic Wasm bundle",
);

function productKey(product) {
  return JSON.stringify([
    product.backend, product.kind, product.name, product.sha256,
  ]);
}

const productByKey = new Map(
  exposedProducts.map((product) => [productKey(product), product]),
);
assert.equal(productByKey.size, exposedProducts.length,
  "the exposed provider product inventory contains duplicates");
const expectedCaseIds = [...selectedCases].sort(compareProtocolStrings);
const referencedProductKeys = new Set();
const productsByCase = new Map();
const bundleCaseIds = [];
for (const [index, binding] of productBundle.cases.entries()) {
  assert.ok(binding && typeof binding === "object" && !Array.isArray(binding),
    `bundle case ${index} must be an object`);
  assert.deepStrictEqual(Object.keys(binding).sort(), ["caseId", "products"],
    `bundle case ${index} has malformed fields`);
  assert.ok(typeof binding.caseId === "string" && binding.caseId.length > 0,
    `bundle case ${index} has a malformed case ID`);
  assert.ok(Array.isArray(binding.products) && binding.products.length > 0,
    `bundle case ${binding.caseId} must contain products`);
  const caseProducts = binding.products.map((product, productIndex) => {
    checkedProduct(
      product,
      `bundle case ${binding.caseId} product ${productIndex}`,
      false,
    );
    const key = productKey(product);
    const exposed = productByKey.get(key);
    assert.ok(exposed,
      `bundle case ${binding.caseId} references an unexposed product`);
    referencedProductKeys.add(key);
    return exposed;
  });
  assert.equal(new Set(caseProducts.map(productKey)).size, caseProducts.length,
    `bundle case ${binding.caseId} contains duplicate products`);
  assert.deepStrictEqual(
    caseProducts.map((product) => product.kind),
    ["wasm-manifest", "wasm-module"],
    `bundle case ${binding.caseId} must bind one manifest and one module`,
  );
  bundleCaseIds.push(binding.caseId);
  productsByCase.set(binding.caseId, caseProducts);
}
assert.deepStrictEqual(bundleCaseIds, expectedCaseIds,
  "the product bundle case IDs disagree with the V8 selection");
assert.deepStrictEqual(
  [...referencedProductKeys].sort(compareProtocolStrings),
  [...productByKey.keys()].sort(compareProtocolStrings),
  "the semantic Wasm bundle contains unbound products",
);

function caseProduct(caseId, kind) {
  const matches = productsByCase.get(caseId).filter((product) =>
    product.kind === kind);
  assert.equal(matches.length, 1, `missing or duplicate ${kind} product for ${caseId}`);
  return matches[0];
}

for (const caseId of selectedCases) {
  const descriptorMatches = corpus.cases.filter((item) => item.id === caseId);
  assert.equal(descriptorMatches.length, 1,
    `validation corpus must contain exactly one ${caseId} descriptor`);
  const descriptor = descriptorMatches[0];
  assert.equal(descriptor.args.length, descriptor.argSchemas.length,
    `${caseId} argument schema/fixture arity mismatch`);
  assert.ok(Array.isArray(descriptor.effectProjections),
    `${caseId} effect projections must be an array`);

  const manifestProduct = caseProduct(caseId, "wasm-manifest");
  const moduleProduct = caseProduct(caseId, "wasm-module");
  const manifestBytes = await readFile(manifestProduct.path);
  const consumedManifestSha256 = sha256(manifestBytes);
  assert.equal(consumedManifestSha256, manifestProduct.sha256,
    `loaded compiler manifest for ${caseId} disagrees with the captured product`);
  const compilerManifest = JSON.parse(manifestBytes.toString("utf8"));

  const bytes = await readFile(moduleProduct.path);
  const consumedModuleSha256 = sha256(bytes);
  assert.equal(consumedModuleSha256, moduleProduct.sha256,
    `loaded Wasm bytes for ${caseId} disagree with the captured product`);
  const observation = await executeSemanticWasmCase({
    caseId,
    descriptor,
    compilerManifest,
    bytes,
    semanticRuntime,
    validationExternals,
  });
  const consumedSha256 = new Map([
    [productKey(manifestProduct), consumedManifestSha256],
    [productKey(moduleProduct), consumedModuleSha256],
  ]);
  const receipt = JSON.stringify({
    provider: productBundle.provider,
    bundleSha256: productBundle.bundleSha256,
    products: productsByCase.get(caseId).map((product) => ({
      kind: product.kind,
      name: product.name,
      sha256: consumedSha256.get(productKey(product)),
    })),
  });
  const result = {
    version: PROTOCOL_VERSION,
    caseId,
    backend: "v8",
    diagnostics: [{ key: "validation-product-bundle", value: receipt }],
    outcome: {
      success: { observation },
    },
  };
  console.log(JSON.stringify(result));
}
