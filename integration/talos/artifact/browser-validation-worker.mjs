import assert from "../../../scripts/wasm_assert.mjs";
import * as semanticRuntime from "../../../scripts/wasm_semantic_host.mjs";
import * as validationExternals from "../../../scripts/wasm_validation_externals.mjs";
import {
  executeSemanticWasmCase,
  SEMANTIC_WASM_CONTRACT,
  VALIDATION_PROTOCOL_VERSION,
} from "../../../scripts/wasm_validation_case.mjs";
import {
  CONCRETE_VALIDATION_BLOCKED_CASES,
  concreteValidationBlockers,
  executeConcreteValidationCase,
} from "./concrete-validation-case.mjs";

const validationPath = new URLSearchParams(globalThis.location.search)
  .get("validation") ?? "_build/validation-v8";
assert.ok(/^_build\/[A-Za-z0-9._/-]+$/.test(validationPath) &&
  !validationPath.split("/").includes(".."),
  "browser validation path must be a repository-local _build directory");
const validationBase = new URL(`../../../${validationPath}/`, import.meta.url);
const PROVIDER = "lean-wasm-semantic";
const ENGINE = "v8";

async function fetchBytes(url, context) {
  const response = await fetch(url);
  assert.ok(response.ok, `${context} fetch failed with HTTP ${response.status}`);
  return new Uint8Array(await response.arrayBuffer());
}

async function fetchJson(url, context) {
  const response = await fetch(url);
  assert.ok(response.ok, `${context} fetch failed with HTTP ${response.status}`);
  return response.json();
}

async function sha256(bytes) {
  const digest = await crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)]
    .map((value) => value.toString(16).padStart(2, "0"))
    .join("");
}

function checkedProduct(product, context) {
  assert.ok(product && typeof product === "object" && !Array.isArray(product),
    `${context} must be an object`);
  assert.deepStrictEqual(Object.keys(product).sort(),
    ["backend", "kind", "name", "sha256"].sort(),
    `${context} has malformed fields`);
  assert.equal(product.backend, PROVIDER, `${context} has the wrong provider`);
  assert.ok(typeof product.kind === "string" && product.kind.length > 0,
    `${context} has a malformed kind`);
  assert.ok(typeof product.name === "string" && product.name.length > 0 &&
    !product.name.startsWith("/") && !product.name.split("/").includes(".."),
    `${context} has an unsafe product name`);
  assert.ok(/^[0-9a-f]{64}$/.test(product.sha256),
    `${context} has a malformed digest`);
  return product;
}

function productKey(product) {
  return JSON.stringify([
    product.backend,
    product.kind,
    product.name,
    product.sha256,
  ]);
}

async function fetchedProduct(product, caseId) {
  const bytes = await fetchBytes(
    new URL(`${product.backend}/${product.name}`, validationBase),
    `${caseId} ${product.kind}`,
  );
  assert.equal(await sha256(bytes), product.sha256,
    `${caseId} ${product.kind} disagrees with the shared product bundle`);
  return bytes;
}

async function runValidationCorpus() {
  const matrix = await fetchJson(new URL("matrix.json", validationBase), "validation matrix");
  assert.equal(matrix.version, VALIDATION_PROTOCOL_VERSION,
    "unsupported validation matrix version");
  assert.ok(Array.isArray(matrix.selectedCases) && matrix.selectedCases.length > 0,
    "validation matrix must select cases");
  assert.equal(new Set(matrix.selectedCases).size, matrix.selectedCases.length,
    "validation matrix selects duplicate cases");
  assert.ok(Array.isArray(matrix.productBundles),
    "validation matrix has no shared product bundles");
  const bundles = matrix.productBundles.filter((item) => item.provider === PROVIDER);
  assert.equal(bundles.length, 1, `validation matrix must contain one ${PROVIDER} bundle`);
  const bundle = bundles[0];
  assert.equal(bundle.version, VALIDATION_PROTOCOL_VERSION,
    "unsupported semantic Wasm bundle version");
  assert.deepStrictEqual(bundle.contract, SEMANTIC_WASM_CONTRACT,
    "semantic Wasm bundle contract mismatch");
  assert.ok(/^[0-9a-f]{64}$/.test(bundle.bundleSha256),
    "semantic Wasm bundle has a malformed identity");
  assert.ok(Array.isArray(bundle.products) && bundle.products.length > 0,
    "semantic Wasm bundle has no products");
  assert.ok(Array.isArray(bundle.cases), "semantic Wasm bundle has no case bindings");

  const products = bundle.products.map((product, index) =>
    checkedProduct(product, `bundle product ${index}`));
  const productByKey = new Map(products.map((product) => [productKey(product), product]));
  assert.equal(productByKey.size, products.length,
    "semantic Wasm bundle contains duplicate products");
  const byCase = new Map();
  const referenced = new Set();
  for (const [index, binding] of bundle.cases.entries()) {
    assert.deepStrictEqual(Object.keys(binding).sort(), ["caseId", "products"],
      `bundle case ${index} has malformed fields`);
    assert.ok(typeof binding.caseId === "string" && binding.caseId.length > 0,
      `bundle case ${index} has a malformed ID`);
    assert.ok(Array.isArray(binding.products),
      `bundle case ${binding.caseId} products must be an array`);
    const caseProducts = binding.products.map((product, productIndex) => {
      checkedProduct(product, `bundle case ${binding.caseId} product ${productIndex}`);
      const canonical = productByKey.get(productKey(product));
      assert.ok(canonical, `bundle case ${binding.caseId} references an unknown product`);
      referenced.add(productKey(product));
      return canonical;
    });
    assert.deepStrictEqual(caseProducts.map((product) => product.kind),
      ["wasm-manifest", "wasm-module"],
      `bundle case ${binding.caseId} must bind one manifest and one module`);
    assert.ok(!byCase.has(binding.caseId), `bundle contains duplicate case ${binding.caseId}`);
    byCase.set(binding.caseId, caseProducts);
  }
  assert.deepStrictEqual([...byCase.keys()].sort(), [...matrix.selectedCases].sort(),
    "semantic Wasm bundle cases disagree with the validation selection");
  assert.deepStrictEqual([...referenced].sort(), [...productByKey.keys()].sort(),
    "semantic Wasm bundle contains unbound products");

  const corpus = await fetchJson(new URL("corpus.json", validationBase), "validation corpus");
  assert.equal(corpus.version, VALIDATION_PROTOCOL_VERSION,
    "unsupported validation corpus version");
  assert.ok(Array.isArray(corpus.cases), "validation corpus cases must be an array");
  const descriptorById = new Map(corpus.cases.map((item) => [item.id, item]));
  assert.equal(descriptorById.size, corpus.cases.length,
    "validation corpus contains duplicate descriptors");

  const concreteExecuted = [];
  const concreteBlocked = [];
  for (const caseId of matrix.selectedCases) {
    const descriptor = descriptorById.get(caseId);
    assert.ok(descriptor, `validation corpus is missing ${caseId}`);
    const [manifestProduct, moduleProduct] = byCase.get(caseId);
    const manifestBytes = await fetchedProduct(manifestProduct, caseId);
    const compilerManifest = JSON.parse(new TextDecoder().decode(manifestBytes));
    const moduleBytes = await fetchedProduct(moduleProduct, caseId);
    const observation = await executeSemanticWasmCase({
      caseId,
      descriptor,
      compilerManifest,
      bytes: moduleBytes,
      semanticRuntime,
      validationExternals,
    });
    const expected = await fetchJson(
      new URL(`${caseId}/${ENGINE}/result.json`, validationBase),
      `${caseId} canonical ${ENGINE} result`,
    );
    assert.equal(expected.caseId, caseId, `${caseId} canonical result case mismatch`);
    assert.equal(expected.backend, ENGINE, `${caseId} canonical result backend mismatch`);
    assert.deepStrictEqual(expected.outcome, { success: { observation } },
      `${caseId} browser observation disagrees with canonical ${ENGINE}`);

    const blockers = concreteValidationBlockers(compilerManifest);
    if (blockers.length > 0) {
      concreteBlocked.push({ caseId, blockers });
    } else {
      const concreteObservation = await executeConcreteValidationCase({
        caseId,
        descriptor,
        compilerManifest,
        bytes: moduleBytes,
      });
      assert.deepStrictEqual(expected.outcome,
        { success: { observation: concreteObservation } },
        `${caseId} browser concrete observation disagrees with canonical ${ENGINE}`);
      concreteExecuted.push(caseId);
    }
  }

  assert.deepStrictEqual(
    concreteBlocked.map((item) => item.caseId).sort(),
    [...CONCRETE_VALIDATION_BLOCKED_CASES].sort(),
    "browser concrete validation blocker inventory drifted",
  );
  assert.ok(concreteBlocked.every((item) =>
    item.blockers.some((blocker) =>
      blocker.kind === "initial-runtime-object" &&
      blocker.objectKind === "byteArray")),
  "every browser-blocked validation case must expose the ByteArray layout boundary");
  return `PASS browser Worker Fetch shared semantic Wasm corpus ` +
    `(${matrix.selectedCases.length} semantic, ` +
    `${concreteExecuted.length} concrete, ` +
    `${concreteBlocked.length} ByteArray-blocked, ` +
    `${bundle.bundleSha256.slice(0, 12)})`;
}

try {
  globalThis.postMessage({ ok: true, result: await runValidationCorpus() });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
