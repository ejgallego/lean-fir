import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

import {
  CONCRETE_VALIDATION_BLOCKED_CASES,
  concreteValidationBlockers,
  executeConcreteValidationCase,
} from "./concrete-validation-case.mjs";

const PROVIDER = "lean-wasm-semantic";

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function productOfKind(binding, kind) {
  const products = binding.products.filter((product) => product.kind === kind);
  assert.equal(products.length, 1,
    `${binding.caseId} must bind exactly one ${kind} product`);
  return products[0];
}

export async function checkConcreteValidationProducts(validationDirectory) {
  const matrix = JSON.parse(
    await readFile(join(validationDirectory, "matrix.json"), "utf8"));
  const corpus = JSON.parse(
    await readFile(join(validationDirectory, "corpus.json"), "utf8"));
  assert.ok(Array.isArray(matrix.selectedCases) && matrix.selectedCases.length > 0,
    "validation matrix must select cases");
  assert.equal(new Set(matrix.selectedCases).size, matrix.selectedCases.length,
    "validation matrix selects duplicate cases");
  const bundles = matrix.productBundles.filter((bundle) =>
    bundle.provider === PROVIDER);
  assert.equal(bundles.length, 1,
    `validation matrix must contain one ${PROVIDER} bundle`);
  const bundle = bundles[0];
  assert.ok(Array.isArray(bundle.cases), "semantic Wasm bundle has no case bindings");
  const bindingByCase = new Map(
    bundle.cases.map((binding) => [binding.caseId, binding]));
  assert.equal(bindingByCase.size, bundle.cases.length,
    "semantic Wasm bundle contains duplicate case bindings");
  assert.deepStrictEqual(
    [...bindingByCase.keys()].sort(),
    [...matrix.selectedCases].sort(),
    "semantic Wasm bundle cases disagree with the validation selection",
  );
  const descriptorByCase = new Map(
    corpus.cases.map((descriptor) => [descriptor.id, descriptor]));
  assert.equal(descriptorByCase.size, corpus.cases.length,
    "validation corpus contains duplicate descriptors");

  const executed = [];
  const blocked = [];
  for (const caseId of matrix.selectedCases) {
    const binding = bindingByCase.get(caseId);
    const descriptor = descriptorByCase.get(caseId);
    assert.ok(binding, `missing product binding for ${caseId}`);
    assert.ok(descriptor, `missing validation descriptor for ${caseId}`);
    const manifestProduct = productOfKind(binding, "wasm-manifest");
    const moduleProduct = productOfKind(binding, "wasm-module");
    const manifestBytes = await readFile(
      join(validationDirectory, PROVIDER, manifestProduct.name));
    const moduleBytes = await readFile(
      join(validationDirectory, PROVIDER, moduleProduct.name));
    assert.equal(sha256(manifestBytes), manifestProduct.sha256,
      `${caseId} concrete manifest digest mismatch`);
    assert.equal(sha256(moduleBytes), moduleProduct.sha256,
      `${caseId} concrete module digest mismatch`);
    const compilerManifest = JSON.parse(manifestBytes.toString("utf8"));
    const blockers = concreteValidationBlockers(compilerManifest);
    if (blockers.length > 0) {
      blocked.push({ caseId, blockers });
      continue;
    }
    let observation;
    try {
      observation = await executeConcreteValidationCase({
        caseId,
        descriptor,
        compilerManifest,
        bytes: moduleBytes,
      });
    } catch (error) {
      error.message = `${caseId}: ${error.message}`;
      throw error;
    }
    const expected = JSON.parse(await readFile(
      join(validationDirectory, caseId, "v8", "result.json"), "utf8"));
    assert.equal(expected.caseId, caseId, `${caseId} canonical result case mismatch`);
    assert.equal(expected.backend, "v8", `${caseId} canonical result backend mismatch`);
    assert.deepStrictEqual(expected.outcome, { success: { observation } },
      `${caseId} concrete observation disagrees with canonical V8`);
    executed.push(caseId);
  }

  assert.deepStrictEqual(
    blocked.map((item) => item.caseId).sort(),
    [...CONCRETE_VALIDATION_BLOCKED_CASES].sort(),
    "concrete validation blocker inventory drifted",
  );
  assert.ok(blocked.every((item) =>
    item.blockers.some((blocker) =>
      blocker.kind === "initial-runtime-object" &&
      blocker.objectKind === "byteArray")),
  "every blocked validation case must expose the ByteArray layout boundary");
  return {
    executed,
    blocked,
    bundleSha256: bundle.bundleSha256,
    message: `PASS concrete shared validation products ` +
      `(${executed.length}/${matrix.selectedCases.length} executed, ` +
      `${blocked.length} ByteArray-blocked)`,
  };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const validationDirectory = process.argv[2];
  if (!validationDirectory) {
    throw new Error(
      "usage: node check-concrete-validation-products.mjs VALIDATION_DIRECTORY");
  }
  const result = await checkConcreteValidationProducts(validationDirectory);
  console.log(result.message);
}
