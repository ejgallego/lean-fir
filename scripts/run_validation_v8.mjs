import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";

const CASE_ID = "uint64-max";

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
assert.deepStrictEqual(selectedCases, [CASE_ID],
  `the initial V8 adapter supports only ${CASE_ID}`);

const corpus = JSON.parse(
  await readFile(requiredEnvironment("FIR_VALIDATION_CORPUS"), "utf8"),
);
assert.equal(corpus.version, 1, "unsupported validation corpus version");
assert.ok(Array.isArray(corpus.cases), "validation corpus cases must be an array");
const descriptor = corpus.cases.find((item) => item.id === CASE_ID);
assert.ok(descriptor, `validation corpus does not contain ${CASE_ID}`);
assert.deepStrictEqual(descriptor.args, [], `${CASE_ID} must not take arguments`);
assert.deepStrictEqual(descriptor.argSchemas, [], `${CASE_ID} must not take arguments`);
assert.deepStrictEqual(descriptor.resultSchema, { bits: { width: 64 } },
  `${CASE_ID} must return UInt64 bits`);
assert.deepStrictEqual(descriptor.effectProjections, [],
  `${CASE_ID} must not project host effects`);

const products = JSON.parse(requiredEnvironment("FIR_VALIDATION_PRODUCTS"));
assert.equal(products.length, 2,
  "the V8 adapter requires a Wasm module and compiler manifest");
const manifestProduct = products.find((product) => product.kind === "wasm-manifest");
const moduleProduct = products.find((product) => product.kind === "wasm-module");
assert.ok(manifestProduct, "missing compiler manifest product");
assert.ok(moduleProduct, "missing Wasm module product");
assert.equal(manifestProduct.backend, "v8");
assert.equal(manifestProduct.name, `modules/${CASE_ID}.wasm.json`);
assert.match(manifestProduct.sha256, /^[0-9a-f]{64}$/);
assert.equal(moduleProduct.backend, "v8");
assert.equal(moduleProduct.name, `modules/${CASE_ID}.wasm`);
assert.match(moduleProduct.sha256, /^[0-9a-f]{64}$/);

const manifestBytes = await readFile(manifestProduct.path);
const consumedManifestSha256 = sha256(manifestBytes);
assert.equal(consumedManifestSha256, manifestProduct.sha256,
  "loaded compiler manifest disagrees with the captured product");
const compilerManifest = JSON.parse(manifestBytes.toString("utf8"));
assert.deepStrictEqual(compilerManifest, {
  fixture: descriptor.entry,
  sourceEntry: descriptor.entry,
  entry: descriptor.entry,
  result: "uint64",
  params: [],
  arguments: [],
  imports: [],
});

const bytes = await readFile(moduleProduct.path);
const consumedModuleSha256 = sha256(bytes);
assert.equal(consumedModuleSha256, moduleProduct.sha256,
  "loaded Wasm bytes disagree with the captured product");
assert.ok(WebAssembly.validate(bytes), "V8 rejected the generated WebAssembly module");

const wasmModule = await WebAssembly.compile(bytes);
assert.deepStrictEqual(WebAssembly.Module.imports(wasmModule), [],
  `${CASE_ID} unexpectedly requires a semantic host`);
assert.deepStrictEqual(WebAssembly.Module.exports(wasmModule), [
  { name: descriptor.entry, kind: "function" },
]);
const instance = await WebAssembly.instantiate(wasmModule, {});
const entry = instance.exports[descriptor.entry];
assert.equal(typeof entry, "function", `missing Wasm export ${descriptor.entry}`);
const physicalResult = entry();
assert.equal(typeof physicalResult, "bigint", "UInt64 must use V8's i64 lane");
const value = BigInt.asUintN(64, physicalResult).toString();

const receipt = JSON.stringify([
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
  caseId: CASE_ID,
  backend: "v8",
  diagnostics: [{ key: "validation-products", value: receipt }],
  outcome: {
    success: {
      observation: {
        termination: {
          returned: {
            value: { bits: { width: 64, value } },
          },
        },
        stdout: "",
        stderr: "",
        effects: [],
      },
    },
  },
};
console.log(JSON.stringify(result));
