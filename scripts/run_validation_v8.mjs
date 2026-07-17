import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";

const ABI_CODECS = new Map([
  ["uint8", { lane: "i32", width: 8 }],
  ["uint16", { lane: "i32", width: 16 }],
  ["uint32", { lane: "i32", width: 32 }],
  ["uint64", { lane: "i64", width: 64 }],
  ["usize", { lane: "i64" }],
]);

function codecFor(kind, context) {
  const codec = ABI_CODECS.get(kind);
  assert.ok(codec, `${context} uses unsupported Wasm ABI kind ${kind}`);
  return codec;
}

function expectedSchema(codec) {
  return codec.width === undefined
    ? "usize"
    : { bits: { width: codec.width } };
}

function unsignedDecimal(value, context, width = 64) {
  assert.equal(typeof value, "string", `${context} must be a decimal string`);
  assert.match(value, /^(0|[1-9][0-9]*)$/, `${context} must be canonical decimal`);
  const parsed = BigInt(value);
  assert.ok(parsed < (1n << BigInt(width)), `${context} exceeds ${width} bits`);
  return parsed;
}

function datumValue(codec, datum, context) {
  const key = codec.width === undefined ? "usize" : "bits";
  assert.deepStrictEqual(Object.keys(datum), [key], `${context} datum kind mismatch`);
  if (codec.width !== undefined) {
    assert.equal(datum.bits.width, codec.width, `${context} datum width mismatch`);
  }
  return unsignedDecimal(datum[key].value, `${context} value`, codec.width ?? 64);
}

function expectedManifestArgument(kind, codec, value) {
  if (codec.width === undefined) {
    return { kind: "usize", value: value.toString() };
  }
  return {
    kind: "scalar",
    scalarKind: kind,
    value: value.toString(),
  };
}

function physicalArgument(kind, manifestArgument, schema, datum, context) {
  const codec = codecFor(kind, context);
  assert.deepStrictEqual(schema, expectedSchema(codec), `${context} schema mismatch`);
  const value = datumValue(codec, datum, context);
  assert.deepStrictEqual(
    manifestArgument,
    expectedManifestArgument(kind, codec, value),
    `${context} compiler manifest disagrees with the corpus invocation`,
  );
  return codec.lane === "i32"
    ? Number(BigInt.asIntN(32, value))
    : BigInt.asIntN(64, value);
}

function resultDatum(kind, schema, physicalResult, context) {
  const codec = codecFor(kind, context);
  assert.deepStrictEqual(schema, expectedSchema(codec), `${context} schema mismatch`);
  let value;
  if (codec.lane === "i32") {
    assert.equal(typeof physicalResult, "number", `${context} must use V8's i32 lane`);
    value = BigInt(physicalResult >>> 0);
  } else {
    assert.equal(typeof physicalResult, "bigint", `${context} must use V8's i64 lane`);
    value = BigInt.asUintN(64, physicalResult);
  }
  if (codec.width !== undefined) {
    assert.ok(value < (1n << BigInt(codec.width)),
      `${context} result exceeds ${codec.width} bits`);
    return { bits: { width: codec.width, value: value.toString() } };
  }
  return { usize: { value: value.toString() } };
}

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

const corpus = JSON.parse(
  await readFile(requiredEnvironment("FIR_VALIDATION_CORPUS"), "utf8"),
);
assert.equal(corpus.version, 1, "unsupported validation corpus version");
assert.ok(Array.isArray(corpus.cases), "validation corpus cases must be an array");

const buildInputManifest = JSON.parse(
  await readFile(
    `${requiredEnvironment("FIR_VALIDATION_OUT_DIR")}/build-inputs.json`,
    "utf8",
  ),
);
assert.equal(buildInputManifest.version, 1,
  "unsupported build input manifest version");
assert.equal(buildInputManifest.scope, "reported-loaded",
  "unsupported build input manifest scope");
assert.ok(Array.isArray(buildInputManifest.inputs)
  && buildInputManifest.inputs.length > 5,
  "the Lean build input manifest must report a transitive closure");
const buildInputNames = new Set(
  buildInputManifest.inputs.map((input) => input.name),
);
for (const name of [
  "bin/lean",
  "Init.olean",
  "Lean/Elab/Command.olean",
  "Fir/Validation/Corpus.olean",
  "Fir/Validation/LCNF.olean",
  "Fir/Wasm/Emit/Source.olean",
]) {
  assert.ok(buildInputNames.has(name),
    `the Lean build input manifest is missing ${name}`);
}

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
  const descriptorMatches = corpus.cases.filter((item) => item.id === caseId);
  assert.equal(descriptorMatches.length, 1,
    `validation corpus must contain exactly one ${caseId} descriptor`);
  const descriptor = descriptorMatches[0];
  assert.equal(descriptor.args.length, descriptor.argSchemas.length,
    `${caseId} argument schema/fixture arity mismatch`);
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
  assert.deepStrictEqual(Object.keys(compilerManifest).sort(),
    ["arguments", "entry", "fixture", "imports", "params", "result", "sourceEntry"],
    `${caseId} compiler manifest shape mismatch`);
  assert.equal(compilerManifest.fixture, caseId, `${caseId} fixture mismatch`);
  assert.equal(compilerManifest.sourceEntry, descriptor.entry,
    `${caseId} source entry mismatch`);
  assert.equal(compilerManifest.entry, descriptor.entry, `${caseId} entry mismatch`);
  assert.ok(Array.isArray(compilerManifest.params), `${caseId} params must be an array`);
  assert.ok(Array.isArray(compilerManifest.arguments),
    `${caseId} arguments must be an array`);
  assert.equal(compilerManifest.params.length, descriptor.args.length,
    `${caseId} manifest/corpus argument arity mismatch`);
  assert.equal(compilerManifest.arguments.length, descriptor.args.length,
    `${caseId} manifest invocation arity mismatch`);
  assert.deepStrictEqual(compilerManifest.imports, [],
    `${caseId} unexpectedly requires a semantic host`);
  const physicalArguments = compilerManifest.params.map((kind, index) =>
    physicalArgument(
      kind,
      compilerManifest.arguments[index],
      descriptor.argSchemas[index],
      descriptor.args[index],
      `${caseId} argument ${index}`,
    ));

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
  assert.equal(entry.length, compilerManifest.params.length,
    `${caseId} binary/manifest argument arity mismatch`);
  const physicalResult = entry(...physicalArguments);
  const datum = resultDatum(
    compilerManifest.result,
    descriptor.resultSchema,
    physicalResult,
    `${caseId} result`,
  );
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
