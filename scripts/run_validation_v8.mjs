import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { pathToFileURL } from "node:url";

const semanticHostPath = process.argv[2];
const validationExternalsPath = process.argv[3];
assert.ok(semanticHostPath && validationExternalsPath,
  "usage: node run_validation_v8.mjs <semantic-host> <validation-externals>");
const { SemanticHost, manifestValue } = await import(pathToFileURL(semanticHostPath).href);
const {
  byteArrayValue,
  integerValue,
  naturalValue,
  validationExternalRegistry,
} = await import(pathToFileURL(validationExternalsPath).href);

const SCALAR_KINDS = new Map([
  [8, "uint8"],
  [16, "uint16"],
  [32, "uint32"],
  [64, "uint64"],
]);

const PROTOCOL_VERSION = 2;
const SEMANTIC_WASM_CONTRACT = {
  format: "wasm",
  target: "wasm32",
  runtimeFlavor: "fir-semantic-runtime-v1",
  abi: "fir-semantic-abi-v1",
};

function jsonNatural(value, context) {
  assert.ok(value >= 0n, `${context} must be nonnegative`);
  return value.toString();
}

function exactJsonInteger(value, context) {
  const result = Number(value);
  assert.ok(Number.isSafeInteger(result) && BigInt(result) === value,
    `${context} cannot be represented exactly by the validation JSON protocol`);
  return result;
}

function semanticDatum(schema, value, host, context) {
  if (typeof schema === "string") {
    switch (schema) {
      case "unit":
        assert.deepStrictEqual(value, { kind: "tagged", payload: 0n },
          `${context} must be the unit constructor`);
        return { unit: {} };
      case "bool":
        if (value.kind === "tagged") {
          assert.ok(value.payload === 0n || value.payload === 1n,
            `${context} boolean tag is out of range`);
          return { bool: { value: value.payload === 1n } };
        }
        assert.equal(value.kind, "scalar", `${context} must be a tagged or scalar boolean`);
        assert.equal(value.scalarKind, "uint8", `${context} scalar boolean must use uint8`);
        assert.ok(value.value === 0n || value.value === 1n,
          `${context} scalar boolean is out of range`);
        return { bool: { value: value.value === 1n } };
      case "nat":
        return {
          nat: { value: jsonNatural(naturalValue(host, value, context), context) },
        };
      case "int":
        return {
          int: { value: exactJsonInteger(integerValue(host, value, context), context) },
        };
      case "string": {
        assert.equal(value.kind, "heap", `${context} must be a heap string`);
        const object = host.liveCell(value.location).object;
        assert.equal(object.kind, "string", `${context} heap object must be a string`);
        return { string: { value: object.value } };
      }
      case "bytes": {
        assert.equal(value.kind, "heap", `${context} must be a heap byte array`);
        const object = host.liveCell(value.location).object;
        assert.equal(object.kind, "byteArray", `${context} heap object must be a byte array`);
        return { bytes: { value: [...object.value] } };
      }
      case "usize":
        assert.equal(value.kind, "usize", `${context} must be a usize value`);
        return { usize: { value: value.value.toString() } };
      default:
        throw new Error(`${context} uses unsupported validation schema ${schema}`);
    }
  }

  assert.ok(schema && typeof schema === "object", `${context} schema must be an object`);
  if (schema.bits !== undefined) {
    const width = schema.bits.width;
    const scalarKind = SCALAR_KINDS.get(width);
    assert.ok(scalarKind, `${context} uses unsupported scalar width ${width}`);
    assert.equal(value.kind, "scalar", `${context} must be a scalar value`);
    assert.equal(value.scalarKind, scalarKind, `${context} scalar kind mismatch`);
    assert.ok(value.value >= 0n && value.value < (1n << BigInt(width)),
      `${context} scalar value is out of range`);
    return { bits: { width, value: value.value.toString() } };
  }
  if (schema.seq !== undefined) {
    const elements = [];
    const locations = new Set();
    let cursor = value;
    while (cursor.kind !== "tagged" || cursor.payload !== 0n) {
      assert.equal(cursor.kind, "heap", `${context} list tail must be nil or a heap constructor`);
      assert.ok(!locations.has(cursor.location), `${context} list contains a cycle`);
      locations.add(cursor.location);
      const object = host.liveCell(cursor.location).object;
      assert.equal(object.kind, "ctor", `${context} list cell must be a constructor`);
      assert.equal(object.tag, 1n, `${context} list cell must use the cons tag`);
      assert.equal(object.objectFields.length, 2, `${context} list cell must have two fields`);
      assert.equal(object.usizeFields.length, 0, `${context} list cell has usize fields`);
      assert.equal(object.scalarFields.length, 0, `${context} list cell has scalar fields`);
      elements.push(semanticDatum(
        schema.seq.element,
        object.objectFields[0],
        host,
        `${context} element ${elements.length}`,
      ));
      cursor = object.objectFields[1];
    }
    return { seq: { value: elements } };
  }
  if (schema.ctor !== undefined) {
    const ctor = schema.ctor;
    const tag = BigInt(ctor.tag);
    let fields;
    if (value.kind === "tagged") {
      assert.equal(value.payload, tag, `${context} constructor tag mismatch`);
      assert.equal(ctor.fields.length, 0, `${context} tagged constructor has fields`);
      fields = [];
    } else {
      assert.equal(value.kind, "heap", `${context} must be a constructor value`);
      const object = host.liveCell(value.location).object;
      assert.equal(object.kind, "ctor", `${context} heap object must be a constructor`);
      assert.equal(object.tag, tag, `${context} constructor tag mismatch`);
      assert.equal(object.objectFields.length, ctor.fields.length,
        `${context} constructor field arity mismatch`);
      assert.equal(object.usizeFields.length, 0, `${context} constructor has usize fields`);
      assert.equal(object.scalarFields.length, 0, `${context} constructor has scalar fields`);
      fields = ctor.fields.map((fieldSchema, index) => semanticDatum(
        fieldSchema,
        object.objectFields[index],
        host,
        `${context} field ${index}`,
      ));
    }
    return { ctor: { name: ctor.name, tag: ctor.tag, fields } };
  }
  throw new Error(`${context} uses an unsupported validation schema`);
}

function projectedEffects(caseId, projections, snapshots) {
  const byExternal = new Map();
  for (const projection of projections) {
    assert.equal(typeof projection.external, "string",
      `${caseId} effect projection external must be a string`);
    assert.equal(typeof projection.operation, "string",
      `${caseId} effect projection operation must be a string`);
    assert.ok(Array.isArray(projection.argSchemas),
      `${caseId} effect projection argument schemas must be an array`);
    assert.ok(!byExternal.has(projection.external),
      `${caseId} has duplicate effect projection ${projection.external}`);
    byExternal.set(projection.external, projection);
  }

  const effects = [];
  for (const [eventIndex, snapshot] of snapshots.entries()) {
    const projection = byExternal.get(snapshot.name);
    if (projection === undefined) {
      continue;
    }
    assert.equal(snapshot.args.length, projection.argSchemas.length,
      `${caseId} projected external ${snapshot.name} argument arity mismatch`);
    const args = projection.argSchemas.map((schema, index) => semanticDatum(
      schema,
      snapshot.args[index],
      snapshot.before,
      `${caseId} effect ${eventIndex} argument ${index}`,
    ));
    const effect = { operation: projection.operation, args };
    if (projection.resultSchema !== null) {
      effect.result = semanticDatum(
        projection.resultSchema,
        snapshot.result,
        snapshot.after,
        `${caseId} effect ${eventIndex} result`,
      );
    }
    effects.push(effect);
  }
  return effects;
}

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

const selectedCases = JSON.parse(requiredEnvironment("FIR_VALIDATION_CASES"));
assert.ok(Array.isArray(selectedCases) && selectedCases.length > 0,
  "the V8 adapter selection must be a nonempty array");
assert.equal(new Set(selectedCases).size, selectedCases.length,
  "the V8 adapter selection contains duplicates");

const corpus = JSON.parse(
  await readFile(requiredEnvironment("FIR_VALIDATION_CORPUS"), "utf8"),
);
assert.equal(corpus.version, PROTOCOL_VERSION, "unsupported validation corpus version");
assert.ok(Array.isArray(corpus.cases), "validation corpus cases must be an array");

const products = JSON.parse(requiredEnvironment("FIR_VALIDATION_PRODUCTS"));
assert.ok(Array.isArray(products) && products.length > 0,
  "the V8 adapter requires a nonempty provider product inventory");

const productBundle = JSON.parse(
  requiredEnvironment("FIR_VALIDATION_PRODUCT_BUNDLE"),
);
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
  const manifestKeys =
    ["arguments", "entry", "fixture", "imports", "params", "result", "sourceEntry"];
  if (Object.hasOwn(compilerManifest, "initialRuntime")) {
    manifestKeys.push("initialRuntime");
  }
  assert.deepStrictEqual(Object.keys(compilerManifest).sort(),
    manifestKeys.sort(),
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
  assert.ok(Array.isArray(compilerManifest.imports), `${caseId} imports must be an array`);
  const host = new SemanticHost(compilerManifest.initialRuntime, validationExternalRegistry);
  const physicalArguments = compilerManifest.params.map((kind, index) => {
    const semanticArgument = manifestValue(compilerManifest.arguments[index]);
    assert.deepStrictEqual(
      semanticDatum(
        descriptor.argSchemas[index],
        semanticArgument,
        host,
        `${caseId} argument ${index}`,
      ),
      descriptor.args[index],
      `${caseId} compiler manifest disagrees with the corpus invocation`,
    );
    return host.encode(kind, semanticArgument);
  });

  const bytes = await readFile(moduleProduct.path);
  const consumedModuleSha256 = sha256(bytes);
  assert.equal(consumedModuleSha256, moduleProduct.sha256,
    `loaded Wasm bytes for ${caseId} disagree with the captured product`);
  assert.ok(WebAssembly.validate(bytes),
    `V8 rejected the generated WebAssembly module for ${caseId}`);
  const wasmModule = await WebAssembly.compile(bytes);
  assert.deepStrictEqual(
    WebAssembly.Module.imports(wasmModule),
    compilerManifest.imports.map((descriptor) => ({
      module: descriptor.module,
      name: descriptor.name,
      kind: "function",
    })),
    `${caseId} binary/manifest import mismatch`,
  );
  const moduleExports = WebAssembly.Module.exports(wasmModule);
  assert.ok(moduleExports.every((item) => item.kind === "function"),
    `${caseId} binary exports a non-function ABI object`);
  assert.deepStrictEqual(
    moduleExports.filter((item) => item.name === descriptor.entry),
    [{ name: descriptor.entry, kind: "function" }],
    `${caseId} binary must export its selected entry exactly once`,
  );
  const instance = await WebAssembly.instantiate(
    wasmModule,
    host.imports(compilerManifest.imports),
  );
  const entry = instance.exports[descriptor.entry];
  assert.equal(typeof entry, "function", `missing Wasm export ${descriptor.entry}`);
  assert.equal(entry.length, compilerManifest.params.length,
    `${caseId} binary/manifest argument arity mismatch`);
  const physicalResult = entry(...physicalArguments);
  const datum = semanticDatum(
    descriptor.resultSchema,
    host.decode(compilerManifest.result, physicalResult),
    host,
    `${caseId} result`,
  );
  const effects = projectedEffects(
    caseId,
    descriptor.effectProjections,
    host.externalSnapshots,
  );
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
      success: {
        observation: {
          termination: {
            returned: { value: datum },
          },
          stdout: "",
          stderr: "",
          effects,
        },
      },
    },
  };
  console.log(JSON.stringify(result));
}
