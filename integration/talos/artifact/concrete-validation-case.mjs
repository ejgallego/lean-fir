import assert from "../../../scripts/wasm_assert.mjs";
import {
  decodeManifestResult,
  encodeManifestArgument,
  manifestEntryName,
  validateBitExactFloatTransport,
} from "../../../scripts/wasm_semantic_host.mjs";
import {
  semanticDatum,
} from "../../../scripts/wasm_validation_case.mjs";
import * as validationExternals from "../../../scripts/wasm_validation_externals.mjs";

import {
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";
import {
  concreteValidationExternalRegistry,
} from "./concrete-validation-external-registry.mjs";

const SUPPORTED_INITIAL_OBJECTS = new Set([
  "ctor",
  "integer",
  "natural",
  "string",
]);

export const CONCRETE_VALIDATION_BLOCKED_CASES = Object.freeze([
  "aliased-byte-array-child-copy-on-write",
  "aliased-byte-array-self-replace",
  "aliased-byte-array-self-replace-child-copy-on-write",
  "aliased-byte-array-shared-first",
  "aliased-byte-array-shared-self-replace",
  "aliased-byte-array-update-first",
  "aliased-byte-array-update-second",
  "byte-array-get-empty",
  "byte-array-get-end",
  "byte-array-get-heap-oob",
  "byte-array-get-high-bit",
  "byte-array-get-max",
  "byte-array-get-zero",
  "byte-array-object-swap-shared",
  "byte-array-object-swap-unique",
  "byte-array-roundtrip",
  "byte-array-set-shared",
  "byte-array-set-unique",
  "byte-array-size",
  "captured-byte-array-outside-alias-mutation",
  "captured-byte-array-outside-alias-read",
  "conditional-byte-array-get-skipped",
  "conditional-byte-array-get-taken",
  "effect-record-byte-array-twice",
  "empty-byte-array-roundtrip",
  "mixed-closure-capture-once",
  "mixed-closure-capture-thrice",
  "mixed-closure-capture-twice",
  "mixed-closure-capture-zero",
  "mixed-layout-byte-array",
  "mixed-layout-natural",
  "mixed-layout-string",
  "mixed-layout-uint32",
  "mixed-layout-usize",
  "multi-object-shared-first-original",
  "multi-object-shared-first-updated",
  "multi-object-update-first-preserves-last",
  "multi-object-update-last-preserves-middle",
  "multi-object-update-middle-preserves-first",
]);

function decodedValueJson(value) {
  switch (value.kind) {
    case "object":
      if (value.reference.kind === "tagged") {
        return { kind: "tagged", payload: BigInt(value.reference.payload) };
      }
      assert.equal(value.reference.kind, "heap",
        "concrete object JSON has an unknown reference kind");
      return { kind: "heap", location: value.reference.location };
    case "usize":
      return { kind: "usize", value: BigInt(value.value) };
    case "scalar":
      return {
        kind: "scalar",
        scalarKind: value.scalar.kind,
        value: BigInt(value.scalar.value),
      };
    case "erased":
      return { kind: "erased" };
    case "reuseToken":
      return { kind: "reuseToken", location: value.location };
    default:
      throw new Error(`unsupported concrete observed value kind ${value.kind}`);
  }
}

function semanticObject(host, location) {
  const address = host.addressOf(location);
  const header = host.readHeader(address);
  const object = host.objectJson(address, header);
  switch (object.kind) {
    case "ctor":
      return {
        kind: "ctor",
        tag: BigInt(object.tag),
        objectFields: object.objectFields.map(decodedValueJson),
        usizeFields: object.usizeFields.map(BigInt),
        scalarFields: object.scalarFields.map((field) => ({
          width: field.width,
          offset: field.offset,
          value: {
            kind: "scalar",
            scalarKind: field.value.kind,
            value: BigInt(field.value.value),
          },
        })),
      };
    case "natural":
      return { kind: "natural", value: BigInt(object.value) };
    case "integer":
      return { kind: "integer", value: BigInt(object.value) };
    case "string":
      return { kind: "string", value: object.value };
    default:
      throw new Error(`unsupported concrete validation object kind ${object.kind}`);
  }
}

function semanticHeapView(host) {
  return {
    liveCell(location) {
      return {
        location,
        live: true,
        object: semanticObject(host, location),
      };
    },
  };
}

function manifestShape(caseId, manifest) {
  const keys =
    ["arguments", "closureDescriptors", "closureDispatch", "entry", "fixture",
      "imports", "params", "result", "sourceEntry"];
  if (Object.hasOwn(manifest, "initialRuntime")) keys.push("initialRuntime");
  if (Object.hasOwn(manifest, "bitExactFloatTransport")) {
    keys.push("bitExactFloatTransport");
  }
  assert.deepStrictEqual(Object.keys(manifest).sort(), keys.sort(),
    `${caseId} compiler manifest shape mismatch`);
  validateBitExactFloatTransport(manifest);
}

export function concreteValidationBlockers(manifest) {
  const blockers = [];
  const objectKinds = new Set(
    (manifest.initialRuntime?.heap ?? []).map((cell) => cell.object.kind));
  for (const objectKind of [...objectKinds].sort()) {
    if (!SUPPORTED_INITIAL_OBJECTS.has(objectKind)) {
      blockers.push({ kind: "initial-runtime-object", objectKind });
    }
  }
  const declarations = new Set(manifest.imports
    .filter((item) => item.operation.kind === "external")
    .map((item) => item.operation.declaration)
    .filter((declaration) =>
      !Object.hasOwn(concreteValidationExternalRegistry, declaration)));
  for (const declaration of [...declarations].sort()) {
    blockers.push({ kind: "external-declaration", declaration });
  }
  return blockers;
}

/** Execute one validation product through the concrete wasm32 memory host. */
export async function executeConcreteValidationCase({
  caseId,
  descriptor,
  compilerManifest,
  bytes,
}) {
  assert.equal(descriptor.id, caseId, `${caseId} descriptor ID mismatch`);
  assert.equal(compilerManifest.fixture, caseId, `${caseId} fixture mismatch`);
  assert.equal(compilerManifest.sourceEntry, descriptor.entry,
    `${caseId} source entry mismatch`);
  assert.equal(compilerManifest.entry, descriptor.entry,
    `${caseId} exported entry mismatch`);
  assert.equal(descriptor.args.length, descriptor.argSchemas.length,
    `${caseId} argument schema/fixture arity mismatch`);
  assert.ok(Array.isArray(descriptor.effectProjections),
    `${caseId} effect projections must be an array`);
  manifestShape(caseId, compilerManifest);
  assert.deepStrictEqual(concreteValidationBlockers(compilerManifest), [],
    `${caseId} cannot cross the concrete validation gate`);

  const host = new ConcreteHost(
    compilerManifest.imports,
    compilerManifest.initialRuntime,
    concreteValidationExternalRegistry,
    compilerManifest.closureDispatch,
    compilerManifest.closureDescriptors,
  );
  const heapView = semanticHeapView(host);
  assert.equal(compilerManifest.params.length, descriptor.args.length,
    `${caseId} manifest/corpus argument arity mismatch`);
  assert.equal(compilerManifest.arguments.length, descriptor.args.length,
    `${caseId} manifest invocation arity mismatch`);
  const physicalArguments = compilerManifest.params.map((_kind, index) => {
    const semanticArgument = concreteManifestValue(
      compilerManifest.arguments[index]);
    assert.deepStrictEqual(
      semanticDatum(
        descriptor.argSchemas[index],
        semanticArgument,
        heapView,
        `${caseId} argument ${index}`,
        validationExternals,
      ),
      descriptor.args[index],
      `${caseId} concrete manifest disagrees with the corpus invocation`,
    );
    return encodeManifestArgument(
      host, compilerManifest, index, semanticArgument);
  });

  assert.ok(WebAssembly.validate(bytes),
    `JavaScript engine rejected concrete WebAssembly module ${caseId}`);
  const wasmModule = await WebAssembly.compile(bytes);
  assert.deepStrictEqual(
    WebAssembly.Module.imports(wasmModule),
    compilerManifest.imports.map((item) => ({
      module: item.module,
      name: item.name,
      kind: "function",
    })),
    `${caseId} concrete binary/manifest import mismatch`,
  );
  assert.deepStrictEqual(
    WebAssembly.Module.exports(wasmModule)
      .filter((item) => item.name === descriptor.entry),
    [{ name: descriptor.entry, kind: "function" }],
    `${caseId} concrete binary must export its selected entry exactly once`,
  );
  const entryName = manifestEntryName(compilerManifest);
  if (entryName !== descriptor.entry) {
    assert.deepStrictEqual(
      WebAssembly.Module.exports(wasmModule)
        .filter((item) => item.name === entryName),
      [{ name: entryName, kind: "function" }],
      `${caseId} concrete binary must export its float facade exactly once`,
    );
  }
  const instance = await WebAssembly.instantiate(
    wasmModule,
    host.imports(compilerManifest.imports),
  );
  const entry = instance.exports[entryName];
  assert.equal(typeof entry, "function", `missing concrete Wasm export ${entryName}`);
  assert.equal(entry.length, compilerManifest.params.length,
    `${caseId} concrete binary/manifest argument arity mismatch`);
  const result = decodeManifestResult(
    host, compilerManifest, entry(...physicalArguments));
  const datum = semanticDatum(
    descriptor.resultSchema,
    result,
    heapView,
    `${caseId} concrete result`,
    validationExternals,
  );
  const projectedNames = new Set(
    descriptor.effectProjections.map((projection) => projection.external));
  const projectedCalls = host.trace.filter((event) => projectedNames.has(event.name));
  const effects = host.validationEffects ?? [];
  assert.equal(effects.length, projectedCalls.length,
    `${caseId} concrete effect projection count mismatch`);
  return {
    termination: { returned: { value: datum } },
    stdout: "",
    stderr: "",
    effects,
  };
}
