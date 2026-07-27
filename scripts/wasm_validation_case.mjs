import assert from "./wasm_assert.mjs";

const SCALAR_KINDS = new Map([
  [8, "uint8"],
  [16, "uint16"],
  [32, "uint32"],
  [64, "uint64"],
]);

export const VALIDATION_PROTOCOL_VERSION = 2;

export const SEMANTIC_WASM_CONTRACT = Object.freeze({
  format: "wasm",
  target: "wasm32",
  runtimeFlavor: "fir-semantic-runtime-v1",
  abi: "fir-semantic-abi-v1",
});

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

export function semanticDatum(schema, value, host, context, validationExternals) {
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
          nat: {
            value: jsonNatural(
              validationExternals.naturalValue(host, value, context), context),
          },
        };
      case "int":
        return {
          int: {
            value: exactJsonInteger(
              validationExternals.integerValue(host, value, context), context),
          },
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
        validationExternals,
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
        validationExternals,
      ));
    }
    return { ctor: { name: ctor.name, tag: ctor.tag, fields } };
  }
  throw new Error(`${context} uses an unsupported validation schema`);
}

export function projectedEffects(
  caseId,
  projections,
  snapshots,
  validationExternals,
) {
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
      validationExternals,
    ));
    const effect = { operation: projection.operation, args };
    if (projection.resultSchema !== null) {
      effect.result = semanticDatum(
        projection.resultSchema,
        snapshot.result,
        snapshot.after,
        `${caseId} effect ${eventIndex} result`,
        validationExternals,
      );
    }
    effects.push(effect);
  }
  return effects;
}

/** Execute one compiler-produced semantic Wasm validation case in any JS host. */
export async function executeSemanticWasmCase({
  caseId,
  descriptor,
  compilerManifest,
  bytes,
  semanticRuntime,
  validationExternals,
}) {
  assert.equal(descriptor.id, caseId, `${caseId} descriptor ID mismatch`);
  assert.equal(descriptor.args.length, descriptor.argSchemas.length,
    `${caseId} argument schema/fixture arity mismatch`);
  assert.ok(Array.isArray(descriptor.effectProjections),
    `${caseId} effect projections must be an array`);

  const manifestKeys =
    ["arguments", "closureDescriptors", "closureDispatch", "entry", "fixture",
      "imports", "params", "result", "sourceEntry"];
  if (Object.hasOwn(compilerManifest, "initialRuntime")) {
    manifestKeys.push("initialRuntime");
  }
  assert.deepStrictEqual(Object.keys(compilerManifest).sort(), manifestKeys.sort(),
    `${caseId} compiler manifest shape mismatch`);
  assert.equal(compilerManifest.fixture, caseId, `${caseId} fixture mismatch`);
  assert.equal(compilerManifest.sourceEntry, descriptor.entry,
    `${caseId} source entry mismatch`);
  assert.equal(compilerManifest.entry, descriptor.entry, `${caseId} entry mismatch`);
  assert.ok(Array.isArray(compilerManifest.params), `${caseId} params must be an array`);
  assert.ok(Array.isArray(compilerManifest.closureDispatch),
    `${caseId} closureDispatch must be an array`);
  assert.equal(new Set(compilerManifest.closureDispatch).size,
    compilerManifest.closureDispatch.length,
    `${caseId} closureDispatch must not contain duplicates`);
  assert.ok(Array.isArray(compilerManifest.closureDescriptors),
    `${caseId} closureDescriptors must be an array`);
  assert.ok(compilerManifest.closureDescriptors.every((descriptor) =>
    Array.isArray(descriptor) &&
    descriptor.every((kind) => typeof kind === "string" && kind.length > 0)),
  `${caseId} closureDescriptors must contain ABI kind arrays`);
  compilerManifest.closureDescriptors.forEach((descriptor, index) =>
    assert.ok(!compilerManifest.closureDescriptors.slice(0, index).some((candidate) =>
      candidate.length === descriptor.length &&
      candidate.every((kind, kindIndex) => kind === descriptor[kindIndex])),
    `${caseId} closureDescriptors must not contain duplicates`));
  assert.ok(Array.isArray(compilerManifest.arguments),
    `${caseId} arguments must be an array`);
  assert.equal(compilerManifest.params.length, descriptor.args.length,
    `${caseId} manifest/corpus argument arity mismatch`);
  assert.equal(compilerManifest.arguments.length, descriptor.args.length,
    `${caseId} manifest invocation arity mismatch`);
  assert.ok(Array.isArray(compilerManifest.imports), `${caseId} imports must be an array`);

  const host = new semanticRuntime.SemanticHost(
    compilerManifest.initialRuntime,
    validationExternals.validationExternalRegistry,
  );
  const physicalArguments = compilerManifest.params.map((kind, index) => {
    const semanticArgument = semanticRuntime.manifestValue(
      compilerManifest.arguments[index]);
    assert.deepStrictEqual(
      semanticDatum(
        descriptor.argSchemas[index],
        semanticArgument,
        host,
        `${caseId} argument ${index}`,
        validationExternals,
      ),
      descriptor.args[index],
      `${caseId} compiler manifest disagrees with the corpus invocation`,
    );
    return host.encode(kind, semanticArgument);
  });

  assert.ok(WebAssembly.validate(bytes),
    `JavaScript engine rejected the generated WebAssembly module for ${caseId}`);
  const wasmModule = await WebAssembly.compile(bytes);
  assert.deepStrictEqual(
    WebAssembly.Module.imports(wasmModule),
    compilerManifest.imports.map((item) => ({
      module: item.module,
      name: item.name,
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
    validationExternals,
  );
  const effects = projectedEffects(
    caseId,
    descriptor.effectProjections,
    host.externalSnapshots,
    validationExternals,
  );
  return {
    termination: { returned: { value: datum } },
    stdout: "",
    stderr: "",
    effects,
  };
}
