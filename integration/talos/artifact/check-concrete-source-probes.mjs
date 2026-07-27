import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import {
  CONCRETE_SOURCE_PROBES,
} from "./concrete-corpus.mjs";
import {
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";
import { checkConcretePrettyFormatModule } from "./check-concrete-pretty-format-module.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

const scalar = (scalarKind, value) => Object.freeze({
  kind: "scalar",
  scalarKind,
  value: BigInt(value),
});
const usize = (value) => Object.freeze({ kind: "usize", value: BigInt(value) });
const natural = (value) => Object.freeze({ kind: "natural", value: BigInt(value) });
const string = (value) => Object.freeze({ kind: "string", value });

/**
 * Frozen execution oracles for the complete compiler-produced source inventory.
 * They deliberately describe the emitted low-level ABI, not a JavaScript facade.
 */
export const CONCRETE_SOURCE_EXPECTATIONS = Object.freeze({
  "source-nat": Object.freeze({
    mode: "invocation",
    fixture: "Fir.Validation.Corpus.Source.litNat",
    sourceEntry: "Fir.Validation.Corpus.Source.litNat",
    params: Object.freeze([]),
    result: "tobject",
    expected: natural(42),
  }),
  "source-nat-list-case": Object.freeze({
    mode: "invocation",
    fixture: "Fir.Wasm.Emit.SourceFixture.classifyNatList",
    sourceEntry: "Fir.Wasm.Emit.SourceFixture.classifyNatList",
    params: Object.freeze(["tobject"]),
    result: "uint64",
    expected: scalar("uint64", 1),
  }),
  "source-pretty-format": Object.freeze({
    mode: "invocation",
    fixture: "source-pretty-format",
    sourceEntry: "Fir.Wasm.Emit.SourceFixture.prettyFormatRaw",
    params: Object.freeze(["tobject", "tobject", "tobject", "tobject"]),
    result: "object",
    expected: string("hello\n  world"),
  }),
  "source-pretty-format-coverage": Object.freeze({
    mode: "invocation",
    fixture: "source-pretty-format-coverage",
    sourceEntry: "Fir.Wasm.Emit.SourceFixture.prettyFormatRaw",
    params: Object.freeze(["tobject", "tobject", "tobject", "tobject"]),
    result: "object",
    expected: string("α β\n. γ\n  δ\n  ε"),
  }),
  "source-pretty-format-module": Object.freeze({
    mode: "pretty-module",
    sourceEntry: "Fir.Wasm.Emit.SourceFixture.prettyFormatRaw",
    params: Object.freeze(["tobject", "tobject", "tobject", "tobject"]),
    result: "object",
  }),
  "source-string-input": Object.freeze({
    mode: "invocation",
    fixture: "Fir.Wasm.Emit.SourceFixture.acceptString",
    sourceEntry: "Fir.Wasm.Emit.SourceFixture.acceptString",
    params: Object.freeze(["object"]),
    result: "uint64",
    expected: scalar("uint64", 0xffffffffffffffffn),
  }),
  "source-uint16-id": Object.freeze({
    mode: "invocation",
    fixture: "uint16-roundtrip",
    sourceEntry: "Fir.Validation.Corpus.Source.idUInt16",
    params: Object.freeze(["uint16"]),
    result: "uint16",
    expected: scalar("uint16", 0xffffn),
  }),
  "source-uint32-id": Object.freeze({
    mode: "invocation",
    fixture: "uint32-roundtrip",
    sourceEntry: "Fir.Validation.Corpus.Source.idUInt32",
    params: Object.freeze(["uint32"]),
    result: "uint32",
    expected: scalar("uint32", 0xffffffffn),
  }),
  "source-uint64": Object.freeze({
    mode: "invocation",
    fixture: "Fir.Validation.Corpus.Source.maxUInt64",
    sourceEntry: "Fir.Validation.Corpus.Source.maxUInt64",
    params: Object.freeze([]),
    result: "uint64",
    expected: scalar("uint64", 0xffffffffffffffffn),
  }),
  "source-uint64-id": Object.freeze({
    mode: "invocation",
    fixture: "uint64-roundtrip",
    sourceEntry: "Fir.Validation.Corpus.Source.idUInt64",
    params: Object.freeze(["uint64"]),
    result: "uint64",
    expected: scalar("uint64", 0xffffffffffffffffn),
  }),
  "source-uint8-id": Object.freeze({
    mode: "invocation",
    fixture: "uint8-roundtrip",
    sourceEntry: "Fir.Validation.Corpus.Source.idUInt8",
    params: Object.freeze(["uint8"]),
    result: "uint8",
    expected: scalar("uint8", 0xffn),
  }),
  "source-usize-id": Object.freeze({
    mode: "invocation",
    fixture: "usize-roundtrip",
    sourceEntry: "Fir.Validation.Corpus.Source.idUSize",
    params: Object.freeze(["usize"]),
    result: "usize",
    expected: usize(42),
  }),
  "source-usize-id-module": Object.freeze({
    mode: "usize-module",
    sourceEntry: "Fir.Validation.Corpus.Source.idUSize",
    params: Object.freeze(["usize"]),
    result: "usize",
    argument: usize(42),
    expected: usize(42),
  }),
});

function checkInventory() {
  assert.deepStrictEqual(
    Object.keys(CONCRETE_SOURCE_EXPECTATIONS).sort(),
    [...CONCRETE_SOURCE_PROBES].sort(),
    "concrete source execution oracles disagree with the emitted source inventory",
  );
}

function checkDescriptor(id, manifest, expectation) {
  assert.equal(manifest.sourceEntry, expectation.sourceEntry,
    `${id} source entry mismatch`);
  assert.deepStrictEqual(manifest.params, expectation.params,
    `${id} parameter ABI mismatch`);
  assert.equal(manifest.result, expectation.result,
    `${id} result ABI mismatch`);
}

function checkInitialRuntime(id, host, initialRuntime) {
  if (initialRuntime === undefined) return;
  assert.ok(initialRuntime && Array.isArray(initialRuntime.heap),
    `${id} initial runtime must contain a heap`);
  for (const cell of initialRuntime.heap) {
    const address = host.locationAddresses.get(cell.location);
    assert.notEqual(address, undefined,
      `${id} initial location ${cell.location} was not loaded`);
    const header = host.readHeader(address);
    assert.equal(header.rc, cell.rc,
      `${id} initial location ${cell.location} rc mismatch`);
    assert.equal(header.persistent, cell.persistent,
      `${id} initial location ${cell.location} persistence mismatch`);
    assert.equal(header.live, cell.live,
      `${id} initial location ${cell.location} liveness mismatch`);
    assert.deepStrictEqual(host.objectJson(address, header), cell.object,
      `${id} initial location ${cell.location} object mismatch`);
  }
}

function checkResult(id, host, actual, expected) {
  if (expected.kind === "natural") {
    const value = actual.kind === "tagged"
      ? actual.payload
      : host.readNatural(host.addressOf(actual.location));
    assert.equal(value, expected.value, `${id} natural result mismatch`);
    return;
  }
  if (expected.kind === "string") {
    assert.equal(actual.kind, "heap", `${id} did not return a heap string`);
    assert.equal(host.readString(host.addressOf(actual.location)), expected.value,
      `${id} string result mismatch`);
    return;
  }
  assert.deepStrictEqual(actual, expected, `${id} concrete result mismatch`);
}

async function runInvocation(id, bytes, manifest, expectation) {
  assert.equal(manifest.fixture, expectation.fixture, `${id} fixture mismatch`);
  assert.ok(Array.isArray(manifest.arguments), `${id} invocation arguments must be an array`);
  assert.equal(manifest.arguments.length, manifest.params.length,
    `${id} invocation argument arity mismatch`);
  assert.ok(WebAssembly.validate(bytes), `${id} failed WebAssembly validation`);

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry, manifest.closureDispatch,
    manifest.closureDescriptors);
  checkInitialRuntime(id, host, manifest.initialRuntime);
  const physicalArgs = manifest.params.map((kind, index) => {
    const semantic = concreteManifestValue(manifest.arguments[index]);
    const physical = host.encode(kind, semantic);
    assert.deepStrictEqual(host.decode(kind, physical), semantic,
      `${id} argument ${index} did not round-trip through the concrete ABI`);
    return physical;
  });
  const { instance } = await WebAssembly.instantiate(
    bytes, host.imports(manifest.imports));
  const entry = instance.exports[manifest.entry];
  assert.equal(typeof entry, "function", `${id} is missing export ${manifest.entry}`);
  const result = host.decode(manifest.result, entry(...physicalArgs));
  checkResult(id, host, result, expectation.expected);
  assert.ok(!host.trace.some((event) => event.name === "panicCore" ||
    event.name === "instInhabitedOfMonad._redArg"),
  `${id} reached an unreachable prettyM fallback`);
}

async function runModule(id, bytes, manifest, expectation) {
  const host = new ConcreteHost(manifest.imports, undefined,
    concreteArtifactExternalRegistry, manifest.closureDispatch,
    manifest.closureDescriptors);
  const artifact = await instantiateModuleArtifact({ bytes, manifest, host });
  if (expectation.mode === "pretty-module") {
    checkConcretePrettyFormatModule(artifact);
    return;
  }
  const physical = host.encode(manifest.params[0], expectation.argument);
  const result = host.decode(manifest.result, artifact.entry(physical));
  checkResult(id, host, result, expectation.expected);
}

export async function checkConcreteSourceProbe({ id, bytes, manifest }) {
  const expectation = CONCRETE_SOURCE_EXPECTATIONS[id];
  assert.ok(expectation, `unknown concrete source probe ${id}`);
  checkDescriptor(id, manifest, expectation);
  if (expectation.mode === "invocation") {
    await runInvocation(id, bytes, manifest, expectation);
  } else {
    await runModule(id, bytes, manifest, expectation);
  }
  return Object.freeze({ id, mode: expectation.mode, entry: manifest.entry });
}

/**
 * Execute every compiler-produced source artifact through concrete Wasm memory.
 * The caller supplies transport only, so Node and browser Workers share this gate.
 */
export async function checkConcreteSourceInventory(load) {
  assert.equal(typeof load, "function",
    "concrete source inventory requires an artifact loader");
  checkInventory();
  const results = [];
  for (const id of CONCRETE_SOURCE_PROBES) {
    results.push(await checkConcreteSourceProbe({ id, ...await load(id) }));
  }
  return {
    results,
    message: `PASS concrete compiler source inventory ` +
      `(${results.length}/${CONCRETE_SOURCE_PROBES.length} probes)`,
  };
}
