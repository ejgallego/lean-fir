import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
  decodeManifestResult,
  encodeManifestArgument,
  manifestEntryName,
  validateBitExactFloatTransport,
} from "../../../scripts/wasm_semantic_host.mjs";
import {
  ConcreteFault,
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";
import {
  concreteValidationExternalRegistry,
} from "./concrete-validation-external-registry.mjs";

function scalar(kind, value) {
  return { kind: "scalar", scalarKind: kind, value: BigInt(value) };
}

const exactCases = [
  ["float32", 0x00000000n],
  ["float32", 0x80000000n],
  ["float32", 0x00000001n],
  ["float32", 0x7f7fffffn],
  ["float32", 0x7f800000n],
  ["float32", 0xff800000n],
  ["float32", 0x7fc01234n],
  ["float", 0x0000000000000000n],
  ["float", 0x8000000000000000n],
  ["float", 0x0000000000000001n],
  ["float", 0x7fefffffffffffffn],
  ["float", 0x7ff0000000000000n],
  ["float", 0xfff0000000000000n],
  ["float", 0x7ff8000000000042n],
];

for (const [kind, bits] of exactCases) {
  assert.deepStrictEqual(concreteManifestValue({
    kind: "scalar",
    scalarKind: kind,
    value: bits.toString(),
  }), scalar(kind, bits));
  const host = new ConcreteHost([]);
  const physical = host.encode(kind, scalar(kind, bits));
  assert.deepStrictEqual(host.decode(kind, physical), scalar(kind, bits));
}

const facadeCases = Object.freeze({
  float32: Object.freeze([
    0x00000000n,
    0x80000000n,
    0x7f800000n,
    0xff800000n,
    0x7fc01234n,
    0x7f800001n,
    0x7fa12345n,
    0xff800001n,
    0xffffffffn,
  ]),
  float: Object.freeze([
    0x0000000000000000n,
    0x8000000000000000n,
    0x7ff0000000000000n,
    0xfff0000000000000n,
    0x7ff8000000000042n,
    0x7ff0000000000001n,
    0x7ff123456789abcdn,
    0xfff0000000000001n,
    0xffffffffffffffffn,
  ]),
});

for (const [kind, path] of [
  ["float32", "_build/source-float32-id.wasm"],
  ["float", "_build/source-float64-id.wasm"],
]) {
  const [bytes, manifestBytes] = await Promise.all([
    readFile(path),
    readFile(`${path}.json`),
  ]);
  const manifest = JSON.parse(manifestBytes.toString("utf8"));
  const transport = validateBitExactFloatTransport(manifest);
  assert.ok(transport, `${kind} source artifact has no exact-bit transport`);
  assert.equal(transport.entry, manifestEntryName(manifest));
  assert.deepStrictEqual(transport.params,
    [kind === "float32" ? "uint32" : "uint64"]);
  assert.equal(transport.result,
    kind === "float32" ? "uint32" : "uint64");

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteValidationExternalRegistry, manifest.closureDispatch,
    manifest.closureDescriptors);
  const { instance } = await WebAssembly.instantiate(
    bytes, host.imports(manifest.imports));
  const entry = instance.exports[transport.entry];
  assert.equal(typeof entry, "function",
    `${kind} exact-bit facade is not exported`);
  for (const bits of facadeCases[kind]) {
    const physical = encodeManifestArgument(
      host, manifest, 0, scalar(kind, bits));
    assert.deepStrictEqual(
      decodeManifestResult(host, manifest, entry(physical)),
      scalar(kind, bits),
      `${kind} facade changed payload 0x${bits.toString(16)}`,
    );
  }
}

for (const malformed of [
  { kind: "scalar", scalarKind: "float32", value: 1 },
  { kind: "scalar", scalarKind: "float32", value: "-1" },
  { kind: "scalar", scalarKind: "float32", value: "+1" },
  { kind: "scalar", scalarKind: "float32", value: "01" },
  { kind: "scalar", scalarKind: "float", value: " 1" },
  { kind: "scalar", scalarKind: "float", value: "1.0" },
]) {
  assert.throws(() => concreteManifestValue(malformed),
    /must use a decimal string|must use a canonical unsigned decimal string/);
}
assert.throws(() => concreteManifestValue({
  kind: "scalar",
  scalarKind: "float32",
  value: "4294967296",
}), /out of float32 range/);
assert.throws(() => concreteManifestValue({
  kind: "scalar",
  scalarKind: "float",
  value: "18446744073709551616",
}), /out of float range/);
assert.throws(() => concreteManifestValue({
  kind: "scalar",
  scalarKind: "float64",
  value: "0",
}), /unsupported manifest scalar kind/);
{
  const host = new ConcreteHost([]);
  assert.throws(
    () => host.encode("float32", scalar("float", 0n)),
    /float does not refine float32/,
  );
  assert.throws(
    () => host.encode("float", scalar("float32", 0n)),
    /float32 does not refine float/,
  );
  assert.throws(
    () => host.decode("float32", 0n),
    /float32 must use the WebAssembly f32 lane/,
  );
  assert.throws(
    () => host.decode("float", 0n),
    /float must use the WebAssembly f64 lane/,
  );
}

for (const [kind, bits, expectedType, payloadBytes] of [
  ["float32", 0x80000000n, "Lean.Expr.const `Float32 []", 4],
  ["float", 0x7ff8000000000042n, "Lean.Expr.const `Float []", 8],
]) {
  const host = new ConcreteHost([]);
  const boxedPhysical = host.box({
    kind: "box",
    scalar: kind,
    result: "tobject",
  }, [host.encode(kind, scalar(kind, bits))]);
  const boxed = host.decode("tobject", boxedPhysical);
  assert.equal(boxed.kind, "heap", `${kind} must never use a tagged box`);
  const address = host.addressOf(boxed.location);
  const header = host.readHeader(address);
  assert.equal(header.aux1, payloadBytes);
  assert.deepStrictEqual(host.objectJson(address, header), {
    kind: "boxed",
    type: expectedType,
    value: {
      kind: "scalar",
      scalar: { kind, value: bits.toString() },
    },
  });
  const unboxed = host.unbox({ kind: "unbox", scalar: kind }, [boxedPhysical]);
  assert.deepStrictEqual(host.decode(kind, unboxed), scalar(kind, bits));
  const immediate = host.encode("tobject", { kind: "tagged", payload: 0n });
  assert.throws(
    () => host.unbox({ kind: "unbox", scalar: kind }, [immediate]),
    (error) => error instanceof ConcreteFault &&
      error.fault.kind === "expectedScalar",
  );
}

function invoke(host, declaration, params, result, args) {
  const external = host.importFunction({
    kind: "external",
    declaration,
    params,
    results: [result],
  });
  const physicalArgs = params.map((kind, index) => host.encode(kind, args[index]));
  return host.decode(result, external(...physicalArgs));
}

{
  const host = new ConcreteHost(
    [],
    undefined,
    concreteValidationExternalRegistry,
  );
  assert.deepStrictEqual(invoke(
    host,
    "Float.neg",
    ["float"],
    "float",
    [scalar("float", 0x7ff8000000000042n)],
  ), scalar("float", 0xfff8000000000042n));
  assert.deepStrictEqual(invoke(
    host,
    "Float32.neg",
    ["float32"],
    "float32",
    [scalar("float32", 0x00000000n)],
  ), scalar("float32", 0x80000000n));
  assert.deepStrictEqual(invoke(
    host,
    "Float.div",
    ["float", "float"],
    "float",
    [scalar("float", 0n), scalar("float", 0n)],
  ), scalar("float", 0x7ff8000000000000n));
  assert.deepStrictEqual(host.trace.map((event) => event.name), [
    "Float.neg",
    "Float32.neg",
    "Float.div",
  ]);
}

console.log(
  "PASS concrete bit-exact Float32/Float manifest, facade, and runtime paths");
