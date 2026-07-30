import assert from "node:assert/strict";

import {
  SemanticHost,
  decodeManifestResult,
  encodeManifestArgument,
  manifestEntryName,
  validateBitExactFloatTransport,
} from "./wasm_semantic_host.mjs";

function manifest(params, result) {
  const transport = (kind) =>
    kind === "float32" ? "uint32" : kind === "float" ? "uint64" : kind;
  return {
    entry: "source",
    params,
    result,
    bitExactFloatTransport: {
      version: 1,
      encoding: "wasm-reinterpret-i32-i64",
      entry: "source_fir_bit_exact",
      params: params.map(transport),
      result: transport(result),
    },
  };
}

const f32Cases = [
  0x00000000n,
  0x80000000n,
  0x3f800000n,
  0x7f800000n,
  0xff800000n,
  0x7fc00000n,
  0x7f800001n,
  0x7fa12345n,
  0xff800001n,
  0xffffffffn,
];
const f64Cases = [
  0x0000000000000000n,
  0x8000000000000000n,
  0x3ff0000000000000n,
  0x7ff0000000000000n,
  0xfff0000000000000n,
  0x7ff8000000000000n,
  0x7ff0000000000001n,
  0x7ff123456789abcdn,
  0xfff0000000000001n,
  0xffffffffffffffffn,
];

for (const [kind, bitsCases] of [["float32", f32Cases], ["float", f64Cases]]) {
  const descriptor = manifest([kind], kind);
  const host = new SemanticHost();
  assert.equal(manifestEntryName(descriptor), "source_fir_bit_exact");
  for (const bits of bitsCases) {
    const physical = encodeManifestArgument(host, descriptor, 0, {
      kind: "scalar",
      scalarKind: kind,
      value: bits,
    });
    const actual = decodeManifestResult(host, descriptor, physical);
    assert.deepStrictEqual(actual, {
      kind: "scalar",
      scalarKind: kind,
      value: bits,
    }, `${kind} payload ${bits.toString(16)} changed in integer transport`);
  }
}

const mixed = manifest(["uint8", "float32", "usize", "float"], "uint64");
const mixedHost = new SemanticHost();
assert.equal(encodeManifestArgument(mixedHost, mixed, 0,
  { kind: "scalar", scalarKind: "uint8", value: 0xffn }), 0xff);
assert.equal(encodeManifestArgument(mixedHost, mixed, 2,
  { kind: "usize", value: 3n }), 3n);
assert.deepStrictEqual(decodeManifestResult(mixedHost, mixed, 4n),
  { kind: "scalar", scalarKind: "uint64", value: 4n });

const ordinary = { entry: "plain", params: ["uint32"], result: "uint32" };
assert.equal(validateBitExactFloatTransport(ordinary), undefined);
assert.equal(manifestEntryName(ordinary), "plain");

const valid = manifest(["float32"], "float32");
const malformed = [
  { ...valid, bitExactFloatTransport: undefined },
  { ...valid, bitExactFloatTransport: null },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, version: 2,
  } },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, encoding: "numeric-js",
  } },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, entry: "",
  } },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, entry: valid.entry,
  } },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, params: ["float32"],
  } },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, result: "float32",
  } },
  { ...valid, bitExactFloatTransport: {
    ...valid.bitExactFloatTransport, extra: true,
  } },
  {
    ...ordinary,
    bitExactFloatTransport: valid.bitExactFloatTransport,
  },
];
for (const descriptor of malformed) {
  assert.throws(() => validateBitExactFloatTransport(descriptor));
}

assert.throws(() => encodeManifestArgument(new SemanticHost(), valid, -1, {
  kind: "scalar", scalarKind: "float32", value: 0n,
}));
assert.throws(() => encodeManifestArgument(new SemanticHost(), valid, 0, {
  kind: "scalar", scalarKind: "uint32", value: 0n,
}));
assert.throws(() => encodeManifestArgument(new SemanticHost(), valid, 0, {
  kind: "scalar", scalarKind: "float32", value: -1n,
}));
assert.throws(() => encodeManifestArgument(new SemanticHost(), valid, 0, {
  kind: "scalar", scalarKind: "float32", value: 0x100000000n,
}));
assert.throws(() => decodeManifestResult(new SemanticHost(), valid, 0n));

console.log("PASS fail-closed bit-exact float manifest transport");
