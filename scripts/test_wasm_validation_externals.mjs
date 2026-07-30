import assert from "node:assert/strict";

import { formatExternalRegistry } from "./wasm_format_externals.mjs";
import {
  manifestValue,
  SemanticHost,
} from "./wasm_semantic_host.mjs";
import { semanticDatum } from "./wasm_validation_case.mjs";
import * as validationExternals from "./wasm_validation_externals.mjs";
import {
  integerValue,
  naturalValue,
  scalarUInt8,
  scalarUInt16,
  scalarUInt32,
  scalarUInt64,
  semanticUSize,
  validationExternalRegistry,
} from "./wasm_validation_externals.mjs";

const append = validationExternalRegistry["String.Internal.append"];
const pushn = validationExternalRegistry["String.Internal.pushn"];
const decEq = validationExternalRegistry["String.decEq"];
const decLt = validationExternalRegistry["String.decidableLT"];
const compare = validationExternalRegistry["String.compare"];
const natMul = validationExternalRegistry["Nat.mul"];
const natDiv = validationExternalRegistry["Nat.div"];
const natMod = validationExternalRegistry["Nat.mod"];
const natLand = validationExternalRegistry["Nat.land"];
const natLor = validationExternalRegistry["Nat.lor"];
const natXor = validationExternalRegistry["Nat.xor"];
const natShiftLeft = validationExternalRegistry["Nat.shiftLeft"];
const natShiftRight = validationExternalRegistry["Nat.shiftRight"];
const intMul = validationExternalRegistry["Int.mul"];
const intEDiv = validationExternalRegistry["Int.ediv"];
const intEMod = validationExternalRegistry["Int.emod"];
const intShiftLeft = validationExternalRegistry["Int.shiftLeft"];
const intShiftRight = validationExternalRegistry["Int.shiftRight"];
const intDecEq = validationExternalRegistry["Int.decEq"];
const intDecLt = validationExternalRegistry["Int.decLt"];
const intDecLe = validationExternalRegistry["Int.decLe"];
const fixedWidthSuffixes = [
  "add",
  "sub",
  "mul",
  "div",
  "mod",
  "land",
  "lor",
  "xor",
  "shiftLeft",
  "shiftRight",
  "complement",
  "neg",
  "decEq",
  "decLt",
  "decLe",
];
const fixedWidthFamilies = [
  {
    typeName: "UInt8",
    width: 8,
    decode: scalarUInt8,
    encode: value => fixedWidthScalarValue("uint8", value),
    wrongValue: fixedWidthScalarValue("uint16", 1n),
  },
  {
    typeName: "UInt16",
    width: 16,
    decode: scalarUInt16,
    encode: value => fixedWidthScalarValue("uint16", value),
    wrongValue: fixedWidthScalarValue("uint8", 1n),
  },
  {
    typeName: "UInt32",
    width: 32,
    decode: scalarUInt32,
    encode: value => fixedWidthScalarValue("uint32", value),
    wrongValue: fixedWidthScalarValue("uint8", 1n),
  },
  {
    typeName: "UInt64",
    width: 64,
    decode: scalarUInt64,
    encode: value => fixedWidthScalarValue("uint64", value),
    wrongValue: fixedWidthScalarValue("uint8", 1n),
  },
  {
    typeName: "USize",
    width: 64,
    decode: semanticUSize,
    encode: value => ({ kind: "usize", value: BigInt(value) }),
    wrongValue: fixedWidthScalarValue("uint64", 1n),
  },
];
const signedFixedWidthSuffixes = [...fixedWidthSuffixes, "abs"];
const signedFixedWidthFamilies = [
  {
    typeName: "Int8",
    width: 8,
    decode: (value, context) =>
      BigInt.asIntN(8, scalarUInt8(value, context)),
    encode: value =>
      fixedWidthScalarValue("uint8", BigInt.asUintN(8, value)),
    wrongValue: fixedWidthScalarValue("uint16", 1n),
  },
  {
    typeName: "Int16",
    width: 16,
    decode: (value, context) =>
      BigInt.asIntN(16, scalarUInt16(value, context)),
    encode: value =>
      fixedWidthScalarValue("uint16", BigInt.asUintN(16, value)),
    wrongValue: fixedWidthScalarValue("uint8", 1n),
  },
  {
    typeName: "Int32",
    width: 32,
    decode: (value, context) =>
      BigInt.asIntN(32, scalarUInt32(value, context)),
    encode: value =>
      fixedWidthScalarValue("uint32", BigInt.asUintN(32, value)),
    wrongValue: fixedWidthScalarValue("uint8", 1n),
  },
  {
    typeName: "Int64",
    width: 64,
    decode: (value, context) =>
      BigInt.asIntN(64, scalarUInt64(value, context)),
    encode: value =>
      fixedWidthScalarValue("uint64", BigInt.asUintN(64, value)),
    wrongValue: fixedWidthScalarValue("uint8", 1n),
  },
  {
    typeName: "ISize",
    width: 64,
    decode: (value, context) =>
      BigInt.asIntN(64, semanticUSize(value, context)),
    encode: value => ({
      kind: "usize",
      value: BigInt.asUintN(64, value),
    }),
    wrongValue: fixedWidthScalarValue("uint64", 1n),
  },
];

assert.strictEqual(formatExternalRegistry["String.Internal.append"], append);
assert.strictEqual(formatExternalRegistry["String.Internal.pushn"], pushn);
assert.strictEqual(formatExternalRegistry["String.decEq"], decEq);
assert.strictEqual(formatExternalRegistry["String.decidableLT"], decLt);
assert.strictEqual(formatExternalRegistry["String.compare"], compare);
assert.strictEqual(formatExternalRegistry["Nat.mul"], natMul);
assert.strictEqual(formatExternalRegistry["Nat.div"], natDiv);
assert.strictEqual(formatExternalRegistry["Nat.mod"], natMod);
assert.strictEqual(formatExternalRegistry["Nat.land"], natLand);
assert.strictEqual(formatExternalRegistry["Nat.lor"], natLor);
assert.strictEqual(formatExternalRegistry["Nat.xor"], natXor);
assert.strictEqual(formatExternalRegistry["Nat.shiftLeft"], natShiftLeft);
assert.strictEqual(formatExternalRegistry["Nat.shiftRight"], natShiftRight);
assert.strictEqual(formatExternalRegistry["Int.mul"], intMul);
assert.strictEqual(formatExternalRegistry["Int.ediv"], intEDiv);
assert.strictEqual(formatExternalRegistry["Int.emod"], intEMod);
assert.strictEqual(formatExternalRegistry["Int.shiftLeft"], intShiftLeft);
assert.strictEqual(formatExternalRegistry["Int.shiftRight"], intShiftRight);
assert.strictEqual(formatExternalRegistry["Int.decEq"], intDecEq);
assert.strictEqual(formatExternalRegistry["Int.decLt"], intDecLt);
assert.strictEqual(formatExternalRegistry["Int.decLe"], intDecLe);
for (const { typeName } of fixedWidthFamilies) {
  for (const suffix of fixedWidthSuffixes) {
    const declaration = `${typeName}.${suffix}`;
    assert.strictEqual(
      formatExternalRegistry[declaration],
      validationExternalRegistry[declaration]);
  }
}
for (const { typeName } of signedFixedWidthFamilies) {
  for (const suffix of signedFixedWidthSuffixes) {
    const declaration = `${typeName}.${suffix}`;
    assert.strictEqual(
      formatExternalRegistry[declaration],
      validationExternalRegistry[declaration]);
  }
  for (const suffix of ["ofNat", "ofInt", "toInt"]) {
    const declaration = `${typeName}.${suffix}`;
    assert.strictEqual(
      formatExternalRegistry[declaration],
      validationExternalRegistry[declaration]);
  }
}

function invoke(handler, host, args) {
  const beforeWorld = host.world;
  const response = handler({ args, host, world: beforeWorld });
  assert.equal(response.world, beforeWorld);
  assert.equal(host.world, beforeWorld);
  return response.value;
}

function stringCell(host, reference) {
  assert.equal(reference.kind, "heap");
  const cell = host.liveCell(reference.location);
  assert.equal(cell.object.kind, "string");
  return cell;
}

function snapshot(cell) {
  return {
    location: cell.location,
    rc: cell.rc,
    persistent: cell.persistent,
    live: cell.live,
    object: { ...cell.object },
  };
}

function character(codePoint) {
  return { kind: "scalar", scalarKind: "uint32", value: BigInt(codePoint) };
}

function fixedWidthScalarValue(scalarKind, value) {
  return { kind: "scalar", scalarKind, value: BigInt(value) };
}

{
  const float32 = fixedWidthScalarValue("float32", 0x7fc12345n);
  const float64 = fixedWidthScalarValue("float", 0x7ff8123456789abcn);
  assert.deepStrictEqual(manifestValue({
    kind: "scalar",
    scalarKind: "float32",
    value: "2143363909",
  }), float32);
  assert.deepStrictEqual(manifestValue({
    kind: "scalar",
    scalarKind: "float",
    value: "9221140253039434428",
  }), float64);
  for (const value of [
    0,
    -1,
    "-1",
    "+1",
    "01",
    "0x1",
    "1.0",
    "4294967296",
  ]) {
    assert.throws(() => manifestValue({
      kind: "scalar",
      scalarKind: "float32",
      value,
    }));
  }
  assert.throws(() => manifestValue({
    kind: "scalar",
    scalarKind: "float",
    value: "18446744073709551616",
  }));
  assert.throws(() => manifestValue({
    kind: "scalar",
    scalarKind: "float64",
    value: "0",
  }));

  const host = new SemanticHost();
  for (const [kind, bits] of [
    ["float32", 0x00000000n],
    ["float32", 0x80000000n],
    ["float32", 0x7f800000n],
    ["float32", 0xff800000n],
    ["float32", 0x7fc12345n],
    ["float", 0x0000000000000000n],
    ["float", 0x8000000000000000n],
    ["float", 0x7ff0000000000000n],
    ["float", 0xfff0000000000000n],
    ["float", 0x7ff8123456789abcn],
  ]) {
    const semantic = fixedWidthScalarValue(kind, bits);
    assert.deepStrictEqual(
      host.decode(kind, host.encode(kind, semantic)),
      semantic,
      `${kind} physical lane changed raw bits ${bits}`,
    );
  }

  for (const [kind, bits] of [
    ["float32", 0n],
    ["float32", 0x7fc12345n],
    ["float", 0n],
    ["float", 0x7ff8123456789abcn],
  ]) {
    const semantic = fixedWidthScalarValue(kind, bits);
    const boxed = host.importFunction({
      kind: "box",
      scalar: kind,
      result: "object",
    })(host.encode(kind, semantic));
    const reference = host.decode("object", boxed);
    assert.equal(reference.kind, "heap", `${kind} box used a tagged representation`);
    assert.deepStrictEqual(
      host.decode(
        kind,
        host.importFunction({ kind: "unbox", scalar: kind })(boxed),
      ),
      semantic,
      `${kind} box/unbox changed raw bits`,
    );
  }
  const immediate = host.encode("tobject", { kind: "tagged", payload: 0n });
  assert.throws(() =>
    host.importFunction({ kind: "unbox", scalar: "float32" })(immediate));
  assert.throws(() =>
    host.importFunction({ kind: "unbox", scalar: "float" })(immediate));

  assert.deepStrictEqual(
    semanticDatum("float32", float32, host, "Float32 test", validationExternals),
    { bits: { width: 32, value: "2143363909" } },
  );
  assert.deepStrictEqual(
    semanticDatum("float64", float64, host, "Float test", validationExternals),
    { bits: { width: 64, value: "9221140253039434428" } },
  );
  assert.throws(() =>
    semanticDatum("float64", float32, host, "cross-width Float test",
      validationExternals));
  assert.throws(() =>
    semanticDatum("float32", float64, host, "cross-width Float32 test",
      validationExternals));
  assert.throws(() =>
    semanticDatum(
      "float32",
      fixedWidthScalarValue("float32", 0x100000000n),
      host,
      "out-of-range Float32 test",
      validationExternals,
    ));

  const mixedSchema = {
    ctor: {
      name: "Mixed.mk",
      tag: 3,
      fields: [
        "nat",
        "usize",
        { bits: { width: 32 } },
        "float32",
        "float64",
        "nat",
      ],
    },
  };
  const mixed = host.alloc({
    kind: "ctor",
    tag: 3n,
    objectFields: [
      { kind: "tagged", payload: 11n },
      { kind: "tagged", payload: 12n },
    ],
    usizeFields: [0xffffffffffffffffn],
    scalarFields: [
      { width: 3, offset: 0, value: float64 },
      {
        width: 3,
        offset: 12,
        value: fixedWidthScalarValue("float32", 0x80000000n),
      },
      {
        width: 3,
        offset: 8,
        value: fixedWidthScalarValue("uint32", 0xdeadbeefn),
      },
    ],
  });
  assert.deepStrictEqual(
    semanticDatum(mixedSchema, mixed, host, "mixed constructor", validationExternals),
    {
      ctor: {
        name: "Mixed.mk",
        tag: 3,
        fields: [
          { nat: { value: "11" } },
          { usize: { value: "18446744073709551615" } },
          { bits: { width: 32, value: "3735928559" } },
          { bits: { width: 32, value: "2147483648" } },
          { bits: { width: 64, value: "9221140253039434428" } },
          { nat: { value: "12" } },
        ],
      },
    },
  );
  assert.throws(() => semanticDatum(
    { ctor: { name: "Bad.mk", tag: 3, fields: [{ bits: { width: 24 } }] } },
    mixed,
    host,
    "unsupported packed constructor",
    validationExternals,
  ));

  const invokeFloat = (name, args) =>
    invoke(validationExternalRegistry[name], host, args);
  assert.deepStrictEqual(
    invokeFloat("Float32.neg", [fixedWidthScalarValue("float32", 0n)]),
    fixedWidthScalarValue("float32", 0x80000000n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float.neg", [fixedWidthScalarValue("float", 0n)]),
    fixedWidthScalarValue("float", 0x8000000000000000n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float32.ofBits", [fixedWidthScalarValue("uint32", 0x7fc12345n)]),
    fixedWidthScalarValue("float32", 0x7fc00000n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float.ofBits", [
      fixedWidthScalarValue("uint64", 0x7ff8123456789abcn),
    ]),
    fixedWidthScalarValue("float", 0x7ff8000000000000n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float.toBits", [float64]),
    fixedWidthScalarValue("uint64", 0x7ff8123456789abcn),
  );
  assert.deepStrictEqual(
    invokeFloat("Float32.isNaN", [float32]),
    fixedWidthScalarValue("uint8", 1n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float.isFinite", [
      fixedWidthScalarValue("float", 0x7ff0000000000000n),
    ]),
    fixedWidthScalarValue("uint8", 0n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float32.div", [
      fixedWidthScalarValue("float32", 0n),
      fixedWidthScalarValue("float32", 0n),
    ]),
    fixedWidthScalarValue("float32", 0x7fc00000n),
  );
  assert.deepStrictEqual(
    invokeFloat("Float.div", [
      fixedWidthScalarValue("float", 0n),
      fixedWidthScalarValue("float", 0n),
    ]),
    fixedWidthScalarValue("float", 0x7ff8000000000000n),
  );
  assert.throws(() =>
    invokeFloat("Float32.add", [
      fixedWidthScalarValue("float", 0n),
      fixedWidthScalarValue("float32", 0n),
    ]));
}

for (const { typeName, width, decode, encode, wrongValue } of fixedWidthFamilies) {
  const declaration = suffix => `${typeName}.${suffix}`;
  const max = (1n << BigInt(width)) - 1n;
  const high = 1n << BigInt(width - 1);
  for (const [suffix, left, right, expected] of [
    ["add", max, 1n, 0n],
    ["sub", 0n, 1n, max],
    ["mul", high, 2n, 0n],
    ["div", max, 3n, max / 3n],
    ["div", max, 0n, 0n],
    ["mod", max, 16n, 15n],
    ["mod", max, 0n, max],
    ["land", max, high | 1n, high | 1n],
    ["lor", high, 1n, high | 1n],
    ["xor", max, high, max ^ high],
    ["shiftLeft", high | 1n, BigInt(width), high | 1n],
    ["shiftLeft", high | 1n, BigInt(width + 1), 2n],
    ["shiftRight", high | 1n, BigInt(width), high | 1n],
    ["shiftRight", high | 1n, BigInt(width + 1), high >> 1n],
  ]) {
    const name = declaration(suffix);
    const host = new SemanticHost();
    const leftValue = encode(left);
    const rightValue = encode(right);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [leftValue, rightValue]);
    assert.equal(decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.deepStrictEqual(leftValue, encode(left));
    assert.deepStrictEqual(rightValue, encode(right));
  }
  for (const [suffix, input, expected] of [
    ["complement", 0n, max],
    ["neg", 1n, max],
  ]) {
    const name = declaration(suffix);
    const host = new SemanticHost();
    const inputValue = encode(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.deepStrictEqual(inputValue, encode(input));
  }
  for (const [suffix, left, right, expected] of [
    ["decEq", max, max, 1n],
    ["decEq", max, 0n, 0n],
    ["decLt", 0n, max, 1n],
    ["decLt", max, 0n, 0n],
    ["decLe", max, max, 1n],
    ["decLe", max, 0n, 0n],
  ]) {
    const name = declaration(suffix);
    const host = new SemanticHost();
    const leftValue = encode(left);
    const rightValue = encode(right);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [leftValue, rightValue]);
    assert.deepStrictEqual(result, {
      kind: "scalar",
      scalarKind: "uint8",
      value: expected,
    });
    assert.equal(host.nextLocation, frontier);
    assert.deepStrictEqual(leftValue, encode(left));
    assert.deepStrictEqual(rightValue, encode(right));
  }
  assert.throws(() => invoke(
    validationExternalRegistry[declaration("add")],
    new SemanticHost(),
    [wrongValue, encode(1n)]));
  assert.throws(() => decode(encode(max + 1n), `${typeName} out-of-range`));
}

for (const { typeName, width, decode, encode, wrongValue } of fixedWidthFamilies) {
  const ofNatName = `${typeName}.ofNat`;
  const toNatName = `${typeName}.toNat`;
  const max = (1n << BigInt(width)) - 1n;
  const modulus = 1n << BigInt(width);
  assert.strictEqual(
    formatExternalRegistry[ofNatName],
    validationExternalRegistry[ofNatName]);
  assert.strictEqual(
    formatExternalRegistry[toNatName],
    validationExternalRegistry[toNatName]);

  for (const [input, expected] of [
    [0n, 0n],
    [max, max],
    [modulus, 0n],
    [0x100000000000000000000000000000011n, 17n],
  ]) {
    const host = new SemanticHost();
    const inputValue = host.natural(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[ofNatName], host, [inputValue]);
    assert.equal(decode(result, `${ofNatName} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.equal(naturalValue(host, inputValue, `${ofNatName} retained input`), input);
  }

  const toNatCases = width === 64
    ? [
        [0n, false],
        [0x7fffffffffffffffn, false],
        [0x8000000000000000n, true],
        [max, true],
      ]
    : [[0n, false], [max, false]];
  for (const [input, allocates] of toNatCases) {
    const host = new SemanticHost();
    const inputValue = encode(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[toNatName], host, [inputValue]);
    assert.equal(naturalValue(host, result, `${toNatName} result`), input);
    assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
    assert.equal(decode(inputValue, `${toNatName} retained input`), input);
  }

  assert.throws(() => invoke(
    validationExternalRegistry[ofNatName],
    new SemanticHost(),
    [encode(1n)]));
  assert.throws(() => invoke(
    validationExternalRegistry[toNatName],
    new SemanticHost(),
    [wrongValue]));
}

let fixedWidthConversionCount = 0;
for (const source of fixedWidthFamilies) {
  for (const target of fixedWidthFamilies) {
    if (source.typeName === target.typeName) {
      continue;
    }
    fixedWidthConversionCount += 1;
    const name = `${source.typeName}.to${target.typeName}`;
    const input = (1n << BigInt(source.width)) - 1n;
    const expected = BigInt.asUintN(target.width, input);
    assert.strictEqual(
      formatExternalRegistry[name],
      validationExternalRegistry[name]);
    const host = new SemanticHost();
    const inputValue = source.encode(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(target.decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.equal(
      source.decode(inputValue, `${name} retained input`),
      input);
    assert.throws(() => invoke(
      validationExternalRegistry[name],
      new SemanticHost(),
      [source.wrongValue]));
  }
}
assert.equal(fixedWidthConversionCount, 20);

for (const {
  typeName,
  width,
  decode,
  encode,
  wrongValue,
} of signedFixedWidthFamilies) {
  const declaration = suffix => `${typeName}.${suffix}`;
  const min = -(1n << BigInt(width - 1));
  const max = (1n << BigInt(width - 1)) - 1n;
  const halfRange = 1n << BigInt(width - 2);
  const nearMin = min + 1n;
  for (const [suffix, left, right, expected] of [
    ["add", max, 1n, min],
    ["sub", min, 1n, max],
    ["mul", halfRange, 2n, min],
    ["div", -7n, 3n, -2n],
    ["div", min, -1n, min],
    ["div", -7n, 0n, 0n],
    ["mod", -7n, 3n, -1n],
    ["mod", 7n, -3n, 1n],
    ["mod", -7n, 0n, -7n],
    ["land", -16n, 60n, 48n],
    ["lor", -64n, 60n, -4n],
    ["xor", -16n, 60n, -52n],
    ["shiftLeft", nearMin, -BigInt(width), nearMin],
    ["shiftLeft", nearMin, -1n, min],
    ["shiftLeft", nearMin, BigInt(width + 1), 2n],
    ["shiftRight", nearMin, -BigInt(width), nearMin],
    ["shiftRight", nearMin, -1n, -1n],
    ["shiftRight", nearMin, BigInt(width + 1), nearMin >> 1n],
  ]) {
    const name = declaration(suffix);
    const host = new SemanticHost();
    const leftValue = encode(left);
    const rightValue = encode(right);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [leftValue, rightValue]);
    assert.equal(decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.deepStrictEqual(leftValue, encode(left));
    assert.deepStrictEqual(rightValue, encode(right));
  }
  for (const [suffix, input, expected] of [
    ["complement", 0n, -1n],
    ["neg", min, min],
    ["abs", -7n, 7n],
    ["abs", min, min],
  ]) {
    const name = declaration(suffix);
    const host = new SemanticHost();
    const inputValue = encode(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.deepStrictEqual(inputValue, encode(input));
  }
  for (const [suffix, left, right, expected] of [
    ["decEq", -1n, -1n, 1n],
    ["decEq", -1n, 1n, 0n],
    ["decLt", -1n, 0n, 1n],
    ["decLt", max, min, 0n],
    ["decLe", min, min, 1n],
    ["decLe", 0n, -1n, 0n],
  ]) {
    const name = declaration(suffix);
    const host = new SemanticHost();
    const leftValue = encode(left);
    const rightValue = encode(right);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [leftValue, rightValue]);
    assert.deepStrictEqual(result, {
      kind: "scalar",
      scalarKind: "uint8",
      value: expected,
    });
    assert.equal(host.nextLocation, frontier);
    assert.deepStrictEqual(leftValue, encode(left));
    assert.deepStrictEqual(rightValue, encode(right));
  }

  for (const [input, expected] of [
    [(1n << BigInt(width)) - 1n, -1n],
    [1n << BigInt(width), 0n],
    [0x100000000000000000000000000000011n, 17n],
  ]) {
    const name = declaration("ofNat");
    const host = new SemanticHost();
    const inputValue = host.natural(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.equal(naturalValue(host, inputValue, `${name} retained input`), input);
  }

  for (const [input, expected] of [
    [max + 1n, min],
    [min - 1n, max],
    [0x100000000000000000000000000000011n, 17n],
    [-0x100000000000000000000000000000011n, -17n],
  ]) {
    const name = declaration("ofInt");
    const host = new SemanticHost();
    const inputValue = host.integer(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.equal(integerValue(host, inputValue, `${name} retained input`), input);
  }

  for (const input of [min, max]) {
    const name = declaration("toInt");
    const host = new SemanticHost();
    const inputValue = encode(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(integerValue(host, result, `${name} result`), input);
    const allocates = input < -0x80000000n || input > 0x7fffffffn;
    assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
    assert.equal(decode(inputValue, `${name} retained input`), input);
  }

  for (const suffix of signedFixedWidthSuffixes) {
    const args = ["complement", "neg", "abs"].includes(suffix)
      ? [wrongValue]
      : [wrongValue, encode(1n)];
    assert.throws(() => invoke(
      validationExternalRegistry[declaration(suffix)],
      new SemanticHost(),
      args));
  }
  assert.throws(() => invoke(
    validationExternalRegistry[declaration("ofNat")],
    new SemanticHost(),
    [encode(1n)]));
  assert.throws(() => invoke(
    validationExternalRegistry[declaration("ofInt")],
    new SemanticHost(),
    [encode(1n)]));
  assert.throws(() => invoke(
    validationExternalRegistry[declaration("toInt")],
    new SemanticHost(),
    [wrongValue]));
}

let signedFixedWidthConversionCount = 0;
for (const source of signedFixedWidthFamilies) {
  for (const target of signedFixedWidthFamilies) {
    if (source.typeName === target.typeName) {
      continue;
    }
    signedFixedWidthConversionCount += 1;
    const name = `${source.typeName}.to${target.typeName}`;
    const input = BigInt.asIntN(
      source.width, -0x123456789abcdefn);
    const expected = BigInt.asIntN(target.width, input);
    assert.strictEqual(
      formatExternalRegistry[name],
      validationExternalRegistry[name]);
    const host = new SemanticHost();
    const inputValue = source.encode(input);
    const frontier = host.nextLocation;
    const result = invoke(
      validationExternalRegistry[name], host, [inputValue]);
    assert.equal(target.decode(result, `${name} result`), expected);
    assert.equal(host.nextLocation, frontier);
    assert.equal(
      source.decode(inputValue, `${name} retained input`),
      input);
    assert.throws(() => invoke(
      validationExternalRegistry[name],
      new SemanticHost(),
      [source.wrongValue]));
  }
}
assert.equal(signedFixedWidthConversionCount, 20);

for (const [leftValue, rightValue, expected, allocates] of [
  [6n, 7n, 42n, false],
  [0x7fffffffffffffffn, 2n, 0xfffffffffffffffen, true],
  [
    340282366920938463463374607431768211473n,
    18446744073709551619n,
    6277101735386680764856636523970481806806073916012401524787n,
    true,
  ],
  [340282366920938463463374607431768211473n, 0n, 0n, false],
]) {
  const host = new SemanticHost();
  const left = host.natural(leftValue);
  const right = host.natural(rightValue);
  const frontier = host.nextLocation;
  const result = invoke(natMul, host, [left, right]);
  assert.equal(naturalValue(host, result, "Nat.mul result"), expected);
  assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
  assert.equal(naturalValue(host, left, "Nat.mul retained left"), leftValue);
  assert.equal(naturalValue(host, right, "Nat.mul retained right"), rightValue);
}

for (const [leftValue, rightValue, expected, allocates] of [
  [6n, -7n, -42n, false],
  [2147483647n, 2n, 4294967294n, true],
  [-2147483648n, -1n, 2147483648n, true],
  [
    340282366920938463463374607431768211473n,
    -17n,
    -5784800237655953878877368326340059595041n,
    true,
  ],
  [340282366920938463463374607431768211473n, 0n, 0n, false],
]) {
  const host = new SemanticHost();
  const left = host.integer(leftValue);
  const right = host.integer(rightValue);
  const frontier = host.nextLocation;
  const result = invoke(intMul, host, [left, right]);
  assert.equal(integerValue(host, result, "Int.mul result"), expected);
  assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
  assert.equal(integerValue(host, left, "Int.mul retained left"), leftValue);
  assert.equal(integerValue(host, right, "Int.mul retained right"), rightValue);
}

for (const [handler, declaration, value, count, expected, allocates] of [
  [intShiftLeft, "Int.shiftLeft", 2147483647n, 1n, 4294967294n, true],
  [intShiftLeft, "Int.shiftLeft", -2147483648n, 1n, -4294967296n, true],
  [
    intShiftLeft, "Int.shiftLeft",
    340282366920938463463374607431768211473n,
    65n,
    12554203470773361527671578846415332832831900187434193780736n,
    true,
  ],
  [
    intShiftLeft, "Int.shiftLeft",
    -340282366920938463463374607431768211473n,
    65n,
    -12554203470773361527671578846415332832831900187434193780736n,
    true,
  ],
  [
    intShiftRight, "Int.shiftRight",
    340282366920938463463374607431768211473n,
    65n,
    9223372036854775808n,
    true,
  ],
  [
    intShiftRight, "Int.shiftRight",
    -340282366920938463463374607431768211473n,
    65n,
    -9223372036854775809n,
    true,
  ],
  [
    intShiftRight, "Int.shiftRight",
    340282366920938463463374607431768211473n,
    128n,
    1n,
    false,
  ],
  [
    intShiftRight, "Int.shiftRight",
    -340282366920938463463374607431768211473n,
    129n,
    -1n,
    false,
  ],
  [
    intShiftRight, "Int.shiftRight",
    -340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    -1n,
    false,
  ],
]) {
  const host = new SemanticHost();
  const input = host.integer(value);
  const shiftCount = host.natural(count);
  const frontier = host.nextLocation;
  const result = invoke(handler, host, [input, shiftCount]);
  assert.equal(integerValue(host, result, `${declaration} result`), expected);
  assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
  assert.equal(integerValue(host, input, `${declaration} retained value`), value);
  assert.equal(
    naturalValue(host, shiftCount, `${declaration} retained count`), count);
}

for (const [handler, declaration, leftValue, rightValue, expected, allocates] of [
  [
    natDiv, "Nat.div",
    340282366920938463463374607431768211473n,
    18446744073709551619n,
    18446744073709551613n,
    true,
  ],
  [
    natDiv, "Nat.div",
    340282366920938463463374607431768211473n,
    0n,
    0n,
    false,
  ],
  [
    natMod, "Nat.mod",
    340282366920938463463374607431768211473n,
    18446744073709551619n,
    26n,
    false,
  ],
  [
    natMod, "Nat.mod",
    340282366920938463463374607431768211473n,
    0n,
    340282366920938463463374607431768211473n,
    true,
  ],
]) {
  const host = new SemanticHost();
  const left = host.natural(leftValue);
  const right = host.natural(rightValue);
  const frontier = host.nextLocation;
  const result = invoke(handler, host, [left, right]);
  assert.equal(naturalValue(host, result, `${declaration} result`), expected);
  assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
  assert.equal(naturalValue(host, left, `${declaration} retained left`), leftValue);
  assert.equal(naturalValue(host, right, `${declaration} retained right`), rightValue);
}

for (const [handler, declaration, leftValue, rightValue, expected, allocates] of [
  [
    natLand, "Nat.land",
    340282366920938463463374607431768211473n,
    18446744073709551619n,
    1n,
    false,
  ],
  [
    natLor, "Nat.lor",
    340282366920938463463374607431768211473n,
    18446744073709551619n,
    340282366920938463481821351505477763091n,
    true,
  ],
  [
    natXor, "Nat.xor",
    340282366920938463463374607431768211473n,
    18446744073709551619n,
    340282366920938463481821351505477763090n,
    true,
  ],
  [
    natXor, "Nat.xor",
    340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    0n,
    false,
  ],
  [
    natShiftLeft, "Nat.shiftLeft",
    0x7fffffffffffffffn,
    1n,
    0xfffffffffffffffen,
    true,
  ],
  [
    natShiftLeft, "Nat.shiftLeft",
    340282366920938463463374607431768211473n,
    65n,
    12554203470773361527671578846415332832831900187434193780736n,
    true,
  ],
  [
    natShiftRight, "Nat.shiftRight",
    340282366920938463463374607431768211473n,
    65n,
    9223372036854775808n,
    true,
  ],
  [
    natShiftRight, "Nat.shiftRight",
    340282366920938463463374607431768211473n,
    128n,
    1n,
    false,
  ],
  [
    natShiftRight, "Nat.shiftRight",
    340282366920938463463374607431768211473n,
    129n,
    0n,
    false,
  ],
  [
    natShiftRight, "Nat.shiftRight",
    340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    0n,
    false,
  ],
]) {
  const host = new SemanticHost();
  const left = host.natural(leftValue);
  const right = host.natural(rightValue);
  const frontier = host.nextLocation;
  const result = invoke(handler, host, [left, right]);
  assert.equal(naturalValue(host, result, `${declaration} result`), expected);
  assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
  assert.equal(naturalValue(host, left, `${declaration} retained left`), leftValue);
  assert.equal(naturalValue(host, right, `${declaration} retained right`), rightValue);
}

for (const [handler, declaration, leftValue, rightValue, expected, allocates] of [
  [
    intEDiv, "Int.ediv",
    -340282366920938463463374607431768211473n,
    17n,
    -20016609818878733144904388672456953617n,
    true,
  ],
  [intEDiv, "Int.ediv", -12n, -7n, 2n, false],
  [
    intEDiv, "Int.ediv",
    340282366920938463463374607431768211473n,
    0n,
    0n,
    false,
  ],
  [
    intEMod, "Int.emod",
    -340282366920938463463374607431768211473n,
    17n,
    16n,
    false,
  ],
  [intEMod, "Int.emod", -12n, -7n, 2n, false],
  [
    intEMod, "Int.emod",
    -340282366920938463463374607431768211473n,
    0n,
    -340282366920938463463374607431768211473n,
    true,
  ],
]) {
  const host = new SemanticHost();
  const left = host.integer(leftValue);
  const right = host.integer(rightValue);
  const frontier = host.nextLocation;
  const result = invoke(handler, host, [left, right]);
  assert.equal(integerValue(host, result, `${declaration} result`), expected);
  assert.equal(host.nextLocation, frontier + (allocates ? 1 : 0));
  assert.equal(integerValue(host, left, `${declaration} retained left`), leftValue);
  assert.equal(integerValue(host, right, `${declaration} retained right`), rightValue);
}

for (const [handler, declaration, leftValue, rightValue, expected] of [
  [
    intDecEq, "Int.decEq",
    340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    1n,
  ],
  [
    intDecEq, "Int.decEq",
    -340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    0n,
  ],
  [
    intDecLt, "Int.decLt",
    -340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    1n,
  ],
  [
    intDecLt, "Int.decLt",
    340282366920938463463374607431768211473n,
    340282366920938463463374607431768211473n,
    0n,
  ],
  [
    intDecLe, "Int.decLe",
    -340282366920938463463374607431768211473n,
    -340282366920938463463374607431768211473n,
    1n,
  ],
  [
    intDecLe, "Int.decLe",
    340282366920938463463374607431768211473n,
    -340282366920938463463374607431768211473n,
    0n,
  ],
]) {
  const host = new SemanticHost();
  const left = host.integer(leftValue);
  const right = host.integer(rightValue);
  const frontier = host.nextLocation;
  const result = invoke(handler, host, [left, right]);
  assert.deepStrictEqual(result, {
    kind: "scalar",
    scalarKind: "uint8",
    value: expected,
  });
  assert.equal(host.nextLocation, frontier);
  assert.equal(integerValue(host, left, `${declaration} retained left`), leftValue);
  assert.equal(integerValue(host, right, `${declaration} retained right`), rightValue);
}

{
  const host = new SemanticHost();
  const left = host.alloc({ kind: "string", value: "A" });
  const right = host.alloc({ kind: "string", value: "é😀" });
  const beforeRight = snapshot(stringCell(host, right));
  const frontier = host.nextLocation;
  const result = invoke(append, host, [left, right]);
  assert.deepStrictEqual(result, left);
  assert.equal(host.nextLocation, frontier);
  assert.deepStrictEqual(snapshot(stringCell(host, right)), beforeRight);
  assert.deepStrictEqual(stringCell(host, left), {
    location: left.location,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "string", value: "Aé😀" },
  });
}

{
  const host = new SemanticHost();
  const left = host.alloc({ kind: "string", value: "A" });
  const right = host.alloc({ kind: "string", value: "é😀" });
  host.incLocation(left.location, 1);
  const beforeRight = snapshot(stringCell(host, right));
  const frontier = host.nextLocation;
  const result = invoke(append, host, [left, right]);
  assert.equal(result.location, frontier);
  assert.equal(host.nextLocation, frontier + 1);
  assert.deepStrictEqual(snapshot(stringCell(host, right)), beforeRight);
  assert.deepStrictEqual(stringCell(host, left), {
    location: left.location,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "string", value: "A" },
  });
  assert.deepStrictEqual(stringCell(host, result), {
    location: result.location,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "string", value: "Aé😀" },
  });
}

{
  const host = new SemanticHost();
  const left = host.alloc({ kind: "string", value: "A" }, true);
  const right = host.alloc({ kind: "string", value: "é😀" });
  const beforeLeft = snapshot(stringCell(host, left));
  const beforeRight = snapshot(stringCell(host, right));
  const frontier = host.nextLocation;
  const result = invoke(append, host, [left, right]);
  assert.equal(result.location, frontier);
  assert.equal(host.nextLocation, frontier + 1);
  assert.deepStrictEqual(snapshot(stringCell(host, left)), beforeLeft);
  assert.deepStrictEqual(snapshot(stringCell(host, right)), beforeRight);
  assert.equal(stringCell(host, result).object.value, "Aé😀");
}

{
  const host = new SemanticHost();
  const source = host.alloc({ kind: "string", value: "A" });
  host.incLocation(source.location, 1);
  const beforeSource = snapshot(stringCell(host, source));
  const frontier = host.nextLocation;
  const result = invoke(pushn, host, [
    source, character(0x1f600), host.natural(0n),
  ]);
  assert.deepStrictEqual(result, source);
  assert.equal(host.nextLocation, frontier);
  assert.deepStrictEqual(snapshot(stringCell(host, source)), beforeSource);
}

{
  const host = new SemanticHost();
  const source = host.alloc({ kind: "string", value: "A" });
  const frontier = host.nextLocation;
  const result = invoke(pushn, host, [
    source, character(0x1f600), host.natural(2n),
  ]);
  assert.deepStrictEqual(result, source);
  assert.equal(host.nextLocation, frontier);
  assert.deepStrictEqual(stringCell(host, source), {
    location: source.location,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "string", value: "A😀😀" },
  });
}

{
  const host = new SemanticHost();
  const source = host.alloc({ kind: "string", value: "A" });
  host.incLocation(source.location, 1);
  const frontier = host.nextLocation;
  const result = invoke(pushn, host, [
    source, character(0x1f600), host.natural(2n),
  ]);
  assert.equal(result.location, frontier);
  assert.equal(host.nextLocation, frontier + 1);
  assert.deepStrictEqual(stringCell(host, source), {
    location: source.location,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "string", value: "A" },
  });
  assert.deepStrictEqual(stringCell(host, result), {
    location: result.location,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "string", value: "A😀😀" },
  });
}

for (const [handler, leftValue, rightValue, expected] of [
  [decEq, "A\u0000é😀", "A\u0000é😀", 1n],
  [decEq, "A\u0000é😀", "A\u0000é😁", 0n],
  [decLt, "\ue000", "\u{10000}", 1n],
  [decLt, "\u{10000}", "\ue000", 0n],
  [compare, "A\u0000", "A\u0000", 1n],
  [compare, "\ue000", "\u{10000}", 0n],
  [compare, "\u{10000}", "\ue000", 2n],
  [compare, "A", "A\u0000", 0n],
]) {
  const host = new SemanticHost();
  const left = host.alloc({ kind: "string", value: leftValue });
  const right = host.alloc({ kind: "string", value: rightValue });
  const beforeLeft = snapshot(stringCell(host, left));
  const beforeRight = snapshot(stringCell(host, right));
  const frontier = host.nextLocation;
  assert.deepStrictEqual(invoke(handler, host, [left, right]), {
    kind: "scalar",
    scalarKind: "uint8",
    value: expected,
  });
  assert.equal(host.nextLocation, frontier);
  assert.deepStrictEqual(snapshot(stringCell(host, left)), beforeLeft);
  assert.deepStrictEqual(snapshot(stringCell(host, right)), beforeRight);
}

console.log("PASS shared Wasm String and arithmetic external contracts");
