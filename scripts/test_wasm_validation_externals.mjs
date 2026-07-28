import assert from "node:assert/strict";

import { formatExternalRegistry } from "./wasm_format_externals.mjs";
import { SemanticHost } from "./wasm_semantic_host.mjs";
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
