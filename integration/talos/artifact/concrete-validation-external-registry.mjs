import assert from "../../../scripts/wasm_assert.mjs";
import {
  stringCompare,
} from "../../../scripts/wasm_format_external_algorithms.mjs";
import {
  validationExternalRegistry,
} from "../../../scripts/wasm_validation_externals.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";

const concreteFloatExternalRegistry = Object.fromEntries(
  Object.entries(validationExternalRegistry)
    .filter(([declaration]) => declaration.startsWith("Float")),
);

function naturalValue(host, value, context) {
  if (value.kind === "tagged") return value.payload;
  assert.equal(value.kind, "heap", `${context} must be a tagged or heap natural`);
  return host.readNatural(host.addressOf(value.location));
}

function integerValue(host, value, context) {
  if (value.kind === "tagged") {
    assert.ok(value.payload >= 0n && value.payload <= 0xffffffffn,
      `${context} immediate integer payload is out of range`);
    return BigInt.asIntN(32, value.payload);
  }
  assert.equal(value.kind, "heap", `${context} must be a tagged or heap integer`);
  return host.readInteger(host.addressOf(value.location));
}

function naturalResult(host, value) {
  return host.decode("tobject", host.allocateNatural(value));
}

function integerResult(host, value) {
  return host.decode("tobject", host.allocateInteger(value));
}

function stringValue(host, value, context) {
  assert.equal(value.kind, "heap", `${context} must be a heap string`);
  return host.readString(host.addressOf(value.location));
}

function boolResult(value) {
  return { kind: "scalar", scalarKind: "uint8", value: value ? 1n : 0n };
}

function naturalBinary(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = naturalValue(host, args[0], `${declaration} left operand`);
    const right = naturalValue(host, args[1], `${declaration} right operand`);
    return { value: naturalResult(host, operation(left, right)), world };
  };
}

function integerBinary(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = integerValue(host, args[0], `${declaration} left operand`);
    const right = integerValue(host, args[1], `${declaration} right operand`);
    return { value: integerResult(host, operation(left, right)), world };
  };
}

function integerNaturalBinary(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const value = integerValue(host, args[0], `${declaration} value`);
    const count = naturalValue(host, args[1], `${declaration} count`);
    return { value: integerResult(host, operation(value, count)), world };
  };
}

function integerDecision(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = integerValue(host, args[0], `${declaration} left operand`);
    const right = integerValue(host, args[1], `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
  };
}

function fixedWidthScalar(value, scalarKind, width, context) {
  assert.equal(value.kind, "scalar", `${context} must be a scalar`);
  assert.equal(value.scalarKind, scalarKind, `${context} must use ${scalarKind}`);
  assert.ok(value.value >= 0n && value.value < (1n << BigInt(width)),
    `${context} is out of ${scalarKind} range`);
  return value.value;
}

function fixedWidthResult(scalarKind, width, value) {
  return {
    kind: "scalar",
    scalarKind,
    value: BigInt.asUintN(width, value),
  };
}

function fixedWidthBinary(declaration, scalarKind, width, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = fixedWidthScalar(
      args[0], scalarKind, width, `${declaration} left operand`);
    const right = fixedWidthScalar(
      args[1], scalarKind, width, `${declaration} right operand`);
    return {
      value: fixedWidthResult(scalarKind, width, operation(left, right)),
      world,
    };
  };
}

function fixedWidthUnary(declaration, scalarKind, width, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = fixedWidthScalar(
      args[0], scalarKind, width, `${declaration} operand`);
    return {
      value: fixedWidthResult(scalarKind, width, operation(value)),
      world,
    };
  };
}

function fixedWidthDecision(declaration, scalarKind, width, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = fixedWidthScalar(
      args[0], scalarKind, width, `${declaration} left operand`);
    const right = fixedWidthScalar(
      args[1], scalarKind, width, `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
  };
}

function fixedWidthExternalFamily(typeName, scalarKind, width) {
  const declaration = suffix => `${typeName}.${suffix}`;
  const binary = (suffix, operation) =>
    fixedWidthBinary(declaration(suffix), scalarKind, width, operation);
  const unary = (suffix, operation) =>
    fixedWidthUnary(declaration(suffix), scalarKind, width, operation);
  const decision = (suffix, operation) =>
    fixedWidthDecision(declaration(suffix), scalarKind, width, operation);
  const shiftMask = BigInt(width - 1);
  return {
    [declaration("add")]: binary("add", (left, right) => left + right),
    [declaration("sub")]: binary("sub", (left, right) => left - right),
    [declaration("mul")]: binary("mul", (left, right) => left * right),
    [declaration("div")]: binary(
      "div", (left, right) => right === 0n ? 0n : left / right),
    [declaration("mod")]: binary(
      "mod", (left, right) => right === 0n ? left : left % right),
    [declaration("land")]: binary("land", (left, right) => left & right),
    [declaration("lor")]: binary("lor", (left, right) => left | right),
    [declaration("xor")]: binary("xor", (left, right) => left ^ right),
    [declaration("shiftLeft")]: binary(
      "shiftLeft", (value, count) => value << (count & shiftMask)),
    [declaration("shiftRight")]: binary(
      "shiftRight", (value, count) => value >> (count & shiftMask)),
    [declaration("complement")]: unary("complement", value => ~value),
    [declaration("neg")]: unary("neg", value => -value),
    [declaration("decEq")]: decision("decEq", (left, right) => left === right),
    [declaration("decLt")]: decision("decLt", (left, right) => left < right),
    [declaration("decLe")]: decision("decLe", (left, right) => left <= right),
  };
}

function scalarFixedWidthCodec(scalarKind, width) {
  return {
    decode: (value, context) =>
      fixedWidthScalar(value, scalarKind, width, context),
    encode: value => fixedWidthResult(scalarKind, width, value),
  };
}

function signedScalarFixedWidthCodec(scalarKind, width) {
  const unsigned = scalarFixedWidthCodec(scalarKind, width);
  return signedFixedWidthCodec(unsigned, width);
}

function signedFixedWidthCodec(unsigned, width) {
  return {
    decode: (value, context) =>
      BigInt.asIntN(width, unsigned.decode(value, context)),
    encode: value => unsigned.encode(BigInt.asUintN(width, value)),
  };
}

function usizeValue(value, context) {
  assert.equal(value.kind, "usize", `${context} must be a USize`);
  assert.ok(value.value >= 0n && value.value < (1n << 64n),
    `${context} is out of USize range`);
  return value.value;
}

const usizeFixedWidthCodec = {
  decode: usizeValue,
  encode: value => ({ kind: "usize", value: BigInt.asUintN(64, value) }),
};

const fixedWidthCodecs = {
  UInt8: scalarFixedWidthCodec("uint8", 8),
  UInt16: scalarFixedWidthCodec("uint16", 16),
  UInt32: scalarFixedWidthCodec("uint32", 32),
  UInt64: scalarFixedWidthCodec("uint64", 64),
  USize: usizeFixedWidthCodec,
};

const signedFixedWidthCodecs = {
  Int8: signedScalarFixedWidthCodec("uint8", 8),
  Int16: signedScalarFixedWidthCodec("uint16", 16),
  Int32: signedScalarFixedWidthCodec("uint32", 32),
  Int64: signedScalarFixedWidthCodec("uint64", 64),
  ISize: signedFixedWidthCodec(usizeFixedWidthCodec, 64),
};

function codecFixedWidthBinary(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = codec.decode(args[0], `${declaration} left operand`);
    const right = codec.decode(args[1], `${declaration} right operand`);
    return { value: codec.encode(operation(left, right)), world };
  };
}

function codecFixedWidthUnary(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = codec.decode(args[0], `${declaration} operand`);
    return { value: codec.encode(operation(value)), world };
  };
}

function codecFixedWidthDecision(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = codec.decode(args[0], `${declaration} left operand`);
    const right = codec.decode(args[1], `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
  };
}

function codecFixedWidthExternalFamily(typeName, width, codec) {
  const declaration = suffix => `${typeName}.${suffix}`;
  const binary = (suffix, operation) =>
    codecFixedWidthBinary(declaration(suffix), codec, operation);
  const unary = (suffix, operation) =>
    codecFixedWidthUnary(declaration(suffix), codec, operation);
  const decision = (suffix, operation) =>
    codecFixedWidthDecision(declaration(suffix), codec, operation);
  const shiftMask = BigInt(width - 1);
  return {
    [declaration("add")]: binary("add", (left, right) => left + right),
    [declaration("sub")]: binary("sub", (left, right) => left - right),
    [declaration("mul")]: binary("mul", (left, right) => left * right),
    [declaration("div")]: binary(
      "div", (left, right) => right === 0n ? 0n : left / right),
    [declaration("mod")]: binary(
      "mod", (left, right) => right === 0n ? left : left % right),
    [declaration("land")]: binary("land", (left, right) => left & right),
    [declaration("lor")]: binary("lor", (left, right) => left | right),
    [declaration("xor")]: binary("xor", (left, right) => left ^ right),
    [declaration("shiftLeft")]: binary(
      "shiftLeft", (value, count) => value << (count & shiftMask)),
    [declaration("shiftRight")]: binary(
      "shiftRight", (value, count) => value >> (count & shiftMask)),
    [declaration("complement")]: unary("complement", value => ~value),
    [declaration("neg")]: unary("neg", value => -value),
    [declaration("decEq")]: decision("decEq", (left, right) => left === right),
    [declaration("decLt")]: decision("decLt", (left, right) => left < right),
    [declaration("decLe")]: decision("decLe", (left, right) => left <= right),
  };
}

function signedFixedWidthExternalFamily(typeName, width, codec) {
  const declaration = suffix => `${typeName}.${suffix}`;
  return {
    ...codecFixedWidthExternalFamily(typeName, width, codec),
    [declaration("abs")]: codecFixedWidthUnary(
      declaration("abs"), codec, value => value < 0n ? -value : value),
  };
}

function naturalToFixedWidth(declaration, codec) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = naturalValue(host, args[0], `${declaration} operand`);
    return { value: codec.encode(value), world };
  };
}

function integerToFixedWidth(declaration, codec) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = integerValue(host, args[0], `${declaration} operand`);
    return { value: codec.encode(value), world };
  };
}

function fixedWidthToNatural(declaration, codec) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = codec.decode(args[0], `${declaration} operand`);
    return { value: naturalResult(host, value), world };
  };
}

function fixedWidthToInteger(declaration, codec) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = codec.decode(args[0], `${declaration} operand`);
    return { value: integerResult(host, value), world };
  };
}

function fixedWidthConversion(declaration, sourceCodec, targetCodec) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = sourceCodec.decode(args[0], `${declaration} operand`);
    return { value: targetCodec.encode(value), world };
  };
}

function fixedWidthConversionFamily(sourceTypeName) {
  const sourceCodec = fixedWidthCodecs[sourceTypeName];
  return Object.fromEntries(
    Object.entries(fixedWidthCodecs)
      .filter(([targetTypeName]) => targetTypeName !== sourceTypeName)
      .map(([targetTypeName, targetCodec]) => {
        const declaration = `${sourceTypeName}.to${targetTypeName}`;
        return [
          declaration,
          fixedWidthConversion(declaration, sourceCodec, targetCodec),
        ];
      }));
}

function signedFixedWidthConversionFamily(sourceTypeName) {
  const sourceCodec = signedFixedWidthCodecs[sourceTypeName];
  return Object.fromEntries(
    Object.entries(signedFixedWidthCodecs)
      .filter(([targetTypeName]) => targetTypeName !== sourceTypeName)
      .map(([targetTypeName, targetCodec]) => {
        const declaration = `${sourceTypeName}.to${targetTypeName}`;
        return [
          declaration,
          fixedWidthConversion(declaration, sourceCodec, targetCodec),
        ];
      }));
}

function naturalDivision(left, right) {
  return right === 0n ? 0n : left / right;
}

function naturalRemainder(left, right) {
  return right === 0n ? left : left % right;
}

function naturalShiftRight(value, count) {
  if (value === 0n || count >= BigInt(value.toString(2).length)) return 0n;
  return value >> count;
}

function integerShiftRight(value, count) {
  if (value >= 0n) return naturalShiftRight(value, count);
  return -1n - naturalShiftRight(-1n - value, count);
}

function euclideanRemainder(left, right) {
  if (right === 0n) return left;
  const modulus = right < 0n ? -right : right;
  const remainder = left % modulus;
  return remainder < 0n ? remainder + modulus : remainder;
}

function euclideanDivision(left, right) {
  if (right === 0n) return 0n;
  return (left - euclideanRemainder(left, right)) / right;
}

function stringBinaryUInt8(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = stringValue(host, args[0], `${declaration} left operand`);
    const right = stringValue(host, args[1], `${declaration} right operand`);
    return {
      value: { kind: "scalar", scalarKind: "uint8", value: operation(left, right) },
      world,
    };
  };
}

function recordEffect(host, operation, argument, result) {
  host.validationEffects ??= [];
  host.validationEffects.push({
    operation,
    args: [{ nat: { value: argument.toString() } }],
    result: { nat: { value: result.toString() } },
  });
}

function setArray({ args, host, world }) {
  assert.equal(args.length, 4, "Array.set! external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.set! type argument must be erased");
  const source = args[1];
  const array = host.arrayInfo(source);
  const index = naturalValue(host, args[2], "Array.set! index");
  const replacement = args[3];
  if (index >= BigInt(array.size)) {
    host.releaseValue(replacement);
    return { value: source, world };
  }
  const slot = Number(index);
  if (!array.header.persistent && array.header.rc === 1) {
    host.writeArrayElement(source, slot, replacement);
    host.releaseValue(array.elements[slot]);
    return { value: source, world };
  }
  const elements = [...array.elements];
  elements[slot] = replacement;
  elements.forEach(element => host.retainValue(element));
  host.releaseValue(replacement);
  if (!array.header.persistent) host.releaseValue(source);
  return { value: host.allocateArray(elements, array.capacity), world };
}

function sizeArray({ args, host, world }) {
  assert.equal(args.length, 2, "Array.size external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.size type argument must be erased");
  return { value: naturalResult(host, BigInt(host.arrayInfo(args[1]).size)), world };
}

function inhabitedUInt8({ args, world }) {
  assert.equal(args.length, 0, "instInhabitedUInt8 external arity mismatch");
  return { value: { kind: "scalar", scalarKind: "uint8", value: 0n }, world };
}

function getArrayBang({ args, host, world }) {
  assert.equal(args.length, 4, "Array.get!Internal external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.get!Internal type argument must be erased");
  const fallback = args[1];
  const array = host.arrayInfo(args[2]);
  const index = naturalValue(host, args[3], "Array.get!Internal index");
  const value = index < BigInt(array.size)
    ? array.elements[Number(index)]
    : fallback;
  host.retainValue(value);
  return { value, world };
}

function getArrayBangBorrowed({ args, host, world }) {
  assert.equal(args.length, 4,
    "Array.get!InternalBorrowed external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.get!InternalBorrowed type argument must be erased");
  const fallback = args[1];
  const array = host.arrayInfo(args[2]);
  const index = naturalValue(host, args[3],
    "Array.get!InternalBorrowed index");
  return {
    value: index < BigInt(array.size)
      ? array.elements[Number(index)]
      : fallback,
    world,
  };
}

function pushArray({ args, host, world }) {
  assert.equal(args.length, 3, "Array.push external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.push type argument must be erased");
  const source = args[1];
  const array = host.arrayInfo(source);
  const value = args[2];
  if (!array.header.persistent && array.header.rc === 1) {
    if (array.size < array.capacity) {
      host.appendArrayElement(source, value);
      return { value: source, world };
    }
    const result = host.allocateArray(
      [...array.elements, value], 2 * (array.capacity + 1));
    host.retireTransferredValue(source);
    return { value: result, world };
  }
  array.elements.forEach(element => host.retainValue(element));
  if (!array.header.persistent) host.releaseValue(source);
  const minimum = 2 * array.size + 1;
  const capacity = array.capacity < minimum
    ? 2 * (array.capacity + 1)
    : array.capacity;
  return {
    value: host.allocateArray([...array.elements, value], capacity),
    world,
  };
}

function popArray({ args, host, world }) {
  assert.equal(args.length, 2, "Array.pop external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.pop type argument must be erased");
  const source = args[1];
  const array = host.arrayInfo(source);
  if (!array.header.persistent && array.header.rc === 1) {
    const removed = host.popArrayElement(source);
    if (removed !== undefined) host.releaseValue(removed);
    return { value: source, world };
  }
  const remaining = array.elements.slice(0, -1);
  remaining.forEach(element => host.retainValue(element));
  if (!array.header.persistent) host.releaseValue(source);
  return { value: host.allocateArray(remaining, array.capacity), world };
}

function replicateArray({ args, host, world }) {
  assert.equal(args.length, 3, "Array.replicate external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.replicate type argument must be erased");
  const countValue = args[1];
  const count = naturalValue(host, countValue, "Array.replicate count");
  assert.ok(count <= 0xffff_ffffn,
    "Array.replicate count must fit the Wasm32 resident layout");
  host.releaseValue(countValue);
  const value = args[2];
  if (count === 0n) {
    host.releaseValue(value);
  } else {
    for (let slot = 1n; slot < count; slot += 1n) host.retainValue(value);
  }
  const size = Number(count);
  return {
    value: host.allocateArray(Array(size).fill(value), size),
    world,
  };
}

function swapArray({ args, host, world }) {
  assert.equal(args.length, 6, "Array.swap external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.swap type argument must be erased");
  assert.deepStrictEqual(args[4], { kind: "erased" },
    "Array.swap first bounds proof must be erased");
  assert.deepStrictEqual(args[5], { kind: "erased" },
    "Array.swap second bounds proof must be erased");
  const source = args[1];
  const array = host.arrayInfo(source);
  const index = naturalValue(host, args[2], "Array.swap first index");
  const index2 = naturalValue(host, args[3], "Array.swap second index");
  assert.ok(index < BigInt(array.size) && index2 < BigInt(array.size),
    "Array.swap indices must be in bounds");
  const first = Number(index);
  const second = Number(index2);
  const swapped = [...array.elements];
  [swapped[first], swapped[second]] = [swapped[second], swapped[first]];
  if (!array.header.persistent && array.header.rc === 1) {
    host.writeArrayElement(source, first, swapped[first]);
    host.writeArrayElement(source, second, swapped[second]);
    return { value: source, world };
  }
  swapped.forEach(element => host.retainValue(element));
  if (!array.header.persistent) host.releaseValue(source);
  return { value: host.allocateArray(swapped, array.capacity), world };
}

function mkArray({ args, host, world }) {
  assert.equal(args.length, 2, "Array.mk external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.mk type argument must be erased");
  const list = args[1];
  const elements = host.listElements(list);
  elements.forEach(element => host.retainValue(element));
  host.releaseValue(list);
  return { value: host.allocateArray(elements, elements.length), world };
}

function toListArray({ args, host, world }) {
  assert.equal(args.length, 2, "Array.toList external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.toList type argument must be erased");
  const source = args[1];
  const elements = host.arrayInfo(source).elements;
  elements.forEach(element => host.retainValue(element));
  const list = host.allocateList(elements);
  host.releaseValue(source);
  return { value: list, world };
}

/**
 * Validation-only externals layered over the ordinary concrete artifact
 * registry. Generic Array operations use the same opaque/ARRY layout as the
 * resident implementation. ByteArray declarations stay absent until their
 * physical layout is implemented, so that gate still fails closed before
 * instantiation.
 */
export const concreteValidationExternalRegistry = Object.freeze({
  ...concreteArtifactExternalRegistry,
  ...concreteFloatExternalRegistry,
  "Nat.mul": naturalBinary("Nat.mul", (left, right) => left * right),
  "Nat.div": naturalBinary("Nat.div", naturalDivision),
  "Nat.mod": naturalBinary("Nat.mod", naturalRemainder),
  "Nat.land": naturalBinary("Nat.land", (left, right) => left & right),
  "Nat.lor": naturalBinary("Nat.lor", (left, right) => left | right),
  "Nat.xor": naturalBinary("Nat.xor", (left, right) => left ^ right),
  "Nat.shiftLeft": naturalBinary("Nat.shiftLeft", (value, count) => value << count),
  "Nat.shiftRight": naturalBinary("Nat.shiftRight", naturalShiftRight),
  "String.decEq":
    stringBinaryUInt8("String.decEq",
      (left, right) => stringCompare(left, right) === 1n ? 1n : 0n),
  "String.decidableLT":
    stringBinaryUInt8("String.decidableLT",
      (left, right) => stringCompare(left, right) === 0n ? 1n : 0n),
  "String.compare": stringBinaryUInt8("String.compare", stringCompare),
  "instInhabitedUInt8": inhabitedUInt8,
  "instInhabitedFloat": ({ args, world }) => {
    assert.equal(args.length, 0, "instInhabitedFloat external arity mismatch");
    return {
      value: { kind: "scalar", scalarKind: "float", value: 0n },
      world,
    };
  },
  "Array.get!Internal": getArrayBang,
  "Array.get!InternalBorrowed": getArrayBangBorrowed,
  "Array.set!": setArray,
  "Array.size": sizeArray,
  "Array.push": pushArray,
  "Array.pop": popArray,
  "Array.replicate": replicateArray,
  "Array.swap": swapArray,
  "Array.mk": mkArray,
  "Array.toList": toListArray,
  "Int.neg": ({ args, host, world }) => {
    assert.equal(args.length, 1, "Int.neg external arity mismatch");
    const value = integerValue(host, args[0], "Int.neg operand");
    return { value: integerResult(host, -value), world };
  },
  "Int.mul": integerBinary("Int.mul", (left, right) => left * right),
  "Int.ediv": integerBinary("Int.ediv", euclideanDivision),
  "Int.emod": integerBinary("Int.emod", euclideanRemainder),
  "Int.shiftLeft": integerNaturalBinary(
    "Int.shiftLeft", (value, count) => value << count),
  "Int.shiftRight": integerNaturalBinary("Int.shiftRight", integerShiftRight),
  "Int.decEq": integerDecision("Int.decEq", (left, right) => left === right),
  "Int.decLe": integerDecision("Int.decLe", (left, right) => left <= right),
  ...signedFixedWidthExternalFamily("Int8", 8, signedFixedWidthCodecs.Int8),
  "Int8.ofNat": naturalToFixedWidth("Int8.ofNat", signedFixedWidthCodecs.Int8),
  "Int8.ofInt": integerToFixedWidth("Int8.ofInt", signedFixedWidthCodecs.Int8),
  "Int8.toInt": fixedWidthToInteger("Int8.toInt", signedFixedWidthCodecs.Int8),
  ...signedFixedWidthConversionFamily("Int8"),
  ...signedFixedWidthExternalFamily("Int16", 16, signedFixedWidthCodecs.Int16),
  "Int16.ofNat": naturalToFixedWidth(
    "Int16.ofNat", signedFixedWidthCodecs.Int16),
  "Int16.ofInt": integerToFixedWidth(
    "Int16.ofInt", signedFixedWidthCodecs.Int16),
  "Int16.toInt": fixedWidthToInteger(
    "Int16.toInt", signedFixedWidthCodecs.Int16),
  ...signedFixedWidthConversionFamily("Int16"),
  ...signedFixedWidthExternalFamily("Int32", 32, signedFixedWidthCodecs.Int32),
  "Int32.ofNat": naturalToFixedWidth(
    "Int32.ofNat", signedFixedWidthCodecs.Int32),
  "Int32.ofInt": integerToFixedWidth(
    "Int32.ofInt", signedFixedWidthCodecs.Int32),
  "Int32.toInt": fixedWidthToInteger(
    "Int32.toInt", signedFixedWidthCodecs.Int32),
  ...signedFixedWidthConversionFamily("Int32"),
  ...signedFixedWidthExternalFamily("Int64", 64, signedFixedWidthCodecs.Int64),
  "Int64.ofNat": naturalToFixedWidth(
    "Int64.ofNat", signedFixedWidthCodecs.Int64),
  "Int64.ofInt": integerToFixedWidth(
    "Int64.ofInt", signedFixedWidthCodecs.Int64),
  "Int64.toInt": fixedWidthToInteger(
    "Int64.toInt", signedFixedWidthCodecs.Int64),
  ...signedFixedWidthConversionFamily("Int64"),
  ...signedFixedWidthExternalFamily("ISize", 64, signedFixedWidthCodecs.ISize),
  "ISize.ofNat": naturalToFixedWidth(
    "ISize.ofNat", signedFixedWidthCodecs.ISize),
  "ISize.ofInt": integerToFixedWidth(
    "ISize.ofInt", signedFixedWidthCodecs.ISize),
  "ISize.toInt": fixedWidthToInteger(
    "ISize.toInt", signedFixedWidthCodecs.ISize),
  ...signedFixedWidthConversionFamily("ISize"),
  ...fixedWidthExternalFamily("UInt8", "uint8", 8),
  "UInt8.ofNat": naturalToFixedWidth("UInt8.ofNat", fixedWidthCodecs.UInt8),
  "UInt8.toNat": fixedWidthToNatural("UInt8.toNat", fixedWidthCodecs.UInt8),
  ...fixedWidthConversionFamily("UInt8"),
  ...fixedWidthExternalFamily("UInt16", "uint16", 16),
  "UInt16.ofNat": naturalToFixedWidth("UInt16.ofNat", fixedWidthCodecs.UInt16),
  "UInt16.toNat": fixedWidthToNatural("UInt16.toNat", fixedWidthCodecs.UInt16),
  ...fixedWidthConversionFamily("UInt16"),
  ...fixedWidthExternalFamily("UInt32", "uint32", 32),
  "UInt32.ofNat": naturalToFixedWidth("UInt32.ofNat", fixedWidthCodecs.UInt32),
  "UInt32.toNat": fixedWidthToNatural("UInt32.toNat", fixedWidthCodecs.UInt32),
  ...fixedWidthConversionFamily("UInt32"),
  ...fixedWidthExternalFamily("UInt64", "uint64", 64),
  "UInt64.ofNat": naturalToFixedWidth("UInt64.ofNat", fixedWidthCodecs.UInt64),
  "UInt64.toNat": fixedWidthToNatural("UInt64.toNat", fixedWidthCodecs.UInt64),
  ...fixedWidthConversionFamily("UInt64"),
  ...codecFixedWidthExternalFamily("USize", 64, usizeFixedWidthCodec),
  "USize.ofNat": naturalToFixedWidth("USize.ofNat", usizeFixedWidthCodec),
  "USize.toNat": fixedWidthToNatural("USize.toNat", usizeFixedWidthCodec),
  ...fixedWidthConversionFamily("USize"),
  "Fir.Validation.Corpus.NativeEffects.recordImpl": ({ args, host, world }) => {
    assert.equal(args.length, 1, "validation.record external arity mismatch");
    const argument = naturalValue(host, args[0], "validation.record operand");
    const result = argument + 1n;
    recordEffect(host, "validation.record", argument, result);
    return { value: naturalResult(host, result), world: world + 1 };
  },
});
