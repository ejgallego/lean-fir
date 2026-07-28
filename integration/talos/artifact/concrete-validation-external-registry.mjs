import assert from "../../../scripts/wasm_assert.mjs";
import {
  stringCompare,
} from "../../../scripts/wasm_format_external_algorithms.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";

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

/**
 * Validation-only externals layered over the ordinary concrete artifact
 * registry. ByteArray declarations stay absent until their physical layout is
 * implemented; the product gate therefore fails closed before instantiation.
 */
export const concreteValidationExternalRegistry = Object.freeze({
  ...concreteArtifactExternalRegistry,
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
  ...fixedWidthExternalFamily("UInt8", "uint8", 8),
  ...fixedWidthExternalFamily("UInt16", "uint16", 16),
  ...fixedWidthExternalFamily("UInt32", "uint32", 32),
  ...fixedWidthExternalFamily("UInt64", "uint64", 64),
  "Fir.Validation.Corpus.NativeEffects.recordImpl": ({ args, host, world }) => {
    assert.equal(args.length, 1, "validation.record external arity mismatch");
    const argument = naturalValue(host, args[0], "validation.record operand");
    const result = argument + 1n;
    recordEffect(host, "validation.record", argument, result);
    return { value: naturalResult(host, result), world: world + 1 };
  },
});
