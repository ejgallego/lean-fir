import assert from "./wasm_assert.mjs";

import {
  integerValue,
  naturalValue,
  validationExternalRegistry,
} from "./wasm_validation_externals.mjs";
import {
  stringAppend,
  stringExtract,
  stringLength,
  stringNext,
  stringOffsetOfPos,
  stringPosOf,
  stringPushn,
  stringUtf8ByteSize,
} from "./wasm_format_external_algorithms.mjs";

function stringValue(host, value, context) {
  assert.equal(value.kind, "heap", `${context} must be a heap string`);
  const object = host.liveCell(value.location).object;
  assert.equal(object.kind, "string", `${context} heap object must be a string`);
  return object.value;
}

function stringResult(host, value) {
  return host.alloc({ kind: "string", value });
}

function scalarUInt32(value, context) {
  assert.equal(value.kind, "scalar", `${context} must be a scalar`);
  assert.equal(value.scalarKind, "uint32", `${context} must use UInt32`);
  return value.value;
}

function boolResult(value) {
  return { kind: "scalar", scalarKind: "uint8", value: value ? 1n : 0n };
}

function unreachablePanicHelper({ declaration }) {
  throw new Error(`unreachable Lean pretty-printing panic helper executed: ${declaration}`);
}

export const formatExternalRegistry = {
  ...validationExternalRegistry,
  "Int.natAbs": ({ args, host, world }) => {
    assert.equal(args.length, 1, "Int.natAbs external arity mismatch");
    const value = integerValue(host, args[0], "Int.natAbs operand");
    return { value: host.natural(value < 0n ? -value : value), world };
  },
  "Int.sub": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Int.sub external arity mismatch");
    const left = integerValue(host, args[0], "Int.sub left operand");
    const right = integerValue(host, args[1], "Int.sub right operand");
    return { value: host.integer(left - right), world };
  },
  "Int.add": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Int.add external arity mismatch");
    const left = integerValue(host, args[0], "Int.add left operand");
    const right = integerValue(host, args[1], "Int.add right operand");
    return { value: host.integer(left + right), world };
  },
  "Nat.decEq": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.decEq external arity mismatch");
    return {
      value: boolResult(
        naturalValue(host, args[0], "Nat.decEq left operand") ===
          naturalValue(host, args[1], "Nat.decEq right operand")),
      world,
    };
  },
  "Nat.decLt": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.decLt external arity mismatch");
    return {
      value: boolResult(
        naturalValue(host, args[0], "Nat.decLt left operand") <
          naturalValue(host, args[1], "Nat.decLt right operand")),
      world,
    };
  },
  "Nat.decLe": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.decLe external arity mismatch");
    return {
      value: boolResult(
        naturalValue(host, args[0], "Nat.decLe left operand") <=
          naturalValue(host, args[1], "Nat.decLe right operand")),
      world,
    };
  },
  "String.Internal.append": ({ args, host, world }) => {
    assert.equal(args.length, 2, "String.Internal.append external arity mismatch");
    const left = stringValue(host, args[0], "String.Internal.append left operand");
    const right = stringValue(host, args[1], "String.Internal.append right operand");
    return { value: stringResult(host, stringAppend(left, right)), world };
  },
  "String.Internal.pushn": ({ args, host, world }) => {
    assert.equal(args.length, 3, "String.Internal.pushn external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.pushn source");
    const codePoint = scalarUInt32(args[1], "String.Internal.pushn character");
    const count = naturalValue(host, args[2], "String.Internal.pushn count");
    return { value: stringResult(host, stringPushn(source, codePoint, count)), world };
  },
  "String.Internal.length": ({ args, host, world }) => {
    assert.equal(args.length, 1, "String.Internal.length external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.length source");
    return { value: host.natural(stringLength(source)), world };
  },
  "String.Internal.posOf": ({ args, host, world }) => {
    assert.equal(args.length, 2, "String.Internal.posOf external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.posOf source");
    const codePoint = scalarUInt32(args[1], "String.Internal.posOf character");
    return { value: host.natural(stringPosOf(source, codePoint)), world };
  },
  "String.Internal.offsetOfPos": ({ args, host, world }) => {
    assert.equal(args.length, 2, "String.Internal.offsetOfPos external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.offsetOfPos source");
    const position = naturalValue(host, args[1], "String.Internal.offsetOfPos position");
    return { value: host.natural(stringOffsetOfPos(source, position)), world };
  },
  "String.utf8ByteSize": ({ args, host, world }) => {
    assert.equal(args.length, 1, "String.utf8ByteSize external arity mismatch");
    const source = stringValue(host, args[0], "String.utf8ByteSize source");
    return { value: { kind: "tagged", payload: stringUtf8ByteSize(source) }, world };
  },
  "String.Internal.extract": ({ args, host, world }) => {
    assert.equal(args.length, 3, "String.Internal.extract external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.extract source");
    const begin = naturalValue(host, args[1], "String.Internal.extract begin");
    const end = naturalValue(host, args[2], "String.Internal.extract end");
    return { value: stringResult(host, stringExtract(source, begin, end)), world };
  },
  "String.Internal.next": ({ args, host, world }) => {
    assert.equal(args.length, 2, "String.Internal.next external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.next source");
    const position = naturalValue(host, args[1], "String.Internal.next position");
    return { value: host.natural(stringNext(source, position)), world };
  },
  panicCore: unreachablePanicHelper,
  "instInhabitedOfMonad._redArg": unreachablePanicHelper,
};
