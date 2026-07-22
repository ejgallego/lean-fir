import assert from "../../../scripts/wasm_assert.mjs";
import {
  stringAppend,
  stringExtract,
  stringLength,
  stringNext,
  stringOffsetOfPos,
  stringPosOf,
  stringPushn,
  stringUtf8ByteSize,
} from "../../../scripts/wasm_format_external_algorithms.mjs";

import { ConcreteFault } from "./concrete-host.mjs";

function naturalValue(host, value, context) {
  if (value.kind === "tagged") return value.payload;
  assert.equal(value.kind, "heap", `${context} must be a tagged or heap natural`);
  const address = host.addressOf(value.location);
  return host.readNatural(address);
}

function naturalResult(host, value) {
  const natural = BigInt(value);
  assert.ok(natural >= 0n, "concrete natural result must be nonnegative");
  return host.decode("tobject", host.allocateNatural(natural));
}

function stringValue(host, value, context) {
  assert.equal(value.kind, "heap", `${context} must be a heap string`);
  const address = host.addressOf(value.location);
  return host.readString(address);
}

function stringResult(host, value) {
  return host.decode("object", host.allocateString(value));
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
  throw new ConcreteFault({
    kind: "externalFailure",
    name: declaration,
    message: "unreachable Lean pretty-printing panic helper executed",
  });
}

export const concreteFormatExternalRegistry = Object.freeze({
  "Nat.add": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.add external arity mismatch");
    const left = naturalValue(host, args[0], "Nat.add left operand");
    const right = naturalValue(host, args[1], "Nat.add right operand");
    return { value: naturalResult(host, left + right), world };
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
  "Nat.sub": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.sub external arity mismatch");
    const left = naturalValue(host, args[0], "Nat.sub left operand");
    const right = naturalValue(host, args[1], "Nat.sub right operand");
    return { value: naturalResult(host, left < right ? 0n : left - right), world };
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
    return { value: naturalResult(host, stringLength(source)), world };
  },
  "String.Internal.posOf": ({ args, host, world }) => {
    assert.equal(args.length, 2, "String.Internal.posOf external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.posOf source");
    const codePoint = scalarUInt32(args[1], "String.Internal.posOf character");
    return { value: naturalResult(host, stringPosOf(source, codePoint)), world };
  },
  "String.Internal.offsetOfPos": ({ args, host, world }) => {
    assert.equal(args.length, 2, "String.Internal.offsetOfPos external arity mismatch");
    const source = stringValue(host, args[0], "String.Internal.offsetOfPos source");
    const position = naturalValue(host, args[1], "String.Internal.offsetOfPos position");
    return { value: naturalResult(host, stringOffsetOfPos(source, position)), world };
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
    return { value: naturalResult(host, stringNext(source, position)), world };
  },
  panicCore: unreachablePanicHelper,
  "instInhabitedOfMonad._redArg": unreachablePanicHelper,
});
