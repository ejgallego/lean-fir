import assert from "./wasm_assert.mjs";
import {
  stringAppend,
  stringCompare,
  stringExtract,
  stringLength,
  stringNext,
  stringOffsetOfPos,
  stringPosOf,
  stringPushn,
  stringUtf8ByteSize,
} from "./wasm_format_external_algorithms.mjs";

export function naturalValue(host, value, context) {
  if (value.kind === "tagged") {
    return value.payload;
  }
  assert.equal(value.kind, "heap", `${context} must be a tagged or heap natural`);
  const object = host.liveCell(value.location).object;
  assert.equal(object.kind, "natural", `${context} heap object must be a natural`);
  return object.value;
}

export function integerValue(host, value, context) {
  if (value.kind === "tagged") {
    assert.ok(value.payload >= 0n && value.payload <= 0xffffffffn,
      `${context} immediate integer payload is out of range`);
    return BigInt.asIntN(32, value.payload);
  }
  assert.equal(value.kind, "heap", `${context} must be a tagged or heap integer`);
  const object = host.liveCell(value.location).object;
  assert.equal(object.kind, "integer", `${context} heap object must be an integer`);
  return object.value;
}

export function byteArrayValue(host, value, context) {
  assert.equal(value.kind, "heap", `${context} must be a heap byte array`);
  const object = host.liveCell(value.location).object;
  assert.equal(object.kind, "byteArray", `${context} heap object must be a byte array`);
  return object.value;
}

export function stringValue(host, value, context) {
  assert.equal(value.kind, "heap", `${context} must be a heap string`);
  const object = host.liveCell(value.location).object;
  assert.equal(object.kind, "string", `${context} heap object must be a string`);
  return object.value;
}

export function scalarUInt32(value, context) {
  assert.equal(value.kind, "scalar", `${context} must be a scalar`);
  assert.equal(value.scalarKind, "uint32", `${context} must use UInt32`);
  assert.ok(value.value >= 0n && value.value <= 0xffffffffn,
    `${context} is out of UInt32 range`);
  return value.value;
}

function boolResult(value) {
  return { kind: "scalar", scalarKind: "uint8", value: value ? 1n : 0n };
}

function naturalDecision(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = naturalValue(host, args[0], `${declaration} left operand`);
    const right = naturalValue(host, args[1], `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
  };
}

function naturalBinary(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = naturalValue(host, args[0], `${declaration} left operand`);
    const right = naturalValue(host, args[1], `${declaration} right operand`);
    return { value: host.natural(operation(left, right)), world };
  };
}

function integerBinary(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = integerValue(host, args[0], `${declaration} left operand`);
    const right = integerValue(host, args[1], `${declaration} right operand`);
    return { value: host.integer(operation(left, right)), world };
  };
}

function integerNaturalBinary(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const value = integerValue(host, args[0], `${declaration} value`);
    const count = naturalValue(host, args[1], `${declaration} count`);
    return { value: host.integer(operation(value, count)), world };
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

function uint32Result(value) {
  return {
    kind: "scalar",
    scalarKind: "uint32",
    value: BigInt.asUintN(32, value),
  };
}

function uint32Binary(declaration, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = scalarUInt32(args[0], `${declaration} left operand`);
    const right = scalarUInt32(args[1], `${declaration} right operand`);
    return { value: uint32Result(operation(left, right)), world };
  };
}

function uint32Unary(declaration, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = scalarUInt32(args[0], `${declaration} operand`);
    return { value: uint32Result(operation(value)), world };
  };
}

function uint32Decision(declaration, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = scalarUInt32(args[0], `${declaration} left operand`);
    const right = scalarUInt32(args[1], `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
  };
}

function naturalDivision(left, right) {
  return right === 0n ? 0n : left / right;
}

function naturalRemainder(left, right) {
  return right === 0n ? left : left % right;
}

function naturalShiftRight(value, count) {
  if (value === 0n || count >= BigInt(value.toString(2).length)) {
    return 0n;
  }
  return value >> count;
}

function integerShiftRight(value, count) {
  if (value >= 0n) {
    return naturalShiftRight(value, count);
  }
  return -1n - naturalShiftRight(-1n - value, count);
}

function euclideanRemainder(left, right) {
  if (right === 0n) {
    return left;
  }
  const modulus = right < 0n ? -right : right;
  const remainder = left % modulus;
  return remainder < 0n ? remainder + modulus : remainder;
}

function euclideanDivision(left, right) {
  if (right === 0n) {
    return 0n;
  }
  return (left - euclideanRemainder(left, right)) / right;
}

function stringMeasurement(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const source = stringValue(host, args[0], `${declaration} source`);
    return { value: host.natural(operation(source)), world };
  };
}

function stringCharToNatural(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const source = stringValue(host, args[0], `${declaration} source`);
    const codePoint = scalarUInt32(args[1], `${declaration} character`);
    return { value: host.natural(operation(source, codePoint)), world };
  };
}

function stringNaturalToNatural(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const source = stringValue(host, args[0], `${declaration} source`);
    const position = naturalValue(host, args[1], `${declaration} position`);
    return { value: host.natural(operation(source, position)), world };
  };
}

function stringExtractExternal({ args, host, world }) {
  assert.equal(args.length, 3, "String.Internal.extract external arity mismatch");
  const source = stringValue(host, args[0], "String.Internal.extract source");
  const begin = naturalValue(host, args[1], "String.Internal.extract begin");
  const end = naturalValue(host, args[2], "String.Internal.extract end");
  return {
    value: host.alloc({ kind: "string", value: stringExtract(source, begin, end) }),
    world,
  };
}

function consumingStringResult(host, source, result, context) {
  assert.equal(source.kind, "heap", `${context} source must be a heap string`);
  const cell = host.liveCell(source.location);
  assert.equal(cell.object.kind, "string", `${context} source must be a string`);
  if (!cell.persistent && cell.rc === 1) {
    cell.object = { kind: "string", value: result };
    return source;
  }
  host.decLocation(source.location);
  return host.alloc({ kind: "string", value: result });
}

function stringAppendExternal({ args, host, world }) {
  assert.equal(args.length, 2, "String.Internal.append external arity mismatch");
  const left = stringValue(host, args[0], "String.Internal.append left operand");
  const right = stringValue(host, args[1], "String.Internal.append right operand");
  return {
    value: consumingStringResult(
      host, args[0], stringAppend(left, right), "String.Internal.append"),
    world,
  };
}

function stringPushnExternal({ args, host, world }) {
  assert.equal(args.length, 3, "String.Internal.pushn external arity mismatch");
  const source = stringValue(host, args[0], "String.Internal.pushn source");
  const codePoint = scalarUInt32(args[1], "String.Internal.pushn character");
  const count = naturalValue(host, args[2], "String.Internal.pushn count");
  if (count === 0n) {
    return { value: args[0], world };
  }
  return {
    value: consumingStringResult(
      host, args[0], stringPushn(source, codePoint, count), "String.Internal.pushn"),
    world,
  };
}

function stringBinaryUInt8(declaration, operation) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = stringValue(host, args[0], `${declaration} left operand`);
    const right = stringValue(host, args[1], `${declaration} right operand`);
    return {
      value: {
        kind: "scalar",
        scalarKind: "uint8",
        value: operation(left, right),
      },
      world,
    };
  };
}

function setByteArray({ args, host, world }) {
  assert.equal(args.length, 3, "ByteArray.set! external arity mismatch");
  const source = args[0];
  assert.equal(source.kind, "heap", "ByteArray.set! operand must be a heap byte array");
  const cell = host.liveCell(source.location);
  assert.equal(cell.object.kind, "byteArray",
    "ByteArray.set! heap object must be a byte array");
  const index = naturalValue(host, args[1], "ByteArray.set! index");
  const byte = args[2];
  assert.equal(byte.kind, "scalar", "ByteArray.set! byte must be a scalar");
  assert.equal(byte.scalarKind, "uint8", "ByteArray.set! byte must use UInt8");
  assert.ok(byte.value >= 0n && byte.value <= 0xffn,
    "ByteArray.set! byte is out of range");
  if (index >= BigInt(cell.object.value.length)) {
    return { value: source, world };
  }
  const bytes = [...cell.object.value];
  bytes[Number(index)] = Number(byte.value);
  if (!cell.persistent && cell.rc === 1) {
    cell.object = { kind: "byteArray", value: bytes };
    return { value: source, world };
  }
  if (!cell.persistent) {
    host.decLocation(source.location);
  }
  return { value: host.alloc({ kind: "byteArray", value: bytes }), world };
}

export const validationExternalRegistry = {
  "Nat.add": naturalBinary("Nat.add", (left, right) => left + right),
  "Nat.sub": naturalBinary(
    "Nat.sub", (left, right) => left < right ? 0n : left - right),
  "Nat.mul": naturalBinary("Nat.mul", (left, right) => left * right),
  "Nat.div": naturalBinary("Nat.div", naturalDivision),
  "Nat.mod": naturalBinary("Nat.mod", naturalRemainder),
  "Nat.land": naturalBinary("Nat.land", (left, right) => left & right),
  "Nat.lor": naturalBinary("Nat.lor", (left, right) => left | right),
  "Nat.xor": naturalBinary("Nat.xor", (left, right) => left ^ right),
  "Nat.shiftLeft": naturalBinary(
    "Nat.shiftLeft", (value, count) => value << count),
  "Nat.shiftRight": naturalBinary("Nat.shiftRight", naturalShiftRight),
  "Nat.decEq": naturalDecision("Nat.decEq", (left, right) => left === right),
  "Nat.decLt": naturalDecision("Nat.decLt", (left, right) => left < right),
  "Nat.decLe": naturalDecision("Nat.decLe", (left, right) => left <= right),
  "String.Internal.length":
    stringMeasurement("String.Internal.length", stringLength),
  "String.utf8ByteSize":
    stringMeasurement("String.utf8ByteSize", stringUtf8ByteSize),
  "String.Internal.posOf":
    stringCharToNatural("String.Internal.posOf", stringPosOf),
  "String.Internal.offsetOfPos":
    stringNaturalToNatural("String.Internal.offsetOfPos", stringOffsetOfPos),
  "String.Internal.next":
    stringNaturalToNatural("String.Internal.next", stringNext),
  "String.Internal.extract": stringExtractExternal,
  "String.Internal.append": stringAppendExternal,
  "String.Internal.pushn": stringPushnExternal,
  "String.decEq":
    stringBinaryUInt8("String.decEq",
      (left, right) => stringCompare(left, right) === 1n ? 1n : 0n),
  "String.decidableLT":
    stringBinaryUInt8("String.decidableLT",
      (left, right) => stringCompare(left, right) === 0n ? 1n : 0n),
  "String.compare": stringBinaryUInt8("String.compare", stringCompare),
  "Int.ofNat": ({ args, host, world }) => {
    assert.equal(args.length, 1, "Int.ofNat external arity mismatch");
    const value = naturalValue(host, args[0], "Int.ofNat operand");
    return { value: host.integer(value), world };
  },
  "Int.neg": ({ args, host, world }) => {
    assert.equal(args.length, 1, "Int.neg external arity mismatch");
    const value = integerValue(host, args[0], "Int.neg operand");
    return { value: host.integer(-value), world };
  },
  "Int.natAbs": ({ args, host, world }) => {
    assert.equal(args.length, 1, "Int.natAbs external arity mismatch");
    const value = integerValue(host, args[0], "Int.natAbs operand");
    return { value: host.natural(value < 0n ? -value : value), world };
  },
  "Int.add": integerBinary("Int.add", (left, right) => left + right),
  "Int.sub": integerBinary("Int.sub", (left, right) => left - right),
  "Int.mul": integerBinary("Int.mul", (left, right) => left * right),
  "Int.ediv": integerBinary("Int.ediv", euclideanDivision),
  "Int.emod": integerBinary("Int.emod", euclideanRemainder),
  "Int.shiftLeft": integerNaturalBinary(
    "Int.shiftLeft", (value, count) => value << count),
  "Int.shiftRight": integerNaturalBinary("Int.shiftRight", integerShiftRight),
  "Int.decEq": integerDecision("Int.decEq", (left, right) => left === right),
  "Int.decLt": integerDecision("Int.decLt", (left, right) => left < right),
  "Int.decLe": integerDecision("Int.decLe", (left, right) => left <= right),
  "UInt32.add": uint32Binary("UInt32.add", (left, right) => left + right),
  "UInt32.sub": uint32Binary("UInt32.sub", (left, right) => left - right),
  "UInt32.mul": uint32Binary("UInt32.mul", (left, right) => left * right),
  "UInt32.div": uint32Binary(
    "UInt32.div", (left, right) => right === 0n ? 0n : left / right),
  "UInt32.mod": uint32Binary(
    "UInt32.mod", (left, right) => right === 0n ? left : left % right),
  "UInt32.land": uint32Binary("UInt32.land", (left, right) => left & right),
  "UInt32.lor": uint32Binary("UInt32.lor", (left, right) => left | right),
  "UInt32.xor": uint32Binary("UInt32.xor", (left, right) => left ^ right),
  "UInt32.shiftLeft": uint32Binary(
    "UInt32.shiftLeft", (value, count) => value << (count & 31n)),
  "UInt32.shiftRight": uint32Binary(
    "UInt32.shiftRight", (value, count) => value >> (count & 31n)),
  "UInt32.complement": uint32Unary("UInt32.complement", value => ~value),
  "UInt32.neg": uint32Unary("UInt32.neg", value => -value),
  "UInt32.decEq": uint32Decision(
    "UInt32.decEq", (left, right) => left === right),
  "UInt32.decLt": uint32Decision(
    "UInt32.decLt", (left, right) => left < right),
  "UInt32.decLe": uint32Decision(
    "UInt32.decLe", (left, right) => left <= right),
  "ByteArray.size": ({ args, host, world }) => {
    assert.equal(args.length, 1, "ByteArray.size external arity mismatch");
    const bytes = byteArrayValue(host, args[0], "ByteArray.size operand");
    return { value: host.natural(BigInt(bytes.length)), world };
  },
  "ByteArray.get!": ({ args, host, world }) => {
    assert.equal(args.length, 2, "ByteArray.get! external arity mismatch");
    const bytes = byteArrayValue(host, args[0], "ByteArray.get! operand");
    const index = naturalValue(host, args[1], "ByteArray.get! index");
    const value = index < BigInt(bytes.length)
      ? BigInt(bytes[Number(index)])
      : 0n;
    return {
      value: {
        kind: "scalar",
        scalarKind: "uint8",
        value,
      },
      world,
    };
  },
  "ByteArray.set!": setByteArray,
  "Fir.Validation.Corpus.NativeEffects.recordImpl": ({ args, host, world }) => {
    assert.equal(args.length, 1, "validation.record external arity mismatch");
    const value = naturalValue(host, args[0], "validation.record operand");
    return { value: host.natural(value + 1n), world: world + 1 };
  },
  "Fir.Validation.Corpus.NativeEffects.recordByteArrayImpl": ({ args, host, world }) => {
    assert.equal(args.length, 2, "validation.recordByteArray external arity mismatch");
    const response = setByteArray({
      args: [args[0], host.natural(0n), args[1]],
      host,
      world,
    });
    return { value: response.value, world: response.world + 1 };
  },
};
