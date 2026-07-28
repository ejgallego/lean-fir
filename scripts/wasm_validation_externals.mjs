import assert from "./wasm_assert.mjs";
import {
  stringLength,
  stringNext,
  stringOffsetOfPos,
  stringPosOf,
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
  "Nat.add": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.add external arity mismatch");
    const left = naturalValue(host, args[0], "Nat.add left operand");
    const right = naturalValue(host, args[1], "Nat.add right operand");
    return { value: host.natural(left + right), world };
  },
  "Nat.sub": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Nat.sub external arity mismatch");
    const left = naturalValue(host, args[0], "Nat.sub left operand");
    const right = naturalValue(host, args[1], "Nat.sub right operand");
    return { value: host.natural(left < right ? 0n : left - right), world };
  },
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
  "Int.add": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Int.add external arity mismatch");
    const left = integerValue(host, args[0], "Int.add left operand");
    const right = integerValue(host, args[1], "Int.add right operand");
    return { value: host.integer(left + right), world };
  },
  "Int.sub": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Int.sub external arity mismatch");
    const left = integerValue(host, args[0], "Int.sub left operand");
    const right = integerValue(host, args[1], "Int.sub right operand");
    return { value: host.integer(left - right), world };
  },
  "Int.decLt": ({ args, host, world }) => {
    assert.equal(args.length, 2, "Int.decLt external arity mismatch");
    const left = integerValue(host, args[0], "Int.decLt left operand");
    const right = integerValue(host, args[1], "Int.decLt right operand");
    return {
      value: {
        kind: "scalar",
        scalarKind: "uint8",
        value: left < right ? 1n : 0n,
      },
      world,
    };
  },
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
