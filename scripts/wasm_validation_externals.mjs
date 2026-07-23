import assert from "./wasm_assert.mjs";

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
