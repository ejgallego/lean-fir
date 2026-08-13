import assert from "./wasm_assert.mjs";
import {
  float32FromBits,
  float32ToBits,
  float64FromBits,
  float64ToBits,
} from "./wasm_semantic_host.mjs";
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

function fixedWidthScalar(value, scalarKind, width, context) {
  assert.equal(value.kind, "scalar", `${context} must be a scalar`);
  assert.equal(value.scalarKind, scalarKind,
    `${context} must use ${scalarKind}`);
  assert.ok(value.value >= 0n && value.value < (1n << BigInt(width)),
    `${context} is out of ${scalarKind} range`);
  return value.value;
}

export function scalarUInt8(value, context) {
  return fixedWidthScalar(value, "uint8", 8, context);
}

export function scalarUInt16(value, context) {
  return fixedWidthScalar(value, "uint16", 16, context);
}

export function scalarUInt32(value, context) {
  return fixedWidthScalar(value, "uint32", 32, context);
}

export function scalarUInt64(value, context) {
  return fixedWidthScalar(value, "uint64", 64, context);
}

export function scalarFloat32Bits(value, context) {
  return fixedWidthScalar(value, "float32", 32, context);
}

export function scalarFloat64Bits(value, context) {
  return fixedWidthScalar(value, "float", 64, context);
}

export function semanticUSize(value, context) {
  assert.equal(value.kind, "usize", `${context} must be a USize`);
  assert.ok(value.value >= 0n && value.value < (1n << 64n),
    `${context} is out of USize range`);
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

function scalarFixedWidthCodec(scalarKind, width) {
  return {
    decode: (value, context) =>
      fixedWidthScalar(value, scalarKind, width, context),
    encode: value => ({
      kind: "scalar",
      scalarKind,
      value: BigInt.asUintN(width, value),
    }),
  };
}

function signedFixedWidthCodec(unsigned, width) {
  return {
    decode: (value, context) =>
      BigInt.asIntN(width, unsigned.decode(value, context)),
    encode: value => unsigned.encode(BigInt.asUintN(width, value)),
  };
}

function signedScalarFixedWidthCodec(scalarKind, width) {
  return signedFixedWidthCodec(
    scalarFixedWidthCodec(scalarKind, width), width);
}

const usizeFixedWidthCodec = {
  decode: semanticUSize,
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

function fixedWidthBinary(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = codec.decode(args[0], `${declaration} left operand`);
    const right = codec.decode(args[1], `${declaration} right operand`);
    return {
      value: codec.encode(operation(left, right)),
      world,
    };
  };
}

function fixedWidthUnary(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = codec.decode(args[0], `${declaration} operand`);
    return {
      value: codec.encode(operation(value)),
      world,
    };
  };
}

function fixedWidthDecision(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = codec.decode(args[0], `${declaration} left operand`);
    const right = codec.decode(args[1], `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
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
    return { value: host.natural(value), world };
  };
}

function fixedWidthToInteger(declaration, codec) {
  return ({ args, host, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = codec.decode(args[0], `${declaration} operand`);
    return { value: host.integer(value), world };
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

function fixedWidthExternalFamily(typeName, width, codec) {
  const declaration = suffix => `${typeName}.${suffix}`;
  const binary = (suffix, operation) =>
    fixedWidthBinary(declaration(suffix), codec, operation);
  const unary = (suffix, operation) =>
    fixedWidthUnary(declaration(suffix), codec, operation);
  const decision = (suffix, operation) =>
    fixedWidthDecision(declaration(suffix), codec, operation);
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
    [declaration("decEq")]: decision(
      "decEq", (left, right) => left === right),
    [declaration("decLt")]: decision("decLt", (left, right) => left < right),
    [declaration("decLe")]: decision("decLe", (left, right) => left <= right),
  };
}

function floatCodec(
  scalarKind,
  width,
  fromBits,
  toBits,
  round,
  canonicalNaNBits,
) {
  return {
    decodeBits: (value, context) =>
      fixedWidthScalar(value, scalarKind, width, context),
    encodeBits: bits => ({
      kind: "scalar",
      scalarKind,
      value: BigInt.asUintN(width, bits),
    }),
    decode(value, context) {
      return fromBits(this.decodeBits(value, context));
    },
    encode(value) {
      if (Number.isNaN(value)) {
        return this.encodeBits(canonicalNaNBits);
      }
      return this.encodeBits(toBits(round(value)));
    },
  };
}

const float32Codec = floatCodec(
  "float32", 32, float32FromBits, float32ToBits, Math.fround, 0x7fc00000n);
const float64Codec = floatCodec(
  "float", 64, float64FromBits, float64ToBits, value => value,
  0x7ff8000000000000n);

function floatBinary(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = codec.decode(args[0], `${declaration} left operand`);
    const right = codec.decode(args[1], `${declaration} right operand`);
    return { value: codec.encode(operation(left, right)), world };
  };
}

function floatDecision(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 2, `${declaration} external arity mismatch`);
    const left = codec.decode(args[0], `${declaration} left operand`);
    const right = codec.decode(args[1], `${declaration} right operand`);
    return { value: boolResult(operation(left, right)), world };
  };
}

function floatPredicate(declaration, codec, operation) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = codec.decode(args[0], `${declaration} operand`);
    return { value: boolResult(operation(value)), world };
  };
}

function floatNeg(declaration, codec, signMask) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const bits = codec.decodeBits(args[0], `${declaration} operand`);
    return { value: codec.encodeBits(bits ^ signMask), world };
  };
}

function floatOfBits(declaration, bitsCodec, floatCodec) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const bits = bitsCodec.decode(args[0], `${declaration} operand`);
    const semantic = floatCodec.encodeBits(bits);
    return {
      value: floatCodec.encode(
        floatCodec.decode(semantic, `${declaration} result`)),
      world,
    };
  };
}

function floatToBits(declaration, floatCodec, bitsCodec) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const bits = floatCodec.decodeBits(args[0], `${declaration} operand`);
    return { value: bitsCodec.encode(bits), world };
  };
}

function floatConversion(declaration, sourceCodec, targetCodec) {
  return ({ args, world }) => {
    assert.equal(args.length, 1, `${declaration} external arity mismatch`);
    const value = sourceCodec.decode(args[0], `${declaration} operand`);
    return { value: targetCodec.encode(value), world };
  };
}

function floatExternalFamily(typeName, codec, signMask) {
  const declaration = suffix => `${typeName}.${suffix}`;
  const binary = (suffix, operation) =>
    floatBinary(declaration(suffix), codec, operation);
  const decision = (suffix, operation) =>
    floatDecision(declaration(suffix), codec, operation);
  const predicate = (suffix, operation) =>
    floatPredicate(declaration(suffix), codec, operation);
  return {
    [declaration("add")]: binary("add", (left, right) => left + right),
    [declaration("sub")]: binary("sub", (left, right) => left - right),
    [declaration("mul")]: binary("mul", (left, right) => left * right),
    [declaration("div")]: binary("div", (left, right) => left / right),
    [declaration("neg")]: floatNeg(declaration("neg"), codec, signMask),
    [declaration("beq")]: decision("beq", (left, right) => left === right),
    [declaration("decLt")]: decision("decLt", (left, right) => left < right),
    [declaration("decLe")]: decision("decLe", (left, right) => left <= right),
    [declaration("isNaN")]: predicate("isNaN", Number.isNaN),
    [declaration("isInf")]: predicate(
      "isInf", value => value === Number.POSITIVE_INFINITY ||
        value === Number.NEGATIVE_INFINITY),
    [declaration("isFinite")]: predicate("isFinite", Number.isFinite),
  };
}

function signedFixedWidthExternalFamily(typeName, width, codec) {
  const declaration = suffix => `${typeName}.${suffix}`;
  return {
    ...fixedWidthExternalFamily(typeName, width, codec),
    [declaration("abs")]: fixedWidthUnary(
      declaration("abs"), codec, value => value < 0n ? -value : value),
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

function setArray({ args, host, world }) {
  assert.equal(args.length, 4, "Array.set! external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.set! type argument must be erased");
  const source = args[1];
  assert.equal(source.kind, "heap", "Array.set! operand must be a heap Array");
  const cell = host.liveCell(source.location);
  assert.equal(cell.object.kind, "array", "Array.set! heap object must be an Array");
  assert.ok(Number.isSafeInteger(cell.object.capacity) &&
    cell.object.capacity >= cell.object.elements.length,
    "Array.set! source has invalid capacity");
  const index = naturalValue(host, args[2], "Array.set! index");
  const replacement = args[3];
  if (index >= BigInt(cell.object.elements.length)) {
    host.decValueOnce(replacement, true);
    return { value: source, world };
  }
  const elements = [...cell.object.elements];
  const old = elements[Number(index)];
  elements[Number(index)] = replacement;
  if (!cell.persistent && cell.rc === 1) {
    host.decValueOnce(old, true);
    cell.object = { kind: "array", elements, capacity: cell.object.capacity };
    return { value: source, world };
  }
  for (const element of elements) {
    if (element.kind === "heap") host.incLocation(element.location, 1);
  }
  host.decValueOnce(replacement, true);
  if (!cell.persistent) host.decLocation(source.location);
  return {
    value: host.alloc({ kind: "array", elements, capacity: cell.object.capacity }),
    world,
  };
}

function pushArray({ args, host, world }) {
  assert.equal(args.length, 3, "Array.push external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.push type argument must be erased");
  const source = args[1];
  assert.equal(source.kind, "heap", "Array.push operand must be a heap Array");
  const cell = host.liveCell(source.location);
  assert.equal(cell.object.kind, "array", "Array.push heap object must be an Array");
  const { elements, capacity } = cell.object;
  assert.ok(Number.isSafeInteger(capacity) && capacity >= elements.length,
    "Array.push source has invalid capacity");
  const value = args[2];
  if (!cell.persistent && cell.rc === 1) {
    if (elements.length < capacity) {
      cell.object = { kind: "array", elements: [...elements, value], capacity };
      return { value: source, world };
    }
    cell.rc = 0;
    cell.live = false;
    return {
      value: host.alloc({
        kind: "array",
        elements: [...elements, value],
        capacity: 2 * (capacity + 1),
      }),
      world,
    };
  }
  for (const element of elements) {
    if (element.kind === "heap") host.incLocation(element.location, 1);
  }
  if (!cell.persistent) host.decLocation(source.location);
  const minimum = 2 * elements.length + 1;
  const nextCapacity = capacity < minimum ? 2 * (capacity + 1) : capacity;
  return {
    value: host.alloc({
      kind: "array",
      elements: [...elements, value],
      capacity: nextCapacity,
    }),
    world,
  };
}

function popArray({ args, host, world }) {
  assert.equal(args.length, 2, "Array.pop external arity mismatch");
  assert.deepStrictEqual(args[0], { kind: "erased" },
    "Array.pop type argument must be erased");
  const source = args[1];
  assert.equal(source.kind, "heap", "Array.pop operand must be a heap Array");
  const cell = host.liveCell(source.location);
  assert.equal(cell.object.kind, "array", "Array.pop heap object must be an Array");
  const { elements, capacity } = cell.object;
  assert.ok(Number.isSafeInteger(capacity) && capacity >= elements.length,
    "Array.pop source has invalid capacity");
  if (!cell.persistent && cell.rc === 1) {
    if (elements.length === 0) return { value: source, world };
    const removed = elements[elements.length - 1];
    cell.object = { kind: "array", elements: elements.slice(0, -1), capacity };
    host.decValueOnce(removed, true);
    return { value: source, world };
  }
  const remaining = elements.slice(0, -1);
  for (const element of remaining) {
    if (element.kind === "heap") host.incLocation(element.location, 1);
  }
  if (!cell.persistent) host.decLocation(source.location);
  return {
    value: host.alloc({ kind: "array", elements: remaining, capacity }),
    world,
  };
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
  const source = args[2];
  assert.equal(source.kind, "heap",
    "Array.get!Internal operand must be a heap Array");
  const object = host.liveCell(source.location).object;
  assert.equal(object.kind, "array",
    "Array.get!Internal heap object must be an Array");
  assert.ok(Number.isSafeInteger(object.capacity) &&
    object.capacity >= object.elements.length,
    "Array.get!Internal source has invalid capacity");
  const index = naturalValue(host, args[3], "Array.get!Internal index");
  const value = index < BigInt(object.elements.length)
    ? object.elements[Number(index)]
    : fallback;
  if (value.kind === "heap") host.incLocation(value.location, 1);
  return { value, world };
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
  ...signedFixedWidthExternalFamily("Int8", 8, signedFixedWidthCodecs.Int8),
  "Int8.ofNat": naturalToFixedWidth(
    "Int8.ofNat", signedFixedWidthCodecs.Int8),
  "Int8.ofInt": integerToFixedWidth(
    "Int8.ofInt", signedFixedWidthCodecs.Int8),
  "Int8.toInt": fixedWidthToInteger(
    "Int8.toInt", signedFixedWidthCodecs.Int8),
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
  ...fixedWidthExternalFamily("UInt8", 8, fixedWidthCodecs.UInt8),
  "UInt8.ofNat": naturalToFixedWidth(
    "UInt8.ofNat", fixedWidthCodecs.UInt8),
  "UInt8.toNat": fixedWidthToNatural(
    "UInt8.toNat", fixedWidthCodecs.UInt8),
  ...fixedWidthConversionFamily("UInt8"),
  ...fixedWidthExternalFamily("UInt16", 16, fixedWidthCodecs.UInt16),
  "UInt16.ofNat": naturalToFixedWidth(
    "UInt16.ofNat", fixedWidthCodecs.UInt16),
  "UInt16.toNat": fixedWidthToNatural(
    "UInt16.toNat", fixedWidthCodecs.UInt16),
  ...fixedWidthConversionFamily("UInt16"),
  ...fixedWidthExternalFamily("UInt32", 32, fixedWidthCodecs.UInt32),
  "UInt32.ofNat": naturalToFixedWidth(
    "UInt32.ofNat", fixedWidthCodecs.UInt32),
  "UInt32.toNat": fixedWidthToNatural(
    "UInt32.toNat", fixedWidthCodecs.UInt32),
  ...fixedWidthConversionFamily("UInt32"),
  ...fixedWidthExternalFamily("UInt64", 64, fixedWidthCodecs.UInt64),
  "UInt64.ofNat": naturalToFixedWidth(
    "UInt64.ofNat", fixedWidthCodecs.UInt64),
  "UInt64.toNat": fixedWidthToNatural(
    "UInt64.toNat", fixedWidthCodecs.UInt64),
  ...fixedWidthConversionFamily("UInt64"),
  ...fixedWidthExternalFamily("USize", 64, usizeFixedWidthCodec),
  "USize.ofNat": naturalToFixedWidth("USize.ofNat", usizeFixedWidthCodec),
  "USize.toNat": fixedWidthToNatural("USize.toNat", usizeFixedWidthCodec),
  ...fixedWidthConversionFamily("USize"),
  ...floatExternalFamily("Float32", float32Codec, 0x80000000n),
  "Float32.ofBits": floatOfBits(
    "Float32.ofBits", fixedWidthCodecs.UInt32, float32Codec),
  "Float32.toBits": floatToBits(
    "Float32.toBits", float32Codec, fixedWidthCodecs.UInt32),
  "Float32.toFloat": floatConversion(
    "Float32.toFloat", float32Codec, float64Codec),
  ...floatExternalFamily("Float", float64Codec, 0x8000000000000000n),
  "Float.ofBits": floatOfBits(
    "Float.ofBits", fixedWidthCodecs.UInt64, float64Codec),
  "Float.toBits": floatToBits(
    "Float.toBits", float64Codec, fixedWidthCodecs.UInt64),
  "Float.toFloat32": floatConversion(
    "Float.toFloat32", float64Codec, float32Codec),
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
  "instInhabitedUInt8": inhabitedUInt8,
  "Array.get!Internal": getArrayBang,
  "Array.set!": setArray,
  "Array.push": pushArray,
  "Array.pop": popArray,
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
