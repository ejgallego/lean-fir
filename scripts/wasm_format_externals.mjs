import assert from "./wasm_assert.mjs";

import {
  integerValue,
  naturalValue,
  scalarUInt32,
  stringValue,
  validationExternalRegistry,
} from "./wasm_validation_externals.mjs";
import {
  stringAppend,
  stringPushn,
} from "./wasm_format_external_algorithms.mjs";

function stringResult(host, value) {
  return host.alloc({ kind: "string", value });
}

function unreachablePanicHelper({ declaration }) {
  throw new Error(`unreachable Lean pretty-printing panic helper executed: ${declaration}`);
}

export const formatExternalRegistry = {
  ...validationExternalRegistry,
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
  panicCore: unreachablePanicHelper,
  "instInhabitedOfMonad._redArg": unreachablePanicHelper,
};
