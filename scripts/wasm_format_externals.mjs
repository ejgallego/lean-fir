import assert from "./wasm_assert.mjs";

import {
  integerValue,
  validationExternalRegistry,
} from "./wasm_validation_externals.mjs";

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
  panicCore: unreachablePanicHelper,
  "instInhabitedOfMonad._redArg": unreachablePanicHelper,
};
