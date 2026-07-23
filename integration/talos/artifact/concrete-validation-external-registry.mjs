import assert from "../../../scripts/wasm_assert.mjs";

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
  "Int.neg": ({ args, host, world }) => {
    assert.equal(args.length, 1, "Int.neg external arity mismatch");
    const value = integerValue(host, args[0], "Int.neg operand");
    return { value: integerResult(host, -value), world };
  },
  "Fir.Validation.Corpus.NativeEffects.recordImpl": ({ args, host, world }) => {
    assert.equal(args.length, 1, "validation.record external arity mismatch");
    const argument = naturalValue(host, args[0], "validation.record operand");
    const result = argument + 1n;
    recordEffect(host, "validation.record", argument, result);
    return { value: naturalResult(host, result), world: world + 1 };
  },
});

