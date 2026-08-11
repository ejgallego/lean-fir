import assert from "node:assert/strict";

import { ConcreteHost } from "./concrete-host.mjs";

const partialApply = Object.freeze({
  kind: "partialApply",
  function: "callee",
  arity: 2,
  fixed: 1,
  fields: Object.freeze(["tobject"]),
  result: "tobject",
});
const imports = Object.freeze([{ operation: partialApply }]);

const host = new ConcreteHost(
  imports,
  undefined,
  undefined,
  ["match-only-target", "callee"],
  [["uint8"], ["tobject"]],
);
const captured = host.encode("tobject", { kind: "tagged", payload: 21n });
const closure = host.partialApply(partialApply, [captured]);
const header = host.readHeader(closure);
assert.equal(header.aux0, 1,
  "partial application must use the retained module-wide target ID");
assert.equal(header.aux3, 1,
  "partial application must use the retained module-wide descriptor ID");
assert.equal(host.closureMetadata(closure).functionName, "callee");
assert.deepStrictEqual(host.closureMetadata(closure).fields, ["tobject"]);

assert.throws(
  () => new ConcreteHost(imports, undefined, undefined, ["other"]),
  /missing an imported target/,
);
assert.throws(
  () => new ConcreteHost(imports, undefined, undefined, ["callee", "callee"]),
  /must not contain duplicates/,
);
assert.throws(
  () => new ConcreteHost(imports, undefined, undefined,
    ["callee"], [["uint8"]]),
  /missing an imported descriptor/,
);
assert.throws(
  () => new ConcreteHost(imports, undefined, undefined,
    ["callee"], [["tobject"], ["tobject"]]),
  /must not contain duplicates/,
);

const float32Bits = 0x7fc01234n;
const floatBits = 0x8000000000000000n;
const floatPartialApply = Object.freeze({
  kind: "partialApply",
  function: "float-callee",
  arity: 3,
  fixed: 2,
  fields: Object.freeze(["float32", "float"]),
  result: "tobject",
});
const floatHost = new ConcreteHost(
  [{ operation: floatPartialApply }],
  undefined,
  undefined,
  ["float-callee"],
  [["float32", "float"]],
);
const floatClosure = floatHost.partialApply(floatPartialApply, [
  floatHost.encode("float32", {
    kind: "scalar",
    scalarKind: "float32",
    value: float32Bits,
  }),
  floatHost.encode("float", {
    kind: "scalar",
    scalarKind: "float",
    value: floatBits,
  }),
]);
for (const [index, kind, bits] of [
  [0, "float32", float32Bits],
  [1, "float", floatBits],
]) {
  const physical = floatHost.closureProj({
    kind: "closureProj",
    function: "float-callee",
    arity: 3,
    fixed: 2,
    index,
    result: kind,
  }, [floatClosure]);
  assert.deepStrictEqual(floatHost.decode(kind, physical), {
    kind: "scalar",
    scalarKind: kind,
    value: bits,
  });
}
assert.deepStrictEqual(
  floatHost.objectJson(floatClosure, floatHost.readHeader(floatClosure)).fixed,
  [
    {
      kind: "scalar",
      scalar: { kind: "float32", value: float32Bits.toString() },
    },
    {
      kind: "scalar",
      scalar: { kind: "float", value: floatBits.toString() },
    },
  ],
);

const refinedOperations = [
  {
    kind: "partialApply",
    function: "tagged-callee",
    arity: 2,
    fixed: 1,
    fields: ["tagged"],
    result: "tobject",
  },
  {
    kind: "partialApply",
    function: "object-callee",
    arity: 2,
    fixed: 1,
    fields: ["object"],
    result: "tobject",
  },
  {
    kind: "partialApply",
    function: "tobject-callee",
    arity: 2,
    fixed: 1,
    fields: ["tobject"],
    result: "tobject",
  },
];
const refinedHost = new ConcreteHost(
  refinedOperations.map((operation) => ({ operation })),
  undefined,
  undefined,
  refinedOperations.map((operation) => operation.function),
  refinedOperations.map((operation) => operation.fields),
);
const taggedCapture = refinedHost.encode("tagged", { kind: "tagged", payload: 13n });
const objectCapture = refinedHost.allocateString("captured object");
for (const [operation, capture] of [
  [refinedOperations[0], taggedCapture],
  [refinedOperations[1], objectCapture],
]) {
  const refinedClosure = refinedHost.partialApply(operation, [capture]);
  assert.equal(refinedHost.closureProj({
    kind: "closureProj",
    function: operation.function,
    arity: operation.arity,
    fixed: operation.fixed,
    index: 0,
    result: "tobject",
  }, [refinedClosure]), capture,
  `${operation.fields[0]} capture must refine tobject projection`);
}
const tobjectCapture = refinedHost.encode("tobject", { kind: "tagged", payload: 17n });
const tobjectClosure = refinedHost.partialApply(refinedOperations[2], [tobjectCapture]);
assert.throws(() => refinedHost.closureProj({
  kind: "closureProj",
  function: "tobject-callee",
  arity: 2,
  fixed: 1,
  index: 0,
  result: "tagged",
}, [tobjectClosure]), /concrete closure capture kind mismatch/,
"tobject capture must not refine tagged projection");

console.log("PASS retained concrete closure dispatch and descriptor metadata");
