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
);
const captured = host.encode("tobject", { kind: "tagged", payload: 21n });
const closure = host.partialApply(partialApply, [captured]);
const header = host.readHeader(closure);
assert.equal(header.aux0, 1,
  "partial application must use the retained module-wide target ID");
assert.equal(host.closureMetadata(closure).functionName, "callee");

assert.throws(
  () => new ConcreteHost(imports, undefined, undefined, ["other"]),
  /missing an imported target/,
);
assert.throws(
  () => new ConcreteHost(imports, undefined, undefined, ["callee", "callee"]),
  /must not contain duplicates/,
);

console.log("PASS retained concrete closure dispatch metadata");
