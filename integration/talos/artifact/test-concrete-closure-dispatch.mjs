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

console.log("PASS retained concrete closure dispatch and descriptor metadata");
