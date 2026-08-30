import assert from "node:assert/strict";
import fs from "node:fs";

import { ConcreteHost } from "./concrete-host.mjs";

const path = process.argv[2];
if (path === undefined) {
  throw new Error("usage: node run-resident-object-case.mjs PATH.wasm");
}

const bytes = fs.readFileSync(path);
assert.ok(WebAssembly.validate(bytes), "resident object-case module is invalid");
const module = new WebAssembly.Module(bytes);
assert.deepStrictEqual(WebAssembly.Module.imports(module), [],
  "resident object-case retained imports");

const host = new ConcreteHost([]);
const instance = await WebAssembly.instantiate(module, {});
assert.ok(instance.exports.memory instanceof WebAssembly.Memory,
  "resident object-case does not export module-owned memory");
host.attachMemory(instance.exports.memory);

const constructorZero = host.encode("tobject", { kind: "tagged", payload: 0n });
assert.equal(instance.exports.main(constructorZero) >>> 0, 0,
  "resident object-case did not select constructor tag zero");

const promotedUInt32Size = host.encode("tobject", {
  kind: "tagged",
  payload: 0x100000000n,
});
assert.equal(instance.exports.main(promotedUInt32Size) >>> 0, 5,
  "resident object-case truncated UInt32.size to constructor tag zero");

console.log("PASS resident generated object-case preserves promoted UInt64 tag");
