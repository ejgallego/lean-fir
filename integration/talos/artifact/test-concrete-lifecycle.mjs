import assert from "node:assert/strict";
import fs from "node:fs";
import { ConcreteHost } from "./concrete-host.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { instantiateModuleArtifact, manageModuleInstance } from "./module-client.mjs";

const path = process.argv[2];
assert.ok(path, "usage: node test-concrete-lifecycle.mjs RELEASES.wasm");
const manifest = JSON.parse(fs.readFileSync(`${path}.json`, "utf8"));
const host = new ConcreteHost(manifest.imports, undefined,
  concreteArtifactExternalRegistry, manifest.closureDispatch, manifest.closureDescriptors);
const { instance, entry } = await instantiateModuleArtifact({
  bytes: fs.readFileSync(path), manifest, host,
});
assert.equal(entry, instance.exports[manifest.entry]);
assert.ok(Object.isFrozen(instance) && Object.isFrozen(instance.exports));
assert.equal(instance instanceof WebAssembly.Instance, false,
  "managed facade must not expose the raw instance");

const alloc = (fields, values) => host.allocCtor({ kind: "allocCtor", name: "lifecycle-test",
  result: "object", size: fields.length, usize: 0, ssize: 0, tag: "0", fields }, values) >>> 0;
const address = alloc(["erased", "tobject"], [0, 3]);
host.writeWordSlot(address + 32, 3);
assert.throws(() => host.objectJson(address, host.readHeader(address)), /does not refine erased/);
host.writeWordSlot(address + 32, 0);
host.descriptors.get(address).fieldKinds[0] = "tobject";
assert.throws(() => host.constructorDescriptor(address, host.readHeader(address)),
  /same-phase.*descriptor corruption/);
host.recordDescriptor(address, { kind: "constructor", fieldKinds: ["erased", "tobject"] });
const header = host.readHeader(address);
host.writeHeader(address, { ...header, aux1: 1 });
assert.throws(() => host.constructorDescriptor(address, host.readHeader(address)),
  /same-phase.*layout corruption/);
host.writeHeader(address, { ...header, aux1: 3 });
assert.throws(() => host.constructorDescriptor(address, host.readHeader(address)),
  /fields exceed allocation extent/);
host.writeHeader(address, header);
const publish = (word) => host.cacheSet({ kind: "cacheSet", declaration: "test", value: "object" }, [word]);
for (const word of [0, 6, 0xfffffffe]) assert.throws(() => publish(word));
instance.exports.fir_release_0(address);
assert.throws(() => publish(address), /deadObject/);
assert.deepEqual(host.executionPhases, ["host"]);
assert.throws(() => instance.exports.fir_release_0(6), WebAssembly.RuntimeError);
assert.deepEqual(host.executionPhases, ["host"], "guest trap must unwind");

const deadChild = host.allocateString("dead child");
host.releaseWord(deadChild, true);
const parent = alloc(["tobject"], [deadChild]);
assert.throws(() => publish(parent), /deadObject/, "publishing a dead owned child must reject");
const growingChild = host.allocateString("x".repeat(100000));
const growingParent = alloc(["object"], [growingChild]);
instance.exports.fir_heap_frontier();
publish(growingParent);
assert.equal(host.readHeader(growingChild).persistent, true);
assert.equal(host.buffer, instance.exports.memory.buffer);

// Unit exercise of the export adapter with controlled callable exports: all
// helper routes, nested provider reentry, import throws, and memory/global identity.
const nestedHost = new ConcreteHost();
const memory = new WebAssembly.Memory({ initial: 1 });
const global = new WebAssembly.Global({ value: "i32", mutable: true }, 5);
let frontier = 1024;
let facade;
let fail = false;
nestedHost.externalRegistry.set("reenter", ({ host: current }) => {
  assert.equal(current.executionPhases.at(-1), "host");
  const child = current.allocateString("nested");
  if (fail) throw new Error("provider unwind");
  assert.equal(facade.exports.helper(7), 8);
  assert.equal(current.executionPhases.at(-1), "host");
  return { value: { kind: "heap", location: current.locationOf(child) } };
});
const operation = { kind: "external", declaration: "reenter", params: [], results: ["object"] };
const imported = nestedHost.imports([{ module: "test", name: "call", operation }]).test.call;
const raw = { exports: {
  memory, global,
  fir_heap_frontier: () => frontier,
  fir_heap_set_frontier: (value) => { frontier = value; },
  entry: () => imported(),
  helper: (value) => { assert.equal(nestedHost.executionPhases.at(-1), "guest"); return value + 1; },
  thrower: () => { throw new Error("guest unwind"); },
} };
facade = manageModuleInstance(raw, nestedHost);
assert.equal(facade.exports.memory, memory);
assert.equal(facade.exports.global, global);
assert.equal(facade.exports.helper.length, 1);
assert.equal(nestedHost.readString(facade.exports.entry()), "nested");
fail = true;
assert.throws(() => facade.exports.entry(), /provider unwind/);
assert.deepEqual(nestedHost.executionPhases, ["host"]);
assert.throws(() => facade.exports.thrower(), /guest unwind/);
assert.deepEqual(nestedHost.executionPhases, ["host"]);
assert.throws(() => imported(), /requires the managed/,
  "unmanaged resident import cannot claim managed provenance");
const plain = { exports: { helper: (value) => value } };
assert.equal(manageModuleInstance(plain, {}), plain, "hosts without hooks retain raw compatibility");
assert.throws(() => manageModuleInstance(plain, { beginGuestCall() {} }), /both guest lifecycle/);
console.log("PASS managed exports, host provenance negatives, persistence, growth and nested unwind");
