import assert from "node:assert/strict";
import fs from "node:fs";
import { ConcreteHost } from "./concrete-host.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

// Compare legitimate same-layout resident reuse with an illicit live erased
// slot mutation. No production guard is replaced or relaxed.
const [artifactPath, allocatorDescriptorPath] = process.argv.slice(2);
assert.ok(artifactPath && allocatorDescriptorPath,
  "usage: node repro-concrete-descriptor-provenance.mjs RELEASES.wasm ALLOCATOR.wasm.json");
const manifest = JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8"));
const allocator = JSON.parse(fs.readFileSync(allocatorDescriptorPath, "utf8"));
const constructors = allocator.imports.filter(({ operation }) => operation.kind === "allocCtor");
const index = constructors.findIndex(({ operation }) => operation.tag === "0" &&
  operation.size === 2 && operation.usize === 0 && operation.ssize === 0 &&
  JSON.stringify(operation.fields) === JSON.stringify(["object", "tobject"]));
assert.ok(index >= 0, "same-layout resident constructor helper missing");

async function history(residentReuse) {
  const host = new ConcreteHost(manifest.imports, undefined,
    concreteArtifactExternalRegistry, manifest.closureDispatch, manifest.closureDescriptors);
  const { instance } = await instantiateModuleArtifact({
    bytes: fs.readFileSync(artifactPath), manifest, host,
  });
  const child = host.allocateString("owned child");
  const address = host.allocCtor({ kind: "allocCtor", name: "provenance-control",
    result: "object", size: 2, usize: 0, ssize: 0, tag: "0",
    fields: ["erased", "tobject"] }, [0, 3]) >>> 0;
  host.synchronizeResidentFrontierAfterImport();
  if (residentReuse) {
    instance.exports.fir_release_0(address);
    assert.equal(host.readHeader(address, false).live, false);
    const replacement = instance.exports[`fir_alloc_ctor_${index}`](child, 3) >>> 0;
    assert.equal(replacement, address);
  } else {
    // Deliberately violate the recorded erased-slot contract without releasing.
    host.writeWordSlot(address + 32, child);
  }
  return { host, instance, address, child };
}

const reused = await history(true);
const corrupted = await history(false);
assert.equal(reused.address, corrupted.address);
assert.deepEqual(new Uint8Array(reused.instance.exports.memory.buffer),
  new Uint8Array(corrupted.instance.exports.memory.buffer), "physical heaps differ");
assert.equal(reused.host.descriptors.get(reused.address), undefined);
assert.deepEqual(corrupted.host.descriptors.get(corrupted.address).fieldKinds, ["erased", "tobject"]);
assert.deepEqual([...reused.host.addressLocations], [...corrupted.host.addressLocations]);
assert.deepEqual(reused.host.allocations, corrupted.host.allocations);
assert.equal(reused.host.heapCursor, corrupted.host.heapCursor);
assert.equal(reused.host.residentFrontier.frontier(),
  corrupted.host.residentFrontier.frontier());
assert.doesNotThrow(() => reused.host.objectJson(reused.address,
  reused.host.readHeader(reused.address)));
assert.throws(() => corrupted.host.objectJson(corrupted.address,
  corrupted.host.readHeader(corrupted.address)), /does not refine erased/);
reused.host.cacheSet({ kind: "cacheSet", declaration: "same-layout-repro", value: "object" },
  [reused.address]);
assert.equal(reused.host.readHeader(reused.address).persistent, true);
assert.equal(reused.host.readHeader(reused.child).persistent, true,
  "erased slots still participate in persistent traversal");
console.log("PASS: identical heaps distinguished by managed execution history; same-phase erased corruption rejects and resident reuse traverses the child");
