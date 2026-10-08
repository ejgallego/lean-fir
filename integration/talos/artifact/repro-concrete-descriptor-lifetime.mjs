import assert from "node:assert/strict";
import fs from "node:fs";

import { ConcreteHost } from "./concrete-host.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

// Diagnostic reproducer: it deliberately leaves the production arity assertion
// intact and fails there while host metadata outlives a resident allocation.
const [artifactPath, allocatorDescriptorPath] = process.argv.slice(2);
assert.ok(artifactPath && allocatorDescriptorPath,
  "usage: node repro-concrete-descriptor-lifetime.mjs RELEASES.wasm ALLOCATOR.wasm.json");
const manifest = JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8"));
const allocator = JSON.parse(fs.readFileSync(allocatorDescriptorPath, "utf8"));
const constructors = allocator.imports.filter(({ operation }) => operation.kind === "allocCtor");
const replacementIndex = constructors.findIndex(({ operation }) =>
  operation.name.endsWith("Std.Format.SpaceResult.mk") &&
  operation.size === 1 && operation.usize === 0 && operation.ssize === 2 &&
  operation.fields.length === 1 && operation.fields[0] === "tobject");
assert.ok(replacementIndex >= 0, "reproducer lacks the one-field/two-scalar-byte constructor");

const host = new ConcreteHost(manifest.imports, undefined,
  concreteArtifactExternalRegistry, manifest.closureDispatch, manifest.closureDescriptors);
const { instance } = await instantiateModuleArtifact({
  bytes: fs.readFileSync(artifactPath), manifest, host,
});
const original = host.allocCtor({
  kind: "allocCtor", name: "Std.Format.tag", result: "tobject",
  size: 2, usize: 0, ssize: 0, tag: "7", fields: ["tobject", "tobject"],
}, [3, 3]);
assert.equal(host.descriptors.get(original).fieldKinds.length, 2);
instance.exports.fir_heap_set_frontier(host.heapCursor);
instance.exports.fir_release_0(original);
assert.equal(host.readHeader(original, false).live, false);

const replacement = instance.exports[`fir_alloc_ctor_${replacementIndex}`](3) >>> 0;
assert.equal(replacement, original, "resident allocator did not reuse the exact-size block");
const header = host.readHeader(replacement);
assert.equal(header.bytes, 48);
assert.equal(header.aux1, 1);
assert.equal(header.aux3, 2);
console.log(JSON.stringify({ address: replacement, header,
  cachedDescriptor: host.descriptors.get(replacement) }));
host.cacheSet({ kind: "cacheSet", declaration: "descriptor-lifetime-repro", value: "object" },
  [replacement]);
