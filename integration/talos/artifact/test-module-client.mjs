import assert from "node:assert/strict";

import { instantiateModuleArtifact } from "./module-client.mjs";

const modulePath = process.argv[2];
const invocationPath = process.argv[3];
assert.ok(modulePath && invocationPath,
  "usage: node test-module-client.mjs MODULE.wasm INVOCATION.wasm");

const { manifest, host, entry } = await instantiateModuleArtifact(modulePath);
assert.deepStrictEqual(manifest.params, ["usize"]);
assert.equal(manifest.result, "usize");

const argument = host.encode("usize", { kind: "usize", value: 42n });
const result = host.decode("usize", entry(argument));
assert.deepStrictEqual(result, { kind: "usize", value: 42n });

await assert.rejects(
  instantiateModuleArtifact(invocationPath),
  /module-only descriptor must not contain fixture/,
);

console.log(`PASS reusable raw module client (${manifest.entry})`);
