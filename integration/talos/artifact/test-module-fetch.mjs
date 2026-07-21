import assert from "node:assert/strict";
import fs from "node:fs";

import { SemanticHost } from "../../../scripts/wasm_semantic_host.mjs";
import { fetchModuleArtifact } from "./module-client.mjs";

const modulePath = process.argv[2];
assert.ok(modulePath, "usage: node test-module-fetch.mjs MODULE.wasm");

const bytes = fs.readFileSync(modulePath);
const descriptor = fs.readFileSync(`${modulePath}.json`, "utf8");
const artifactUrl = `data:application/wasm;base64,${bytes.toString("base64")}`;
const descriptorUrl = `data:application/json;base64,${Buffer.from(descriptor).toString("base64")}`;
const host = new SemanticHost();
const { manifest, entry } = await fetchModuleArtifact(artifactUrl, {
  descriptorUrl,
  host,
});

const argument = host.encode("usize", { kind: "usize", value: 42n });
assert.deepStrictEqual(host.decode(manifest.result, entry(argument)), {
  kind: "usize",
  value: 42n,
});

console.log(`PASS fetch-backed raw module client (${manifest.entry})`);
