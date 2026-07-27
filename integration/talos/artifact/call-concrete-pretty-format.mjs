import assert from "node:assert/strict";
import fs from "node:fs";

import { checkConcretePrettyFormatModule } from "./check-concrete-pretty-format-module.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath, "usage: node call-concrete-pretty-format.mjs ARTIFACT.wasm");

const manifest = JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8"));
const host = new ConcreteHost(manifest.imports, undefined,
  concreteArtifactExternalRegistry, manifest.closureDispatch,
  manifest.closureDescriptors);
const artifact = await instantiateModuleArtifact({
  bytes: fs.readFileSync(artifactPath),
  manifest,
  host,
});
console.log(checkConcretePrettyFormatModule(artifact));
