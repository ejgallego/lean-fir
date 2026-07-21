import assert from "node:assert/strict";

import { formatExternalRegistry } from "../../../scripts/wasm_format_externals.mjs";
import { checkPrettyFormatModule } from "./check-pretty-format-module.mjs";
import { loadModuleArtifact } from "./node-module-client.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath, "usage: node call-pretty-format.mjs ARTIFACT.wasm");

const artifact = await loadModuleArtifact(artifactPath, {
  externalRegistry: formatExternalRegistry,
});
console.log(checkPrettyFormatModule(artifact));
