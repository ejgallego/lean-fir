import fs from "node:fs";

import { SemanticHost } from "../../../scripts/wasm_semantic_host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

/** Node filesystem wrapper around the transport-neutral module client. */
export async function loadModuleArtifact(artifactPath, options = {}) {
  if (options.host && options.externalRegistry) {
    throw new Error("pass either an existing host or an external registry, not both");
  }
  const host = options.host ?? new SemanticHost(undefined, options.externalRegistry);
  return instantiateModuleArtifact({
    bytes: fs.readFileSync(artifactPath),
    manifest: JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8")),
    host,
  });
}
