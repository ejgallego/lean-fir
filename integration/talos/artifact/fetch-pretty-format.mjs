import { formatExternalRegistry } from "../../../scripts/wasm_format_externals.mjs";
import { SemanticHost } from "../../../scripts/wasm_semantic_host.mjs";
import { checkPrettyFormatModule } from "./check-pretty-format-module.mjs";
import { fetchModuleArtifact } from "./module-client.mjs";

/** Fetch and run prettyM using only browser/worker-compatible dependencies. */
export async function checkFetchedPrettyFormat(artifactUrl) {
  const host = new SemanticHost(undefined, formatExternalRegistry);
  const artifact = await fetchModuleArtifact(artifactUrl, { host });
  return checkPrettyFormatModule(artifact);
}
