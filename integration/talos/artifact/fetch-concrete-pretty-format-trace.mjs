import {
  checkConcretePrettyFormatTraceModule,
} from "./check-concrete-pretty-format-trace-module.mjs";
import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

function requireCondition(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

/** Fetch and check the raw styled prettyM boundary in Node or a browser. */
export async function checkFetchedConcretePrettyFormatTrace(artifactUrl) {
  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  requireCondition(moduleResponse.ok,
    `failed to fetch styled concrete prettyM module: HTTP ${moduleResponse.status}`);
  requireCondition(descriptorResponse.ok,
    `failed to fetch styled concrete prettyM descriptor: HTTP ${descriptorResponse.status}`);

  const manifest = await descriptorResponse.json();
  const host = new ConcreteHost(
    manifest.imports,
    undefined,
    concreteArtifactExternalRegistry,
    manifest.closureDispatch,
    manifest.closureDescriptors,
  );
  const artifact = await instantiateModuleArtifact({
    bytes: await moduleResponse.arrayBuffer(),
    manifest,
    host,
  });
  return checkConcretePrettyFormatTraceModule(artifact);
}
