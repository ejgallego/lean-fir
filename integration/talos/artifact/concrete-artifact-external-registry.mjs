import { artifactExternalRegistry } from "./artifact-external-registry.mjs";
import { concreteFormatExternalRegistry } from "./concrete-format-external-registry.mjs";

export const concreteArtifactExternalRegistry = Object.freeze({
  ...artifactExternalRegistry,
  ...concreteFormatExternalRegistry,
});
