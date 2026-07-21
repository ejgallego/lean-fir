import assert from "node:assert/strict";
import fs from "node:fs";

import { SemanticHost } from "../../../scripts/wasm_semantic_host.mjs";

const INVOCATION_FIELDS = ["fixture", "arguments", "initialRuntime"];

function readModuleDescriptor(artifactPath) {
  const manifest = JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8"));
  assert.ok(manifest && typeof manifest === "object" && !Array.isArray(manifest),
    "module descriptor must be a JSON object");
  assert.equal(typeof manifest.sourceEntry, "string",
    "module descriptor sourceEntry must be a string");
  assert.equal(typeof manifest.entry, "string",
    "module descriptor entry must be a string");
  assert.equal(typeof manifest.result, "string",
    "module descriptor result must be a string");
  assert.ok(Array.isArray(manifest.params),
    "module descriptor params must be an array");
  assert.ok(manifest.params.every((kind) => typeof kind === "string"),
    "module descriptor params must contain ABI kind names");
  assert.ok(Array.isArray(manifest.imports),
    "module descriptor imports must be an array");
  for (const field of INVOCATION_FIELDS) {
    assert.ok(!Object.hasOwn(manifest, field),
      `module-only descriptor must not contain ${field}`);
  }
  return manifest;
}

/**
 * Instantiate an invocation-free FIR Wasm artifact.
 *
 * This intentionally exposes the raw exported WebAssembly function and the
 * semantic host. Callers allocate Lean runtime values in `host`, encode them
 * with the descriptor's ABI kinds, and decode the physical result themselves.
 */
export async function instantiateModuleArtifact(artifactPath, options = {}) {
  const bytes = fs.readFileSync(artifactPath);
  const manifest = readModuleDescriptor(artifactPath);
  assert.ok(WebAssembly.validate(bytes), `${artifactPath} failed WebAssembly validation`);

  assert.ok(!(options.host && options.externalRegistry),
    "pass either an existing host or an external registry, not both");
  const host = options.host ?? new SemanticHost(undefined, options.externalRegistry);
  assert.ok(host instanceof SemanticHost, "module artifact host must be a SemanticHost");

  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const entry = instance.exports[manifest.entry];
  assert.equal(typeof entry, "function",
    `module export ${manifest.entry} must be a function`);
  return { manifest, host, instance, entry };
}
