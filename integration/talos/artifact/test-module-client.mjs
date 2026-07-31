import assert from "node:assert/strict";

import {
  decodeManifestResult,
  encodeManifestArgument,
  manifestEntryName,
  validateBitExactFloatTransport,
} from "../../../scripts/wasm_semantic_host.mjs";
import { validateModuleDescriptor } from "./module-client.mjs";
import { loadModuleArtifact } from "./node-module-client.mjs";

const modulePath = process.argv[2];
const invocationPath = process.argv[3];
const float32ModulePath = process.argv[4];
const float64ModulePath = process.argv[5];
assert.ok(modulePath && invocationPath && float32ModulePath && float64ModulePath,
  "usage: node test-module-client.mjs MODULE.wasm INVOCATION.wasm " +
  "FLOAT32-MODULE.wasm FLOAT64-MODULE.wasm");

const { manifest, host, entry } = await loadModuleArtifact(modulePath);
assert.deepStrictEqual(manifest.params, ["usize"]);
assert.equal(manifest.result, "usize");

const argument = host.encode("usize", { kind: "usize", value: 42n });
const result = host.decode("usize", entry(argument));
assert.deepStrictEqual(result, { kind: "usize", value: 42n });

await assert.rejects(
  loadModuleArtifact(invocationPath),
  /module-only descriptor must not contain fixture/,
);

for (const [path, kind, bits] of [
  [float32ModulePath, "float32", 0x7fa12345n],
  [float64ModulePath, "float", 0x7ff123456789abcdn],
]) {
  const artifact = await loadModuleArtifact(path);
  const transport = validateBitExactFloatTransport(artifact.manifest);
  assert.equal(transport.entry, manifestEntryName(artifact.manifest));
  const physical = encodeManifestArgument(artifact.host, artifact.manifest, 0, {
    kind: "scalar",
    scalarKind: kind,
    value: bits,
  });
  assert.deepStrictEqual(
    decodeManifestResult(
      artifact.host, artifact.manifest, artifact.entry(physical)),
    { kind: "scalar", scalarKind: kind, value: bits },
    `${kind} module client lost a signaling-NaN payload`,
  );
  const { version: _version, ...missingVersion } = transport;
  assert.throws(() => validateModuleDescriptor({
    ...artifact.manifest,
    bitExactFloatTransport: missingVersion,
  }), /unknown or missing fields/);
  assert.throws(() => validateModuleDescriptor({
    ...artifact.manifest,
    params: [kind === "float32" ? "uint32" : "uint64"],
    result: kind === "float32" ? "uint32" : "uint64",
  }), /non-floating manifest must not advertise/);
}

console.log(
  `PASS reusable raw module client with exact float facade (${manifest.entry})`);
