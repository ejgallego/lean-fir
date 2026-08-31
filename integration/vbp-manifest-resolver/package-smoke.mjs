import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import {
  VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION,
  VBP_MANIFEST_RESOLVER_ENTRY,
  createVbpManifestResolverAdapter,
} from "./vbp-manifest-resolver-browser-adapter.mjs";

const bytes = readFileSync(new URL("./vbp-manifest-resolver.wasm", import.meta.url));
const manifest = JSON.parse(readFileSync(
  new URL("./vbp-manifest-resolver.wasm.json", import.meta.url), "utf8"));
const build = JSON.parse(readFileSync(
  new URL("./BUILD.json", import.meta.url), "utf8"));
const fixtureBytes = readFileSync(
  new URL("./runtime-manifest-resolver.json", import.meta.url));
const fixtureText = fixtureBytes.toString("utf8");
const fixture = JSON.parse(fixtureText);
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

function valueIdentity(result) {
  switch (result.kind) {
    case "preview":
    case "label":
    case "declaration":
    case "sourceMetadata":
      return result.manifestEntry?.key ?? "";
    case "group":
      return result.value?.label ?? "";
    case "sourceDocument":
      return result.value?.id ?? "";
    default:
      throw new Error(`unknown result kind ${result.kind}`);
  }
}

function snapshot(result) {
  const noLocation = result.kind === "group" || result.kind === "sourceDocument";
  return {
    id: result.requestId,
    kind: result.kind,
    ok: result.ok,
    key: result.key,
    reason: result.reason,
    label: result.label ?? null,
    facet: result.facet ?? null,
    declaration: result.declaration ?? null,
    valueIdentity: valueIdentity(result),
    href: result.href,
    sourceLocationOk: noLocation ? null : (result.sourceLocation?.ok ?? null),
    sourceDocumentIds: result.sources.map(({ documentId }) => documentId),
  };
}

assert.equal(VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION,
  "fir.vbp-manifest-resolver.browser/v1");
assert.equal(build.wasm.sha256, sha256(bytes));
assert.equal(build.fixture.sha256, sha256(fixtureBytes));
const module = await WebAssembly.compile(bytes);
assert.deepEqual(WebAssembly.Module.imports(module), []);
assert.deepEqual(WebAssembly.Module.exports(module), build.wasm.exports);

const initializeStarted = performance.now();
const adapter = await createVbpManifestResolverAdapter({
  module, manifest, build,
});
const initializationWallMs = performance.now() - initializeStarted;
const output = JSON.parse(adapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY,
  [fixtureText]));
assert.equal(output.abiVersion, fixture.abiVersion);
assert.equal(output.ok, true);
assert.equal(output.error, "");
assert.deepEqual(output.results.map(snapshot), fixture.expected);
assert.equal(output.results.length, 11);
const checkpoint = adapter.lastCall.memory.checkpoint;
assert.equal(adapter.lastCall.memory.postRewindFrontier, checkpoint);

for (const invalid of fixture.invalidCases) {
  const invalidInput = JSON.stringify({
    abiVersion: fixture.abiVersion,
    manifest: invalid.manifest,
    requests: [],
  });
  const result = JSON.parse(adapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY,
    [invalidInput]));
  assert.equal(result.ok, false, invalid.id);
  assert.ok(result.error.includes(invalid.errorIncludes), invalid.id);
  assert.deepEqual(result.results, [], invalid.id);
  assert.equal(adapter.lastCall.memory.postRewindFrontier, checkpoint, invalid.id);
}

const malformed = JSON.parse(adapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY,
  ["not json"]));
assert.equal(malformed.ok, false);
assert.ok(malformed.error.length > 0);
assert.deepEqual(malformed.results, []);
assert.equal(adapter.lastCall.memory.postRewindFrontier, checkpoint);

const unicodeInput = JSON.stringify({
  abiVersion: 1,
  manifest: { previews: [], groups: [], graphs: [] },
  requests: [{ id: "λ-日本語", kind: "preview", value: "不存在" }],
});
const unicode = JSON.parse(adapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY,
  [unicodeInput]));
assert.equal(unicode.results[0].requestId, "λ-日本語");
assert.equal(unicode.results[0].ok, false);
assert.equal(adapter.lastCall.memory.postRewindFrontier, checkpoint);

const warmupCalls = 4;
for (let index = 0; index < warmupCalls; ++index) {
  adapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY, [fixtureText]);
}
const warmCalls = 16;
const warmStarted = performance.now();
for (let index = 0; index < warmCalls; ++index) {
  const repeated = adapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY, [fixtureText]);
  assert.equal(JSON.parse(repeated).results.length, 11);
  assert.equal(adapter.lastCall.memory.postRewindFrontier, checkpoint);
}
const warmBatchMs = performance.now() - warmStarted;

let fakeTick = 0;
const timedAdapter = await createVbpManifestResolverAdapter({
  module, manifest, build, now: () => fakeTick++,
});
timedAdapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY, ["not json"]);
for (const field of ["encodeMs", "executeMs", "decodeMs", "rewindMs",
  "totalMs", "overheadMs"]) {
  assert.ok(Number.isFinite(timedAdapter.lastCall.timings[field]));
}
assert.equal(timedAdapter.lastCall.memory.postRewindFrontier,
  timedAdapter.lastCall.memory.checkpoint);
timedAdapter.dispose();
assert.throws(() => timedAdapter.invoke(VBP_MANIFEST_RESOLVER_ENTRY,
  [fixtureText]), /disposed or invalid/);

const lastCall = adapter.lastCall;
adapter.dispose();
console.log(JSON.stringify({
  ok: true,
  validAndMissingResults: output.results.length,
  malformedManifestCases: fixture.invalidCases.length,
  malformedJsonCases: 1,
  unicodeCases: 1,
  wasmBytes: bytes.byteLength,
  wasmSha256: build.wasm.sha256,
  imports: WebAssembly.Module.imports(module).length,
  exports: WebAssembly.Module.exports(module),
  initializationWallMs,
  warmCalls,
  warmBatchMs,
  warmCallMeanMs: warmBatchMs / warmCalls,
  flatCheckpoint: checkpoint,
  lastCall,
}, null, 2));
