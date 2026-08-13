import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

import { createIlluminateSpatialHitSceneAdapter } from
  "./illuminate-spatial-hit-scene-browser-adapter.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const wasm = readFileSync(join(directory, "illuminate-spatial-hit-scene.wasm"));
const build = JSON.parse(readFileSync(join(directory, "BUILD.json"), "utf8"));
const fixture = JSON.parse(readFileSync(
  join(directory, "hit-scene-benchmark.json"), "utf8"));
const suite = JSON.parse(readFileSync(
  join(directory, "hit-scene-benchmark-suite.json"), "utf8"));
const sha256 = (bytes) => createHash("sha256").update(bytes).digest("hex");
const bitsView = new DataView(new ArrayBuffer(8));
const fromBits = (bits) => {
  bitsView.setBigUint64(0, BigInt(bits), true);
  return bitsView.getFloat64(0, true);
};

assert.equal(fixture.schemaVersion, "illuminate.hit-scene-benchmark/v1");
assert.equal(fixture.queries.length, 301);
assert.equal(suite.schemaVersion, "illuminate.hit-scene-benchmark-suite/v1");
assert.deepEqual(suite.fixtures.map(({ queries }) => queries.length),
  [83, 301, 625]);
assert.equal(build.capabilities.inputLayout.version,
  "lean-4.33-Illuminate.SpatialHitScene/v1");
assert.equal(build.wasm.sha256, sha256(wasm));
assert.equal(build.fixture.sha256,
  sha256(readFileSync(join(directory, "hit-scene-benchmark.json"))));
assert.equal(build.fixtureSuite.sha256,
  sha256(readFileSync(join(directory, "hit-scene-benchmark-suite.json"))));

const module = new WebAssembly.Module(wasm);
assert.deepEqual(WebAssembly.Module.imports(module), []);
assert.deepEqual(WebAssembly.Module.exports(module).map(({ name, kind }) =>
  ({ name, kind })), build.wasm.exports);

const adapter = await createIlluminateSpatialHitSceneAdapter({ bytes: wasm, build });
const created = adapter.createHitScene(fixture.encodedScene);
assert.equal(created.memory.reservedFrontier,
  build.capabilities.completeRuntime.externalRuntime.reservedMemoryBytes);
assert(created.memory.persistentCheckpoint > created.memory.reservedFrontier);
assert(created.memory.preparationBytes > 0);
assert.equal(created.memory.persistentBytes,
  created.memory.persistentCheckpoint - created.memory.reservedFrontier);
assert(Number.isFinite(created.timings.prepareMs));

let suiteQueries = 0;
for (const item of suite.fixtures) {
  const prepared = adapter.createHitScene(item.encodedScene);
  for (const query of item.queries) {
    assert.deepEqual(adapter.hitTest(prepared.scene,
      fromBits(query.xBits), fromBits(query.yBits)), query.expected,
    `${item.name}/${query.name}`);
    suiteQueries += 1;
  }
  adapter.disposeHitScene(prepared.scene);
}
assert.equal(suiteQueries, 1_009);

for (const query of fixture.queries) {
  assert.deepEqual(adapter.hitTest(created.scene,
    fromBits(query.xBits), fromBits(query.yBits)), query.expected, query.name);
}

const checkpoint = created.memory.persistentCheckpoint;
for (let index = 0; index < 10_000; ++index) {
  const query = fixture.queries[index % fixture.queries.length];
  adapter.hitTest(created.scene, fromBits(query.xBits), fromBits(query.yBits));
}
const diagnostic = adapter.hitTestDiagnostic(created.scene,
  fromBits(fixture.queries[0].xBits), fromBits(fixture.queries[0].yBits));
assert.deepEqual(diagnostic.result, fixture.queries[0].expected);
assert.equal(diagnostic.memory.frontierBefore, checkpoint);
assert.equal(diagnostic.memory.postRewindFrontier, checkpoint);
assert(diagnostic.memory.peakFrontier >= checkpoint);

const second = adapter.createHitScene(fixture.encodedScene);
assert.deepEqual(adapter.hitTest(second.scene,
  fromBits(fixture.queries[1].xBits), fromBits(fixture.queries[1].yBits)),
fixture.queries[1].expected);
assert.deepEqual(adapter.hitTest(created.scene,
  fromBits(fixture.queries[2].xBits), fromBits(fixture.queries[2].yBits)),
fixture.queries[2].expected);
adapter.disposeHitScene(second.scene);
adapter.disposeHitScene(second.scene);
assert.throws(() => adapter.hitTest(second.scene, 0, 0), /scene is disposed/);

for (let index = 0; index < 8; ++index) {
  const temporary = adapter.createHitScene(fixture.encodedScene);
  adapter.disposeHitScene(temporary.scene);
}
assert.throws(() => adapter.createHitScene(JSON.stringify({
  tree: { kind: "unsupported" }, labels: [],
})), /unsupported/);

adapter.disposeHitScene(created.scene);
assert.throws(() => adapter.hitTest(created.scene, 0, 0), /scene is disposed/);

const summary = {
  queries: suiteQueries,
  flatQueries: 10_000,
  checkpoint,
  encodedBytes: created.memory.encodedBytes,
  wasmBytes: wasm.byteLength,
  wasmSha256: sha256(wasm),
  imports: WebAssembly.Module.imports(module).length,
  exports: WebAssembly.Module.exports(module),
};
console.log(JSON.stringify(summary, null, 2));
