import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import {
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";

export async function checkConcretePrettyFormatInvocation({
  bytes,
  manifest,
  expected = "α β\n. γ\n  δ\n  ε",
}) {
  assert.equal(manifest.fixture, "source-pretty-format-coverage");
  assert.equal(manifest.sourceEntry, "Fir.Wasm.Emit.SourceFixture.prettyFormatRaw");
  assert.deepStrictEqual(manifest.params,
    ["tobject", "tobject", "tobject", "tobject"]);
  assert.equal(manifest.result, "object");
  assert.ok(manifest.initialRuntime,
    "concrete prettyM invocation has no initial runtime");
  assert.equal(manifest.arguments.length, manifest.params.length);
  assert.ok(WebAssembly.validate(bytes),
    "concrete prettyM invocation failed WebAssembly validation");

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime,
    concreteArtifactExternalRegistry, manifest.closureDispatch);
  for (const cell of manifest.initialRuntime.heap) {
    const address = host.locationAddresses.get(cell.location);
    assert.notEqual(address, undefined,
      `initial location ${cell.location} was not loaded`);
    const header = host.readHeader(address);
    assert.equal(header.rc, cell.rc,
      `initial location ${cell.location} rc mismatch`);
    assert.equal(header.persistent, cell.persistent,
      `initial location ${cell.location} persistence mismatch`);
    assert.equal(header.live, cell.live,
      `initial location ${cell.location} liveness mismatch`);
    assert.deepStrictEqual(host.objectJson(address, header), cell.object,
      `initial location ${cell.location} object mismatch`);
  }

  const physicalArgs = manifest.params.map((kind, index) =>
    host.encode(kind, concreteManifestValue(manifest.arguments[index])));
  const { instance } = await WebAssembly.instantiate(
    bytes, host.imports(manifest.imports));
  const result = host.decode(manifest.result,
    instance.exports[manifest.entry](...physicalArgs));
  assert.equal(result.kind, "heap");
  assert.equal(host.readString(host.addressOf(result.location)), expected);
  assert.ok(!host.trace.some((event) => event.name === "panicCore" ||
    event.name === "instInhabitedOfMonad._redArg"));

  return `PASS concrete initial-runtime prettyM invocation (${manifest.entry})`;
}
