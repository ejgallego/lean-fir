import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { pathToFileURL } from "node:url";

import {
  ConcreteHost,
  concreteManifestValue,
} from "./concrete-host.mjs";

export async function runConcreteNatListSource(wasmPath) {
  const manifest = JSON.parse(await readFile(`${wasmPath}.json`, "utf8"));
  assert.equal(manifest.fixture, "Fir.Wasm.Emit.SourceFixture.classifyNatList");
  assert.deepStrictEqual(manifest.params, ["tobject"]);
  assert.equal(manifest.result, "uint64");
  assert.ok(manifest.initialRuntime, "nat-list source has no initial runtime");
  const bytes = await readFile(wasmPath);
  assert.ok(WebAssembly.validate(bytes), "nat-list source failed WebAssembly validation");

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime);
  for (const cell of manifest.initialRuntime.heap) {
    const address = host.locationAddresses.get(cell.location);
    assert.notEqual(address, undefined, `initial location ${cell.location} was not loaded`);
    const header = host.readHeader(address);
    assert.equal(header.rc, cell.rc, `initial location ${cell.location} rc mismatch`);
    assert.equal(header.persistent, cell.persistent,
      `initial location ${cell.location} persistence mismatch`);
    assert.equal(header.live, cell.live, `initial location ${cell.location} liveness mismatch`);
    assert.deepStrictEqual(host.objectJson(address, header), cell.object,
      `initial location ${cell.location} object mismatch`);
  }

  const semanticArgument = concreteManifestValue(manifest.arguments[0]);
  const physicalArgument = host.encode(manifest.params[0], semanticArgument);
  assert.deepStrictEqual(host.decode(manifest.params[0], physicalArgument), semanticArgument,
    "initial heap argument did not round-trip through its concrete address");
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const result = host.decode(manifest.result,
    instance.exports[manifest.entry](physicalArgument));
  assert.deepStrictEqual(result,
    { kind: "scalar", scalarKind: "uint64", value: 1n });
  console.log("PASS concrete initial-runtime List Nat source");
}

export async function runConcreteStringSource(wasmPath) {
  const manifest = JSON.parse(await readFile(`${wasmPath}.json`, "utf8"));
  assert.equal(manifest.fixture, "Fir.Wasm.Emit.SourceFixture.acceptString");
  assert.deepStrictEqual(manifest.params, ["object"]);
  assert.equal(manifest.result, "uint64");
  assert.ok(manifest.initialRuntime, "string source has no initial runtime");
  const bytes = await readFile(wasmPath);
  assert.ok(WebAssembly.validate(bytes), "string source failed WebAssembly validation");

  const host = new ConcreteHost(manifest.imports, manifest.initialRuntime);
  for (const cell of manifest.initialRuntime.heap) {
    const address = host.locationAddresses.get(cell.location);
    assert.notEqual(address, undefined, `initial location ${cell.location} was not loaded`);
    const header = host.readHeader(address);
    assert.equal(header.rc, cell.rc, `initial location ${cell.location} rc mismatch`);
    assert.equal(header.persistent, cell.persistent,
      `initial location ${cell.location} persistence mismatch`);
    assert.equal(header.live, cell.live, `initial location ${cell.location} liveness mismatch`);
    assert.deepStrictEqual(host.objectJson(address, header), cell.object,
      `initial location ${cell.location} object mismatch`);
  }

  const semanticArgument = concreteManifestValue(manifest.arguments[0]);
  const physicalArgument = host.encode(manifest.params[0], semanticArgument);
  assert.deepStrictEqual(host.decode(manifest.params[0], physicalArgument), semanticArgument,
    "initial string argument did not round-trip through its concrete address");
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const result = host.decode(manifest.result,
    instance.exports[manifest.entry](physicalArgument));
  assert.deepStrictEqual(result,
    { kind: "scalar", scalarKind: "uint64", value: 18446744073709551615n });
  console.log("PASS concrete initial-runtime Unicode string source");
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const wasmPath = process.argv[2];
  const stringWasmPath = process.argv[3];
  if (!wasmPath || !stringWasmPath) {
    console.error(
      "usage: node run-concrete-source-artifacts.mjs NAT_LIST_WASM STRING_WASM",
    );
    process.exit(2);
  }
  await runConcreteNatListSource(wasmPath);
  await runConcreteStringSource(stringWasmPath);
}
