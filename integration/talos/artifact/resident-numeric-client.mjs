import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

function exported(instance, name) {
  const value = instance.exports[name];
  assert.equal(typeof value, "function", `missing resident numeric export ${name}`);
  return value;
}

function synchronize(host) {
  host.synchronizeResidentFrontierBeforeImport();
}

function naturalInput(host, value) {
  synchronize(host);
  return host.allocateNatural(BigInt(value)) | 0;
}

function integerInput(host, value) {
  synchronize(host);
  return host.allocateInteger(BigInt(value)) | 0;
}

function naturalValue(host, physical) {
  synchronize(host);
  const word = physical >>> 0;
  if (host.classify(word) === "immediate") return host.decodeImmediate(word);
  const header = host.readHeader(word);
  if (header.persistent && header.kind === 5 && header.aux0 === 1) {
    return host.readU64(word + 32);
  }
  return host.readNatural(word, header);
}

function integerValue(host, physical) {
  synchronize(host);
  const word = physical >>> 0;
  if (host.classify(word) === "immediate") {
    return BigInt.asIntN(32, host.decodeImmediate(word));
  }
  const header = host.readHeader(word);
  if (header.persistent && header.kind === 5 && header.aux0 === 1) {
    return BigInt.asIntN(32, host.readU64(word + 32));
  }
  return host.readInteger(word, header);
}

function expectTrap(action, message) {
  let trapped = false;
  try {
    action();
  } catch (error) {
    assert.ok(error instanceof WebAssembly.RuntimeError,
      `${message}: expected WebAssembly.RuntimeError, got ${error}`);
    trapped = true;
  }
  assert.ok(trapped, message);
}

export async function checkResidentNumeric({ bytes, manifest }) {
  const host = new ConcreteHost(
    manifest.imports,
    undefined,
    concreteArtifactExternalRegistry,
    manifest.closureDispatch,
    manifest.closureDescriptors,
  );
  const { instance } = await instantiateModuleArtifact({ bytes, manifest, host });
  const importCount =
    WebAssembly.Module.imports(new WebAssembly.Module(bytes)).length;
  assert.equal(importCount, manifest.imports.length,
    "resident numeric Wasm and manifest import counts must agree");
  assert.ok(importCount === 0 || importCount === 14,
    `resident numeric test expects a standalone or linked checkpoint, got ${importCount} imports`);

  const intOfNat = exported(instance, "fir_ext_Int_ofNat");
  const intDecLt = exported(instance, "fir_ext_Int_decLt");
  const intNatAbs = exported(instance, "fir_ext_Int_natAbs");
  const intSub = exported(instance, "fir_ext_Int_sub");
  const intAdd = exported(instance, "fir_ext_Int_add");
  const natAdd = exported(instance, "fir_ext_Nat_add");
  const natDecEq = exported(instance, "fir_ext_Nat_decEq");
  const natSub = exported(instance, "fir_ext_Nat_sub");
  const natDecLt = exported(instance, "fir_ext_Nat_decLt");
  const natDecLe = exported(instance, "fir_ext_Nat_decLe");

  assert.equal(integerValue(host, intOfNat(naturalInput(host, 0x80000000n))),
    0x80000000n);
  assert.equal(integerValue(host,
    intAdd(integerInput(host, 0x7fffffffn), integerInput(host, 1n))),
  0x80000000n);
  assert.equal(integerValue(host,
    intSub(integerInput(host, -0x80000000n), integerInput(host, 1n))),
  -0x80000001n);
  assert.equal(integerValue(host,
    intAdd(integerInput(host, -5n), integerInput(host, 3n))), -2n);
  assert.equal(integerValue(host,
    intAdd(integerInput(host, -5n), integerInput(host, -7n))), -12n);
  assert.equal(integerValue(host,
    intSub(integerInput(host, 3n), integerInput(host, 8n))), -5n);
  assert.equal(intDecLt(
    integerInput(host, -0x80000001n), integerInput(host, 0x80000000n)), 1);
  assert.equal(intDecLt(
    integerInput(host, -8n), integerInput(host, -3n)), 1);
  assert.equal(intDecLt(
    integerInput(host, 8n), integerInput(host, -3n)), 0);
  assert.equal(naturalValue(host,
    intNatAbs(integerInput(host, -0x8000000000000001n))),
  0x8000000000000001n);

  const huge = 0x8000000000000000n;
  assert.equal(naturalValue(host,
    natAdd(naturalInput(host, huge), naturalInput(host, 9n))), huge + 9n);
  assert.equal(naturalValue(host,
    natSub(naturalInput(host, 3n), naturalInput(host, 8n))), 0n);
  assert.equal(natDecEq(
    naturalInput(host, huge), naturalInput(host, huge)), 1);
  assert.equal(natDecLt(
    naturalInput(host, 3n), naturalInput(host, 8n)), 1);
  assert.equal(natDecLe(
    naturalInput(host, 8n), naturalInput(host, 8n)), 1);

  expectTrap(() =>
    natAdd(naturalInput(host, 0xffffffffffffffffn), naturalInput(host, 1n)),
  "one-limb Natural overflow must trap instead of wrapping");
  expectTrap(() =>
    natDecEq(naturalInput(host, 0x10000000000000000n), naturalInput(host, 0n)),
  "multi-limb Natural input must remain fail-closed");
  expectTrap(() =>
    intNatAbs(integerInput(host, -0x10000000000000000n)),
  "multi-limb Integer input must remain fail-closed");

  return "PASS Wasm-resident one-limb Nat/Int prettyM operations";
}

export async function checkFetchedResidentNumeric(artifactUrl) {
  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  assert.ok(moduleResponse.ok,
    `failed to fetch resident numeric module: HTTP ${moduleResponse.status}`);
  assert.ok(descriptorResponse.ok,
    `failed to fetch resident numeric descriptor: HTTP ${descriptorResponse.status}`);
  return checkResidentNumeric({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await descriptorResponse.json(),
  });
}
