import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

function exported(instance, name) {
  const value = instance.exports[name];
  assert.equal(typeof value, "function",
    `missing resident arbitrary-precision numeric export ${name}`);
  return value;
}

function synchronize(host) {
  host.synchronizeResidentFrontierBeforeImport();
}

function naturalInput(host, value) {
  synchronize(host);
  const result = host.allocateNatural(BigInt(value)) | 0;
  synchronize(host);
  return result;
}

function integerInput(host, value) {
  synchronize(host);
  const result = host.allocateInteger(BigInt(value)) | 0;
  synchronize(host);
  return result;
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

function checkNaturalAddition(host, natAdd, {
  left,
  right,
  leftClass,
  rightClass,
  resultClass,
}) {
  const leftInput = naturalInput(host, left);
  const rightInput = naturalInput(host, right);
  assert.equal(host.classify(leftInput), leftClass,
    `unexpected concrete class for Nat.add left operand ${left}`);
  assert.equal(host.classify(rightInput), rightClass,
    `unexpected concrete class for Nat.add right operand ${right}`);
  const result = natAdd(leftInput, rightInput);
  assert.equal(host.classify(result), resultClass,
    `unexpected concrete class for Nat.add result ${left} + ${right}`);
  assert.equal(naturalValue(host, result), left + right);
}

function checkStackSafeWalkers(host, {
  intOfNat,
  natAdd,
  natDecEq,
  natSub,
}) {
  const limbCount = 8192n;
  const highBit = 1n << (64n * limbCount);
  const allLowerLimbs = highBit - 1n;

  assert.equal(natDecEq(
    naturalInput(host, highBit + 9n),
    naturalInput(host, highBit + 9n),
  ), 1);
  assert.equal(naturalValue(host, natAdd(
    naturalInput(host, allLowerLimbs),
    naturalInput(host, 1n),
  )), highBit);
  assert.equal(naturalValue(host, natSub(
    naturalInput(host, highBit),
    naturalInput(host, 1n),
  )), allLowerLimbs);
  assert.equal(integerValue(host, intOfNat(
    naturalInput(host, highBit),
  )), highBit);
}

export async function checkResidentBigNumeric({ bytes, manifest }) {
  const host = new ConcreteHost(
    manifest.imports,
    undefined,
    concreteArtifactExternalRegistry,
    manifest.closureDispatch,
    manifest.closureDescriptors,
  );
  const { instance } = await instantiateModuleArtifact({ bytes, manifest, host });
  const module = new WebAssembly.Module(bytes);
  assert.equal(WebAssembly.Module.imports(module).length, manifest.imports.length,
    "arbitrary-precision numeric Wasm and manifest import counts must agree");
  assert.ok([0, 2, 14].includes(manifest.imports.length),
    "arbitrary-precision numeric fixture must be standalone or a linked prettyM checkpoint");

  const intOfNat = exported(instance, "fir_big_ext_Int_ofNat");
  const intDecLt = exported(instance, "fir_big_ext_Int_decLt");
  const intNatAbs = exported(instance, "fir_big_ext_Int_natAbs");
  const intSub = exported(instance, "fir_big_ext_Int_sub");
  const intAdd = exported(instance, "fir_big_ext_Int_add");
  const natAdd = exported(instance, "fir_big_ext_Nat_add");
  const natDecEq = exported(instance, "fir_big_ext_Nat_decEq");
  const natSub = exported(instance, "fir_big_ext_Nat_sub");
  const natDecLt = exported(instance, "fir_big_ext_Nat_decLt");
  const natDecLe = exported(instance, "fir_big_ext_Nat_decLe");

  const n256 = 1n << 256n;
  const n384 = 1n << 384n;
  const a = n256 + (1n << 129n) + 0x123456789abcdefn;
  const b = (1n << 192n) + (1n << 64n) + 0xfedcba987654321n;

  const maxImmediate = 2147483647n;
  checkNaturalAddition(host, natAdd, {
    left: maxImmediate - 2n,
    right: 1n,
    leftClass: "immediate",
    rightClass: "immediate",
    resultClass: "immediate",
  });
  checkNaturalAddition(host, natAdd, {
    left: maxImmediate - 1n,
    right: 1n,
    leftClass: "immediate",
    rightClass: "immediate",
    resultClass: "immediate",
  });
  checkNaturalAddition(host, natAdd, {
    left: maxImmediate,
    right: 1n,
    leftClass: "immediate",
    rightClass: "immediate",
    resultClass: "heap",
  });
  checkNaturalAddition(host, natAdd, {
    left: maxImmediate,
    right: maxImmediate,
    leftClass: "immediate",
    rightClass: "immediate",
    resultClass: "heap",
  });
  checkNaturalAddition(host, natAdd, {
    left: maxImmediate + 1n,
    right: 1n,
    leftClass: "heap",
    rightClass: "immediate",
    resultClass: "heap",
  });
  checkNaturalAddition(host, natAdd, {
    left: maxImmediate + 1n,
    right: maxImmediate + 2n,
    leftClass: "heap",
    rightClass: "heap",
    resultClass: "heap",
  });

  assert.equal(naturalValue(host,
    natAdd(naturalInput(host, a), naturalInput(host, b))), a + b);
  assert.equal(naturalValue(host,
    natAdd(naturalInput(host, n256 - 1n), naturalInput(host, 1n))), n256);
  assert.equal(naturalValue(host,
    natSub(naturalInput(host, a + b), naturalInput(host, b))), a);
  assert.equal(naturalValue(host,
    natSub(naturalInput(host, 1n << 128n),
      naturalInput(host, (1n << 128n) - 5n))), 5n);
  assert.equal(naturalValue(host,
    natSub(naturalInput(host, b), naturalInput(host, a))), 0n);
  assert.equal(natDecEq(naturalInput(host, n384 + 9n),
    naturalInput(host, n384 + 9n)), 1);
  assert.equal(natDecLt(naturalInput(host, n384 - 1n),
    naturalInput(host, n384)), 1);
  assert.equal(natDecLe(naturalInput(host, n384),
    naturalInput(host, n384)), 1);

  const persistentNatural = naturalInput(host, n384);
  host.markPersistentWord(persistentNatural);
  assert.equal(host.readHeader(persistentNatural).persistent, true);
  assert.equal(natDecLt(naturalInput(host, n384 - 1n), persistentNatural), 1,
    "Nat.decLt rejected a persistent arbitrary-limb Natural");

  assert.equal(integerValue(host, intOfNat(naturalInput(host, a))), a);
  assert.equal(naturalValue(host, intNatAbs(integerInput(host, -a))), a);
  assert.equal(integerValue(host,
    intAdd(integerInput(host, a), integerInput(host, b))), a + b);
  assert.equal(integerValue(host,
    intAdd(integerInput(host, -a), integerInput(host, -b))), -(a + b));
  assert.equal(integerValue(host,
    intAdd(integerInput(host, -a), integerInput(host, a))), 0n);
  assert.equal(integerValue(host,
    intSub(integerInput(host, a), integerInput(host, a - 7n))), 7n);
  assert.equal(integerValue(host,
    intSub(integerInput(host, -a), integerInput(host, b))), -(a + b));
  assert.equal(intDecLt(integerInput(host, -(n384 + 1n)),
    integerInput(host, -n384)), 1);
  assert.equal(intDecLt(integerInput(host, n384),
    integerInput(host, -n384)), 0);

  const persistentInteger = integerInput(host, -n384);
  host.markPersistentWord(persistentInteger);
  assert.equal(host.readHeader(persistentInteger).persistent, true);
  assert.equal(intDecLt(persistentInteger, integerInput(host, n384)), 1,
    "Int.decLt rejected a persistent arbitrary-limb Integer");

  if (manifest.walkerControl !== undefined) {
    assert.equal(manifest.walkerControl, "structured-loop",
      "arbitrary-precision numeric walker control changed");
    checkStackSafeWalkers(host, {
      intOfNat,
      natAdd,
      natDecEq,
      natSub,
    });
  }

  return "PASS stack-safe Wasm-resident arbitrary-precision Nat/Int prettyM operations";
}

export async function checkFetchedResidentBigNumeric(artifactUrl) {
  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  assert.ok(moduleResponse.ok,
    `failed to fetch resident big-numeric module: HTTP ${moduleResponse.status}`);
  assert.ok(descriptorResponse.ok,
    `failed to fetch resident big-numeric descriptor: HTTP ${descriptorResponse.status}`);
  return checkResidentBigNumeric({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await descriptorResponse.json(),
  });
}
