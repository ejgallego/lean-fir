import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

function exported(instance, name) {
  const value = instance.exports[name];
  assert.equal(typeof value, "function",
    `missing resident Nat arithmetic export ${name}`);
  return value;
}

function expectTrap(action, label) {
  let trapped = false;
  try {
    action();
  } catch (error) {
    trapped = error instanceof WebAssembly.RuntimeError;
  }
  assert.equal(trapped, true, `${label} did not trap`);
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

export async function checkResidentNatArithmetic({ bytes, manifest }) {
  const host = new ConcreteHost(
    manifest.imports,
    undefined,
    concreteArtifactExternalRegistry,
    manifest.closureDispatch,
    manifest.closureDescriptors,
  );
  const { instance } = await instantiateModuleArtifact({ bytes, manifest, host });
  const module = new WebAssembly.Module(bytes);
  assert.equal(WebAssembly.Module.imports(module).length, 0,
    "resident Nat arithmetic artifact must have zero imports");
  assert.equal(manifest.imports.length, 0,
    "resident Nat arithmetic manifest must declare zero imports");

  const mul = exported(instance, "fir_ext_Nat_mul");
  const pow = exported(instance, "fir_ext_Nat_pow");
  const land = exported(instance, "fir_ext_Nat_land");
  const lor = exported(instance, "fir_ext_Nat_lor");
  const div = exported(instance, "fir_ext_Nat_div");
  const mod = exported(instance, "fir_ext_Nat_mod");
  const frontier = exported(instance, "fir_heap_frontier");
  const shiftLeft = exported(instance, "fir_ext_Nat_shiftLeft");
  const shiftRight = exported(instance, "fir_ext_Nat_shiftRight");
  const log2 = exported(instance, "fir_ext_Nat_log2");
  const apply = (operation, left, right) => naturalValue(host,
    operation(naturalInput(host, left), naturalInput(host, right)));
  const applyUnary = (operation, value) => naturalValue(host,
    operation(naturalInput(host, value)));

  assert.equal(apply(mul, 0n, 0n), 0n);
  const immediateMulFrontier = frontier() >>> 0;
  for (const [left, right] of [
    [0n, 0x7fff_ffffn],
    [1n, 0x7fff_ffffn],
    [0x3fff_ffffn, 2n],
  ]) {
    const leftInput = naturalInput(host, left);
    const rightInput = naturalInput(host, right);
    assert.equal(host.classify(leftInput), "immediate");
    assert.equal(host.classify(rightInput), "immediate");
    const result = mul(leftInput, rightInput);
    assert.equal(host.classify(result), "immediate",
      `Nat.mul immediate result was promoted: ${left} * ${right}`);
    assert.equal(naturalValue(host, result), left * right,
      `Nat.mul immediate mismatch: ${left} * ${right}`);
  }
  assert.equal(frontier() >>> 0, immediateMulFrontier,
    "Nat.mul immediate products allocated in the resident heap");
  for (const [left, right] of [
    [0x7fff_ffffn, 2n],
    [0x7fff_ffffn, 0x7fff_ffffn],
  ]) {
    const result = mul(naturalInput(host, left), naturalInput(host, right));
    assert.notEqual(host.classify(result), "immediate",
      `Nat.mul promoted result stayed immediate: ${left} * ${right}`);
    assert.equal(naturalValue(host, result), left * right,
      `Nat.mul promoted mismatch: ${left} * ${right}`);
  }
  assert.equal(apply(mul, 0xffff_ffffn, 0xffff_ffffn),
    0xffff_fffe_0000_0001n);
  const mulLeft = (1n << 257n) + (1n << 129n) + 3n;
  const mulRight = (1n << 193n) + (1n << 65n) + 5n;
  assert.equal(apply(mul, mulLeft, mulRight), mulLeft * mulRight);
  expectTrap(() => mul(0, naturalInput(host, 1n)),
    "Nat.mul malformed heap left operand");
  expectTrap(() => mul(naturalInput(host, 1n), 0),
    "Nat.mul malformed heap right operand");

  assert.equal(apply(pow, 0n, 0n), 1n);
  assert.equal(apply(pow, 3n, 0n), 1n);
  assert.equal(apply(pow, 3n, 80n), 3n ** 80n);
  const powBase = (1n << 64n) + 3n;
  assert.equal(apply(pow, powBase, 5n), powBase ** 5n);

  const maskLeft = (1n << 385n) - 1n;
  const maskRight = (1n << 384n) | (1n << 192n) | 0x1234_5678n;
  assert.equal(apply(land, maskLeft, maskRight), maskLeft & maskRight);
  assert.equal(apply(land, 1n << 256n, (1n << 256n) - 1n), 0n);
  for (const [left, right] of [
    [0n, 0n],
    [1n, 1n << 384n],
    [(1n << 385n) - 1n, (1n << 192n) | 0x1234_5678n],
    [(1n << 129n) + 3n, (1n << 521n) + (1n << 65n)],
  ]) {
    assert.equal(apply(lor, left, right), left | right,
      `Nat.lor(${left}, ${right})`);
  }

  assert.equal(apply(div, 5n, 0n), 0n);
  assert.equal(apply(div, 0n, 5n), 0n);
  assert.equal(apply(div, 17n, 5n), 3n);
  assert.equal(apply(div, (1n << 63n) + 123n, (1n << 32n) + 7n),
    ((1n << 63n) + 123n) / ((1n << 32n) + 7n));
  const dividend = (1n << 521n) + (1n << 317n) + (1n << 129n) + 99n;
  const divisor = (1n << 257n) + (1n << 64n) + 11n;
  assert.equal(apply(div, dividend, divisor), dividend / divisor);
  assert.equal(apply(div, divisor - 1n, divisor), 0n);

  assert.equal(apply(mod, 5n, 0n), 5n);
  assert.equal(apply(mod, 0n, 5n), 0n);
  assert.equal(apply(mod, 17n, 5n), 2n);
  const immediateFrontier = frontier() >>> 0;
  for (const [left, right] of [
    [0n, 0n],
    [0n, 1n],
    [17n, 5n],
    [0x7fff_ffffn, 2n],
    [0x7fff_ffffn, 0x7fff_fffen],
  ]) {
    const result = mod(naturalInput(host, left), naturalInput(host, right));
    assert.equal(host.classify(result), "immediate",
      `Nat.mod immediate pair returned a non-immediate: ${left} % ${right}`);
    assert.equal(naturalValue(host, result), right === 0n ? left : left % right,
      `Nat.mod immediate pair mismatch: ${left} % ${right}`);
  }
  assert.equal(frontier() >>> 0, immediateFrontier,
    "Nat.mod immediate pairs allocated in the resident heap");
  expectTrap(() => mod(0, naturalInput(host, 1n)),
    "Nat.mod malformed heap left operand");
  expectTrap(() => mod(naturalInput(host, 1n), 0),
    "Nat.mod malformed heap right operand");
  assert.equal(apply(mod, (1n << 63n) + 123n, (1n << 32n) + 7n),
    ((1n << 63n) + 123n) % ((1n << 32n) + 7n));
  assert.equal(apply(mod, dividend, divisor), dividend % divisor);
  assert.equal(apply(mod, divisor - 1n, divisor), divisor - 1n);

  for (const [value, count] of [
    [0n, 65n],
    [1n, 0n],
    [1n, 63n],
    [1n, 64n],
    [1n, 65n],
    [(1n << 130n) + 3n, 67n],
  ]) {
    assert.equal(apply(shiftLeft, value, count), value << count,
      `Nat.shiftLeft(${value}, ${count})`);
  }

  const shiftValue = (1n << 521n) + (1n << 320n) +
    (1n << 129n) + 0x1234_5678_9abcn;
  for (const [value, count] of [
    [0n, 65n],
    [1n, 0n],
    [1n, 64n],
    [(1n << 130n) + 3n, 67n],
    [shiftValue, 0n],
    [shiftValue, 1n],
    [shiftValue, 32n],
    [shiftValue, 63n],
    [shiftValue, 64n],
    [shiftValue, 65n],
    [shiftValue, 257n],
    [shiftValue, 600n],
    [shiftValue, 1n << 64n],
  ]) {
    assert.equal(apply(shiftRight, value, count), value >> count,
      `Nat.shiftRight(${value}, ${count})`);
  }
  expectTrap(() => shiftRight(0, naturalInput(host, 1n)),
    "Nat.shiftRight malformed value");
  expectTrap(() => shiftRight(naturalInput(host, 1n), 0),
    "Nat.shiftRight malformed count");

  for (const [value, expected] of [
    [0n, 0n],
    [1n, 0n],
    [2n, 1n],
    [(1n << 63n) - 1n, 62n],
    [1n << 63n, 63n],
    [1n << 64n, 64n],
    [1n << 65n, 65n],
    [(1n << 257n) + (1n << 129n) + 3n, 257n],
  ]) {
    assert.equal(applyUnary(log2, value), expected, `Nat.log2(${value})`);
  }

  const borrowedLeft = naturalInput(host, mulLeft);
  const borrowedRight = naturalInput(host, mulRight);
  const leftHeader = host.readHeader(borrowedLeft);
  const rightHeader = host.readHeader(borrowedRight);
  assert.equal(naturalValue(host, mul(borrowedLeft, borrowedRight)),
    mulLeft * mulRight);
  assert.equal(host.readHeader(borrowedLeft).rc, leftHeader.rc,
    "Nat.mul consumed its borrowed left input");
  assert.equal(host.readHeader(borrowedRight).rc, rightHeader.rc,
    "Nat.mul consumed its borrowed right input");

  return "PASS zero-import Wasm-resident arbitrary-precision Nat arithmetic";
}

export async function checkFetchedResidentNatArithmetic(artifactUrl) {
  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  assert.ok(moduleResponse.ok,
    `failed to fetch resident Nat arithmetic module: HTTP ${moduleResponse.status}`);
  assert.ok(descriptorResponse.ok,
    `failed to fetch resident Nat arithmetic descriptor: HTTP ${descriptorResponse.status}`);
  return checkResidentNatArithmetic({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await descriptorResponse.json(),
  });
}
