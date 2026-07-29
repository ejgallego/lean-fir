import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

function exported(instance, name) {
  const value = instance.exports[name];
  assert.equal(typeof value, "function", `missing resident String export ${name}`);
  return value;
}

function synchronize(host) {
  host.synchronizeResidentFrontierBeforeImport();
}

function stringInput(host, value) {
  synchronize(host);
  const result = host.allocateString(value) | 0;
  synchronize(host);
  return result;
}

function naturalInput(host, value) {
  synchronize(host);
  const result = host.allocateNatural(BigInt(value)) | 0;
  synchronize(host);
  return result;
}

function stringValue(host, physical) {
  synchronize(host);
  return host.readString(physical >>> 0);
}

function naturalValue(host, physical) {
  synchronize(host);
  const word = physical >>> 0;
  if (host.classify(word) === "immediate") return host.decodeImmediate(word);
  return host.readNatural(word, host.readHeader(word));
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

export async function checkResidentString({ bytes, manifest }) {
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
    "resident String Wasm and manifest import counts must agree");
  assert.ok(importCount === 0 || importCount === 2,
    `resident String test expects a standalone or linked checkpoint, got ${importCount} imports`);

  const append = exported(instance, "fir_ext_String_Internal_append");
  const pushn = exported(instance, "fir_ext_String_Internal_pushn");
  const length = exported(instance, "fir_ext_String_Internal_length");
  const posOf = exported(instance, "fir_ext_String_Internal_posOf");
  const offsetOfPos =
    exported(instance, "fir_ext_String_Internal_offsetOfPos");
  const utf8ByteSize = exported(instance, "fir_ext_String_utf8ByteSize");
  const extract = exported(instance, "fir_ext_String_Internal_extract");
  const next = exported(instance, "fir_ext_String_Internal_next");

  assert.equal(stringValue(host,
    append(stringInput(host, "λ"), stringInput(host, "💩"))), "λ💩");
  assert.equal(stringValue(host,
    pushn(stringInput(host, "x"), 0x1f4a9, naturalInput(host, 2n))),
  "x💩💩");
  assert.equal(stringValue(host,
    pushn(stringInput(host, ""), 0x03bb, naturalInput(host, 3n))),
  "λλλ");
  assert.equal(naturalValue(host,
    length(stringInput(host, "A💩λ"))), 3n);
  assert.equal(naturalValue(host,
    posOf(stringInput(host, "A💩λ💩"), 0x03bb)), 5n);
  assert.equal(naturalValue(host,
    posOf(stringInput(host, "A💩λ💩"), 0x2603)), 11n);
  assert.equal(naturalValue(host,
    offsetOfPos(stringInput(host, "A💩λ"), naturalInput(host, 2n))), 2n);
  assert.equal(naturalValue(host,
    offsetOfPos(stringInput(host, "A💩λ"), naturalInput(host, 5n))), 2n);
  assert.equal(naturalValue(host,
    offsetOfPos(
      stringInput(host, "A💩λ"),
      naturalInput(host, 0x100000000n))), 3n);
  assert.equal(host.taggedPayload(
    utf8ByteSize(stringInput(host, "A💩λ"))), 7n);
  assert.equal(stringValue(host,
    extract(
      stringInput(host, "A💩λB"),
      naturalInput(host, 1n),
      naturalInput(host, 7n))),
  "💩λ");
  assert.equal(stringValue(host,
    extract(
      stringInput(host, "A💩λB"),
      naturalInput(host, 2n),
      naturalInput(host, 7n))),
  "");
  assert.equal(stringValue(host,
    extract(
      stringInput(host, "A💩λB"),
      naturalInput(host, 1n),
      naturalInput(host, 2n))),
  "💩λB");
  assert.equal(naturalValue(host,
    next(stringInput(host, "A💩λ"), naturalInput(host, 1n))), 5n);
  assert.equal(naturalValue(host,
    next(stringInput(host, "A💩λ"), naturalInput(host, 2n))), 3n);
  assert.equal(naturalValue(host,
    next(stringInput(host, "A💩λ"), naturalInput(host, 7n))), 8n);
  assert.equal(naturalValue(host,
    next(
      stringInput(host, "A"),
      naturalInput(host, 0xffffffffn))), 0x100000000n);

  expectTrap(() =>
    pushn(stringInput(host, ""), 0x110000, naturalInput(host, 1n)),
  "out-of-range Unicode scalar must trap");
  const malformed = stringInput(host, "bad") >>> 0;
  new DataView(host.memory.buffer).setUint32(malformed + 16, 99, true);
  expectTrap(() => length(malformed),
    "malformed concrete String marker must trap");

  if (instance.exports.resident_string_empty_literal !== undefined) {
    assert.equal(stringValue(host,
      exported(instance, "resident_string_empty_literal")()), "");
    assert.equal(stringValue(host,
      exported(instance, "resident_string_unicode_literal")()), "λ\n");
  }

  return "PASS zero-import Wasm-resident UTF-8 String prettyM operations";
}

export async function checkFetchedResidentString(artifactUrl) {
  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  assert.ok(moduleResponse.ok,
    `failed to fetch resident String module: HTTP ${moduleResponse.status}`);
  assert.ok(descriptorResponse.ok,
    `failed to fetch resident String descriptor: HTTP ${descriptorResponse.status}`);
  return checkResidentString({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await descriptorResponse.json(),
  });
}
