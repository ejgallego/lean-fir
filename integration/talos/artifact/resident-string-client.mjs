import assert from "../../../scripts/wasm_assert.mjs";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteHost } from "./concrete-host.mjs";
import { instantiateModuleArtifact } from "./module-client.mjs";

function exported(instance, name) {
  const value = instance.exports[name];
  assert.equal(typeof value, "function", `missing resident String export ${name}`);
  return value;
}

function optionalExport(instance, name) {
  const value = instance.exports[name];
  if (value !== undefined) {
    assert.equal(typeof value, "function", `${name} must be a function`);
  }
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
  const publicAppend = optionalExport(instance, "fir_ext_String_append");
  const publicPush = optionalExport(instance, "fir_ext_String_push");
  const positionNext = optionalExport(instance, "fir_ext_String_Pos_next");
  const decodeChar = optionalExport(instance, "fir_ext_String_decodeChar");
  const usizeRepr = exported(instance, "fir_ext_USize_repr");

  const zeroPushSource = stringInput(host, "unique");
  const zeroPushFrontier = instance.exports.fir_heap_frontier();
  const zeroPushResult = pushn(
    zeroPushSource, 0x21, naturalInput(host, 0n));
  assert.equal(zeroPushResult, zeroPushSource,
    "String.Internal.pushn zero must return its owned source");
  assert.equal(instance.exports.fir_heap_frontier(), zeroPushFrontier,
    "String.Internal.pushn zero must not allocate");

  const reusableLeft = stringInput(host, "abc");
  const reusableRight = stringInput(host, "d");
  const reusableRightHeader = host.readHeader(reusableRight);
  const reusableFrontier = instance.exports.fir_heap_frontier();
  const reusedAppend = append(reusableLeft, reusableRight);
  assert.equal(reusedAppend, reusableLeft,
    "String append must reuse an exclusive input with capacity");
  assert.equal(instance.exports.fir_heap_frontier(), reusableFrontier,
    "reused String append must not allocate");
  assert.equal(stringValue(host, reusedAppend), "abcd",
    "reused String append payload");
  assert.equal(host.readHeader(reusableRight).rc, reusableRightHeader.rc,
    "String append consumed its borrowed right input");

  const growthLeft = stringInput(host, "12345678");
  const growthRight = stringInput(host, "9");
  const grownAppend = append(growthLeft, growthRight);
  assert.notEqual(grownAppend, growthLeft,
    "full exclusive String did not grow");
  assert.equal(stringValue(host, grownAppend), "123456789",
    "grown String append payload");
  assert.equal(host.readHeader(growthLeft, false).live, false,
    "grown String append did not consume its exclusive input");
  const grownHeader = host.readHeader(grownAppend);
  assert.ok(grownHeader.bytes - 32 > grownHeader.aux1,
    "grown String did not retain spare capacity");
  const grownFrontier = instance.exports.fir_heap_frontier();
  const grownAgain = pushn(grownAppend, 0x21, naturalInput(host, 1n));
  assert.equal(grownAgain, grownAppend,
    "grown String did not reuse retained capacity");
  assert.equal(instance.exports.fir_heap_frontier(), grownFrontier,
    "String push within grown capacity allocated");
  assert.equal(stringValue(host, grownAgain), "123456789!",
    "String push within grown capacity payload");

  const sharedLeft = stringInput(host, "share");
  host.writeHeader(sharedLeft, { ...host.readHeader(sharedLeft), rc: 2 });
  const sharedRight = stringInput(host, "d");
  const sharedAppend = append(sharedLeft, sharedRight);
  assert.notEqual(sharedAppend, sharedLeft,
    "String append mutated a shared input");
  assert.equal(host.readHeader(sharedLeft).rc, 1,
    "String append did not consume one shared input reference");
  assert.equal(stringValue(host, sharedLeft), "share",
    "String append mutated a shared alias");
  assert.equal(stringValue(host, sharedAppend), "shared",
    "shared String append payload");
  assert.equal(host.readHeader(sharedRight).rc, 1,
    "shared String append consumed its borrowed right input");

  const persistentLeft = stringInput(host, "fixed");
  host.markPersistentWord(persistentLeft);
  const persistentRight = stringInput(host, "!");
  const persistentAppend = append(persistentLeft, persistentRight);
  assert.notEqual(persistentAppend, persistentLeft,
    "String append mutated a persistent input");
  assert.equal(stringValue(host, persistentLeft), "fixed",
    "String append changed persistent source bytes");
  assert.equal(stringValue(host, persistentAppend), "fixed!",
    "persistent String append payload");
  assert.equal(host.readHeader(persistentLeft).persistent, true,
    "String append changed persistent source ownership");

  let pushed = stringInput(host, "");
  pushed = pushn(pushed, 0x61, naturalInput(host, 1n));
  const pushCapacityFrontier = instance.exports.fir_heap_frontier();
  for (let index = 0; index < 7; index += 1) {
    const next = pushn(pushed, 0x61, naturalInput(host, 1n));
    assert.equal(next, pushed,
      `String push did not reuse capacity at step ${index}`);
    pushed = next;
  }
  assert.equal(instance.exports.fir_heap_frontier(), pushCapacityFrontier,
    "repeated String pushes within capacity allocated");
  assert.equal(stringValue(host, pushed), "aaaaaaaa",
    "repeated String push payload");

  assert.equal(stringValue(host,
    append(stringInput(host, "λ"), stringInput(host, "💩"))), "λ💩");
  if (publicAppend !== undefined) {
    assert.equal(stringValue(host,
      publicAppend(stringInput(host, "λ"), stringInput(host, "💩"))), "λ💩");
  }
  assert.equal(stringValue(host,
    pushn(stringInput(host, "x"), 0x1f4a9, naturalInput(host, 2n))),
  "x💩💩");
  assert.equal(stringValue(host,
    pushn(stringInput(host, ""), 0x03bb, naturalInput(host, 3n))),
  "λλλ");
  if (publicPush !== undefined) {
    assert.equal(stringValue(host,
      publicPush(stringInput(host, "x"), 0x1f4a9)), "x💩");
  }
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
  if (positionNext !== undefined) {
    assert.equal(naturalValue(host,
      positionNext(stringInput(host, "A💩λ"), naturalInput(host, 1n), 0)), 5n);
  }
  if (decodeChar !== undefined) {
    assert.equal(decodeChar(
      stringInput(host, "A💩λ"), naturalInput(host, 0n), 0), 0x41);
    assert.equal(decodeChar(
      stringInput(host, "A💩λ"), naturalInput(host, 1n), 0), 0x1f4a9);
    assert.equal(decodeChar(
      stringInput(host, "A💩λ"), naturalInput(host, 5n), 0), 0x03bb);
  }
  for (const value of [
    0n,
    1n,
    9n,
    10n,
    307n,
    0xffffffffn,
    0x100000000n,
    0x0123456789abcdefn,
    0xffffffffffffffffn,
  ]) {
    assert.equal(stringValue(host, usizeRepr(value)), value.toString(),
      `USize.repr(${value})`);
  }

  expectTrap(() =>
    pushn(stringInput(host, ""), 0x110000, naturalInput(host, 1n)),
  "out-of-range Unicode scalar must trap");
  if (decodeChar !== undefined) {
    expectTrap(() =>
      decodeChar(stringInput(host, "A"), naturalInput(host, 1n), 0),
    "past-end String.decodeChar must trap");
  }
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
