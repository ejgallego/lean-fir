import assert from "node:assert/strict";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import { ConcreteFault, ConcreteHost } from "./concrete-host.mjs";

const concreteDeclarations = [
  "Nat.add",
  "Nat.decEq",
  "Nat.decLe",
  "Nat.decLt",
  "Nat.sub",
  "String.Internal.append",
  "String.Internal.extract",
  "String.Internal.length",
  "String.Internal.next",
  "String.Internal.offsetOfPos",
  "String.Internal.posOf",
  "String.Internal.pushn",
  "String.utf8ByteSize",
  "instInhabitedOfMonad._redArg",
  "panicCore",
];
for (const declaration of concreteDeclarations) {
  assert.ok(Object.hasOwn(concreteArtifactExternalRegistry, declaration),
    `concrete Format registry is missing ${declaration}`);
}
const pendingIntegerDeclarations = [
  "Int.add", "Int.decLt", "Int.natAbs", "Int.ofNat", "Int.sub",
];
for (const declaration of pendingIntegerDeclarations) {
  assert.ok(!Object.hasOwn(concreteArtifactExternalRegistry, declaration),
    `concrete Format registry admitted W6-dependent ${declaration}`);
}

function natural(host, value) {
  return host.decode("tobject", host.allocateNatural(value));
}

function readNatural(host, value) {
  if (value.kind === "tagged") return value.payload;
  assert.equal(value.kind, "heap");
  return host.readNatural(host.addressOf(value.location));
}

function string(host, value) {
  return host.decode("object", host.allocateString(value));
}

function readString(host, value) {
  assert.equal(value.kind, "heap");
  return host.readString(host.addressOf(value.location));
}

function scalar(kind, value) {
  return { kind: "scalar", scalarKind: kind, value: BigInt(value) };
}

function invoke(host, declaration, params, result, args) {
  const external = host.importFunction({
    kind: "external",
    declaration,
    params,
    results: [result],
  });
  const physicalArgs = params.map((kind, index) => host.encode(kind, args[index]));
  return host.decode(result, external(...physicalArgs));
}

const host = new ConcreteHost([], undefined, concreteArtifactExternalRegistry);
const huge = 0x8000000000000000n;

assert.equal(readNatural(host, invoke(host, "Nat.add",
  ["tobject", "tobject"], "tobject", [natural(host, huge), natural(host, 9n)])), huge + 9n);
assert.equal(readNatural(host, invoke(host, "Nat.sub",
  ["tobject", "tobject"], "tobject", [natural(host, 3n), natural(host, 8n)])), 0n);
assert.deepStrictEqual(invoke(host, "Nat.decEq",
  ["tobject", "tobject"], "uint8", [natural(host, huge), natural(host, huge)]),
  scalar("uint8", 1n));
assert.deepStrictEqual(invoke(host, "Nat.decLt",
  ["tobject", "tobject"], "uint8", [natural(host, 3n), natural(host, 8n)]),
  scalar("uint8", 1n));
assert.deepStrictEqual(invoke(host, "Nat.decLe",
  ["tobject", "tobject"], "uint8", [natural(host, 8n), natural(host, 8n)]),
  scalar("uint8", 1n));

assert.equal(readString(host, invoke(host, "String.Internal.append",
  ["object", "object"], "object", [string(host, "α"), string(host, " β")])), "α β");
assert.equal(readString(host, invoke(host, "String.Internal.pushn",
  ["object", "uint32", "tobject"], "object",
  [string(host, "\n"), scalar("uint32", 32n), natural(host, 3n)])), "\n   ");
assert.equal(readNatural(host, invoke(host, "String.Internal.length",
  ["object"], "tobject", [string(host, "α😀x")])), 3n);
assert.equal(readNatural(host, invoke(host, "String.Internal.posOf",
  ["object", "uint32"], "tobject", [string(host, "xαβ"), scalar("uint32", 0x03b1n)])), 1n);
assert.equal(readNatural(host, invoke(host, "String.Internal.offsetOfPos",
  ["object", "tobject"], "tobject", [string(host, "xαβ"), natural(host, 3n)])), 2n);
assert.equal(readNatural(host, invoke(host, "String.utf8ByteSize",
  ["object"], "tagged", [string(host, "xαβ")])), 5n);
assert.equal(readString(host, invoke(host, "String.Internal.extract",
  ["object", "tobject", "tobject"], "object",
  [string(host, "xαβ"), natural(host, 1n), natural(host, 3n)])), "α");
assert.equal(readNatural(host, invoke(host, "String.Internal.next",
  ["object", "tobject"], "tobject", [string(host, "xαβ"), natural(host, 1n)])), 3n);

assert.equal(host.world, 0);
assert.deepStrictEqual(host.trace.map((event) => event.name), [
  "Nat.add",
  "Nat.sub",
  "Nat.decEq",
  "Nat.decLt",
  "Nat.decLe",
  "String.Internal.append",
  "String.Internal.pushn",
  "String.Internal.length",
  "String.Internal.posOf",
  "String.Internal.offsetOfPos",
  "String.utf8ByteSize",
  "String.Internal.extract",
  "String.Internal.next",
]);

assert.throws(() => invoke(host, "Nat.add", ["tobject", "tobject"], "tobject",
  [string(host, "wrong kind"), natural(host, 1n)]), /expected a concrete natural object/);

const deletedAddress = host.allocateString("deleted");
const deletedValue = host.decode("object", deletedAddress);
host.deleteObject([deletedAddress]);
assert.throws(() => invoke(host, "String.Internal.length", ["object"], "tobject",
  [deletedValue]), (error) => error instanceof ConcreteFault &&
    error.fault.kind === "deadObject" && error.fault.location === deletedValue.location);

for (const [declaration, params, result, args] of [
  ["panicCore", ["erased", "tobject", "object"], "tobject",
    [{ kind: "erased" }, natural(host, 0n), string(host, "panic")]],
  ["instInhabitedOfMonad._redArg", ["object", "tobject"], "object",
    [string(host, "fallback"), natural(host, 0n)]],
]) {
  assert.throws(() => invoke(host, declaration, params, result, args),
    (error) => error instanceof ConcreteFault &&
      error.fault.kind === "externalFailure" && error.fault.name === declaration &&
      error.fault.message === "unreachable Lean pretty-printing panic helper executed");
}

assert.equal(host.trace.length, 13, "failed concrete Format externals polluted the trace");
console.log("PASS concrete Format Nat/String external families");
