import assert from "node:assert/strict";

import { ConcreteHost } from "./concrete-host.mjs";

const FLOAT32_NEGATIVE_ZERO = 0x80000000n;
const FLOAT32_NAN_PAYLOAD = 0x7fc01234n;
const FLOAT64_NEGATIVE_ZERO = 0x8000000000000000n;
const FLOAT64_NAN_PAYLOAD = 0x7ff8000000000042n;

const scalarFields = [
  { width: 2, offset: 0, value: { kind: "uint8", value: "171" } },
  { width: 2, offset: 1, value: { kind: "uint16", value: "52719" } },
  { width: 2, offset: 3, value: { kind: "uint32", value: "2309737967" } },
  { width: 2, offset: 7, value: { kind: "uint64", value: "18446744073709551615" } },
  {
    width: 2,
    offset: 15,
    value: { kind: "float32", value: FLOAT32_NEGATIVE_ZERO.toString() },
  },
  {
    width: 2,
    offset: 19,
    value: { kind: "float", value: FLOAT64_NAN_PAYLOAD.toString() },
  },
];

function initialRuntime(fields = scalarFields) {
  return {
    nextLocation: 1,
    heap: [{
      location: 0,
      rc: 3,
      persistent: false,
      live: true,
      object: {
        kind: "ctor",
        tag: "9",
        objectFields: [
          { kind: "object", reference: { kind: "tagged", payload: "7" } },
        ],
        usizeFields: ["18446744073709551615"],
        scalarFields: fields,
      },
    }],
  };
}

const runtime = initialRuntime();
const host = new ConcreteHost([], runtime);
const address = host.locationAddresses.get(0);
assert.notEqual(address, undefined);
const header = host.readHeader(address);
assert.equal(header.kind, 1);
assert.equal(header.aux0, 9);
assert.equal(header.aux1, 1);
assert.equal(header.aux2, 1);
assert.equal(header.aux3, 27);
assert.equal(header.bytes, 80);
assert.equal(header.rc, 3);
assert.deepStrictEqual(host.objectJson(address, header), runtime.heap[0].object);

// A constructor slot has no runtime tag of its own. Track the physical kind
// supplied by the latest mutation so an object-only slot can subsequently hold
// a tagged value and still be decoded faithfully.
const mutationHost = new ConcreteHost([]);
const largeNatural = mutationHost.allocateNatural(1n << 64n);
const mutable = mutationHost.allocCtor({
  fields: ["object"],
  size: 1,
  usize: 0,
  ssize: 0,
  tag: "0",
}, [largeNatural]);
mutationHost.objectSet({ index: 0, field: "tobject" }, [
  mutable,
  mutationHost.encode("tobject", { kind: "tagged", payload: 29n }),
]);
assert.deepStrictEqual(
  mutationHost.objectJson(mutable, mutationHost.readHeader(mutable)),
  {
    kind: "ctor",
    tag: "0",
    objectFields: [
      { kind: "object", reference: { kind: "tagged", payload: "29" } },
    ],
    usizeFields: [],
    scalarFields: [],
  },
);

for (const field of scalarFields) {
  const physical = host.scalarProj({
    kind: "scalarProj",
    width: field.width,
    offset: field.offset,
    result: field.value.kind,
  }, [address]);
  assert.deepStrictEqual(host.decode(field.value.kind, physical), {
    kind: "scalar",
    scalarKind: field.value.kind,
    value: BigInt(field.value.value),
  });
}

for (const [kind, offset, bits] of [
  ["float32", 15, FLOAT32_NAN_PAYLOAD],
  ["float", 19, FLOAT64_NEGATIVE_ZERO],
]) {
  host.scalarSet({
    kind: "scalarSet",
    width: 2,
    offset,
    field: kind,
  }, [address, host.encode(kind, {
    kind: "scalar",
    scalarKind: kind,
    value: bits,
  })]);
  const physical = host.scalarProj({
    kind: "scalarProj",
    width: 2,
    offset,
    result: kind,
  }, [address]);
  assert.deepStrictEqual(host.decode(kind, physical), {
    kind: "scalar",
    scalarKind: kind,
    value: bits,
  });
}

assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 1, offset: 0, value: { kind: "uint8", value: "0" } },
])), /scalar width must equal its fixed-slot prefix/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0, value: { kind: "uint8", value: "256" } },
])), /uint8 scalar is out of uint8 range/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0, value: { kind: "uint16", value: "258" } },
  { width: 2, offset: 1, value: { kind: "uint8", value: "2" } },
])), /overlapping initial constructor scalar fields disagree/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0xffffffff, value: { kind: "uint8", value: "0" } },
])), /packed scalar extent must fit UInt32/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0, value: { kind: "float32", value: "4294967296" } },
])), /float32 scalar is out of float32 range/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0, value: { kind: "float", value: "01" } },
])), /must use a canonical unsigned decimal string/);

console.log("PASS concrete packed initial-runtime constructors");
