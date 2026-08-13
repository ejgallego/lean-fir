import assert from "node:assert/strict";

import { ConcreteHost } from "./concrete-host.mjs";
import {
  concreteValidationExternalRegistry,
} from "./concrete-validation-external-registry.mjs";

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

function boxedRuntime(scalarKind, value) {
  return {
    nextLocation: 1,
    heap: [{
      location: 0,
      rc: 1,
      persistent: false,
      live: true,
      object: { kind: "boxed", scalarKind, value },
    }],
  };
}

for (const [scalarKind, value, expectedBits] of [
  ["uint8", { kind: "scalar", scalar: { kind: "uint8", value: "255" } }, 255n],
  ["float", {
    kind: "scalar",
    scalar: { kind: "float", value: FLOAT64_NAN_PAYLOAD.toString() },
  }, FLOAT64_NAN_PAYLOAD],
]) {
  const boxedHost = new ConcreteHost([], boxedRuntime(scalarKind, value));
  const boxedAddress = boxedHost.locationAddresses.get(0);
  const boxedHeader = boxedHost.readHeader(boxedAddress);
  assert.equal(boxedHeader.kind, 3);
  assert.equal(boxedHeader.rc, 1);
  assert.deepStrictEqual(
    boxedHost.decode(
      scalarKind,
      boxedHost.unbox({ scalar: scalarKind }, [boxedAddress]),
    ),
    { kind: "scalar", scalarKind, value: expectedBits },
  );
}

assert.throws(() => new ConcreteHost([], boxedRuntime(
  "uint8",
  { kind: "scalar", scalar: { kind: "uint16", value: "255" } },
)), /payload kind mismatch/);
assert.throws(() => new ConcreteHost([], boxedRuntime(
  "float32",
  { kind: "scalar", scalar: { kind: "float32", value: "4294967296" } },
)), /out of float32 range/);

const arrayRuntime = {
  nextLocation: 2,
  heap: [
    {
      location: 1,
      rc: 1,
      persistent: false,
      live: true,
      object: {
        kind: "array",
        elements: [
          { kind: "object", reference: { kind: "heap", location: 0 } },
          { kind: "object", reference: { kind: "tagged", payload: "1" } },
        ],
        capacity: 4,
      },
    },
    {
      location: 0,
      rc: 1,
      persistent: false,
      live: true,
      object: {
        kind: "boxed",
        scalarKind: "uint8",
        value: { kind: "scalar", scalar: { kind: "uint8", value: "255" } },
      },
    },
  ],
};
const arrayHost = new ConcreteHost([], arrayRuntime);
const arrayAddress = arrayHost.addressOf(1);
const arrayHeader = arrayHost.readHeader(arrayAddress);
assert.equal(arrayHeader.kind, 8);
assert.equal(arrayHeader.aux0, 0x41525259);
assert.equal(arrayHeader.aux1, 2);
assert.equal(arrayHeader.aux2, 4);
assert.equal(arrayHeader.bytes, 64);
assert.deepStrictEqual(arrayHost.objectJson(arrayAddress, arrayHeader),
  arrayRuntime.heap[0].object);
const boxedAddress = arrayHost.addressOf(0);
arrayHost.dec({ amount: 1, check: true }, [arrayAddress]);
assert.equal(arrayHost.readHeader(arrayAddress, false).kind, 255);
assert.equal(arrayHost.readHeader(boxedAddress, false).kind, 255);
assert.throws(() => new ConcreteHost([], {
  nextLocation: 1,
  heap: [{
    location: 0,
    rc: 1,
    persistent: false,
    live: true,
    object: { kind: "array", elements: [], capacity: -1 },
  }],
}), /capacity must cover its live elements/);

const setArray = concreteValidationExternalRegistry["Array.set!"];
const pushArray = concreteValidationExternalRegistry["Array.push"];
const popArray = concreteValidationExternalRegistry["Array.pop"];
const replicateArray = concreteValidationExternalRegistry["Array.replicate"];
const getArray = concreteValidationExternalRegistry["Array.get!Internal"];
const inhabitedUInt8 = concreteValidationExternalRegistry["instInhabitedUInt8"];
const erased = { kind: "erased" };
const taggedIndex = value => ({ kind: "tagged", payload: BigInt(value) });
const heapNatural = (target, value) =>
  target.decode("object", target.allocateNatural(value));

const uniqueArrayHost = new ConcreteHost([]);
const uniqueOld = heapNatural(uniqueArrayHost, 1n << 64n);
const uniqueRetained = heapNatural(uniqueArrayHost, (1n << 64n) + 1n);
const uniqueReplacement = heapNatural(uniqueArrayHost, (1n << 64n) + 2n);
const uniqueArray =
  uniqueArrayHost.allocateArray([uniqueOld, uniqueRetained], 4);
const uniqueResult = setArray({
  args: [erased, uniqueArray, taggedIndex(0), uniqueReplacement],
  host: uniqueArrayHost,
  world: 0,
}).value;
assert.deepStrictEqual(uniqueResult, uniqueArray);
assert.deepStrictEqual(
  uniqueArrayHost.arrayInfo(uniqueArray).elements,
  [uniqueReplacement, uniqueRetained],
);
assert.equal(
  uniqueArrayHost.readHeader(uniqueArrayHost.addressOf(uniqueOld.location), false).kind,
  255,
);
assert.deepStrictEqual(inhabitedUInt8({ args: [], world: 0 }).value,
  { kind: "scalar", scalarKind: "uint8", value: 0n });
assert.deepStrictEqual(getArray({
  args: [erased, taggedIndex(0), uniqueArray, taggedIndex(0)],
  host: uniqueArrayHost,
  world: 0,
}).value, uniqueReplacement);
assert.equal(
  uniqueArrayHost.readHeader(uniqueArrayHost.addressOf(uniqueReplacement.location)).rc,
  2,
);
uniqueArrayHost.releaseValue(uniqueReplacement);

const sharedArrayHost = new ConcreteHost([]);
const sharedOld = heapNatural(sharedArrayHost, (1n << 64n) + 3n);
const sharedRetained = heapNatural(sharedArrayHost, (1n << 64n) + 4n);
const sharedReplacement = heapNatural(sharedArrayHost, (1n << 64n) + 5n);
const sharedArray = sharedArrayHost.allocateArray([sharedOld, sharedRetained], 5);
sharedArrayHost.retainValue(sharedArray);
const sharedResult = setArray({
  args: [erased, sharedArray, taggedIndex(0), sharedReplacement],
  host: sharedArrayHost,
  world: 0,
}).value;
assert.notDeepStrictEqual(sharedResult, sharedArray);
assert.deepStrictEqual(
  sharedArrayHost.arrayInfo(sharedArray).elements, [sharedOld, sharedRetained]);
assert.deepStrictEqual(
  sharedArrayHost.arrayInfo(sharedResult).elements,
  [sharedReplacement, sharedRetained],
);
assert.equal(
  sharedArrayHost.readHeader(sharedArrayHost.addressOf(sharedRetained.location)).rc,
  2,
);
assert.equal(sharedArrayHost.arrayInfo(sharedArray).header.rc, 1);
assert.equal(sharedArrayHost.arrayInfo(sharedResult).capacity, 5);

const roomyArrayHost = new ConcreteHost([]);
const roomyChild = heapNatural(roomyArrayHost, (1n << 64n) + 7n);
const roomyValue = heapNatural(roomyArrayHost, (1n << 64n) + 8n);
const roomyArray = roomyArrayHost.allocateArray([roomyChild], 3);
assert.deepStrictEqual(pushArray({
  args: [erased, roomyArray, roomyValue],
  host: roomyArrayHost,
  world: 0,
}).value, roomyArray);
assert.deepStrictEqual(
  roomyArrayHost.arrayInfo(roomyArray).elements, [roomyChild, roomyValue]);
assert.equal(roomyArrayHost.arrayInfo(roomyArray).capacity, 3);
assert.deepStrictEqual(popArray({
  args: [erased, roomyArray],
  host: roomyArrayHost,
  world: 0,
}).value, roomyArray);
assert.deepStrictEqual(roomyArrayHost.arrayInfo(roomyArray).elements, [roomyChild]);
assert.equal(
  roomyArrayHost.readHeader(roomyArrayHost.addressOf(roomyValue.location), false).kind,
  255,
);

const fullArrayHost = new ConcreteHost([]);
const fullChild = heapNatural(fullArrayHost, (1n << 64n) + 9n);
const fullValue = heapNatural(fullArrayHost, (1n << 64n) + 10n);
const fullArray = fullArrayHost.allocateArray([fullChild], 1);
const grownArray = pushArray({
  args: [erased, fullArray, fullValue],
  host: fullArrayHost,
  world: 0,
}).value;
assert.notDeepStrictEqual(grownArray, fullArray);
assert.equal(
  fullArrayHost.readHeader(fullArrayHost.addressOf(fullArray.location), false).kind,
  255,
);
assert.deepStrictEqual(
  fullArrayHost.arrayInfo(grownArray).elements, [fullChild, fullValue]);
assert.equal(fullArrayHost.arrayInfo(grownArray).capacity, 4);
assert.equal(fullArrayHost.readHeader(fullArrayHost.addressOf(fullChild.location)).rc, 1);
assert.equal(fullArrayHost.readHeader(fullArrayHost.addressOf(fullValue.location)).rc, 1);

const replicateArrayHost = new ConcreteHost([]);
const repeatedArrayValue = heapNatural(replicateArrayHost, (1n << 64n) + 11n);
const replicatedArray = replicateArray({
  args: [erased, taggedIndex(3), repeatedArrayValue],
  host: replicateArrayHost,
  world: 0,
}).value;
assert.deepStrictEqual(
  replicateArrayHost.arrayInfo(replicatedArray).elements,
  [repeatedArrayValue, repeatedArrayValue, repeatedArrayValue],
);
assert.equal(replicateArrayHost.arrayInfo(replicatedArray).capacity, 3);
assert.equal(
  replicateArrayHost.readHeader(
    replicateArrayHost.addressOf(repeatedArrayValue.location)).rc,
  3,
);
replicateArrayHost.releaseValue(replicatedArray);
assert.equal(
  replicateArrayHost.readHeader(
    replicateArrayHost.addressOf(repeatedArrayValue.location), false).kind,
  255,
);

const emptyReplicateArrayHost = new ConcreteHost([]);
const unusedArrayValue = heapNatural(emptyReplicateArrayHost, (1n << 64n) + 12n);
const emptyReplicatedArray = replicateArray({
  args: [erased, taggedIndex(0), unusedArrayValue],
  host: emptyReplicateArrayHost,
  world: 0,
}).value;
assert.deepStrictEqual(emptyReplicateArrayHost.arrayInfo(emptyReplicatedArray), {
  address: emptyReplicateArrayHost.addressOf(emptyReplicatedArray.location),
  header: emptyReplicateArrayHost.readHeader(
    emptyReplicateArrayHost.addressOf(emptyReplicatedArray.location)),
  size: 0,
  capacity: 0,
  elements: [],
});
assert.equal(
  emptyReplicateArrayHost.readHeader(
    emptyReplicateArrayHost.addressOf(unusedArrayValue.location), false).kind,
  255,
);

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
// Model an allocation performed by a resident Wasm helper: its concrete
// header and slots are visible to the host, but no host-side allocation
// descriptor was recorded.
mutationHost.descriptors.delete(mutable >>> 0);
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

console.log("PASS concrete packed constructors, boxed values, and generic Array initial runtime");
