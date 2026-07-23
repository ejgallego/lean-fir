import assert from "node:assert/strict";

import { ConcreteHost } from "./concrete-host.mjs";

const scalarFields = [
  { width: 2, offset: 0, value: { kind: "uint8", value: "171" } },
  { width: 2, offset: 1, value: { kind: "uint16", value: "52719" } },
  { width: 2, offset: 3, value: { kind: "uint32", value: "2309737967" } },
  { width: 2, offset: 7, value: { kind: "uint64", value: "18446744073709551615" } },
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
assert.equal(header.aux3, 15);
assert.equal(header.bytes, 64);
assert.equal(header.rc, 3);
assert.deepStrictEqual(host.objectJson(address, header), runtime.heap[0].object);

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

assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 1, offset: 0, value: { kind: "uint8", value: "0" } },
])), /scalar width must equal its fixed-slot prefix/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0, value: { kind: "uint8", value: "256" } },
])), /uint8 value is out of range/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0, value: { kind: "uint16", value: "258" } },
  { width: 2, offset: 1, value: { kind: "uint8", value: "2" } },
])), /overlapping initial constructor scalar fields disagree/);
assert.throws(() => new ConcreteHost([], initialRuntime([
  { width: 2, offset: 0xffffffff, value: { kind: "uint8", value: "0" } },
])), /packed scalar extent must fit UInt32/);

console.log("PASS concrete packed initial-runtime constructors");
