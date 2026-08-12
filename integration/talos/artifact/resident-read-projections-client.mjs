import { ConcreteHost } from "./concrete-host.mjs";

const EXPECTED_ENTRIES = [
  { entry: "fir_oproj_0_object", kind: "objectProj", index: 0, result: "object" },
  { entry: "fir_oproj_0_tobject", kind: "objectProj", index: 0, result: "tobject" },
  { entry: "fir_oproj_1_tobject", kind: "objectProj", index: 1, result: "tobject" },
  { entry: "fir_oproj_2_tobject", kind: "objectProj", index: 2, result: "tobject" },
  { entry: "fir_sproj_u8_0_0", kind: "scalarProj", width: 0, offset: 0, result: "uint8" },
  { entry: "fir_sproj_u8_1_0", kind: "scalarProj", width: 1, offset: 0, result: "uint8" },
  { entry: "fir_sproj_u8_1_1", kind: "scalarProj", width: 1, offset: 1, result: "uint8" },
  { entry: "fir_sproj_u8_2_0", kind: "scalarProj", width: 2, offset: 0, result: "uint8" },
  { entry: "fir_sproj_u64_1_0", kind: "scalarProj", width: 1, offset: 0, result: "uint64" },
];

const HEADER_BYTES = 32;
const SLOT_BYTES = 8;

function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function expectTrap(action, label) {
  try {
    action();
  } catch (error) {
    expect(error instanceof WebAssembly.RuntimeError,
      `${label} raised the wrong error type: ${error}`);
    return;
  }
  throw new Error(`${label} did not trap`);
}

function writeHeader(view, address, {
  kind = 1,
  flags = 2,
  refCount = 1,
  allocationBytes = 64,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
} = {}) {
  view.setUint32(address + 0, kind, true);
  view.setUint32(address + 4, flags, true);
  view.setUint32(address + 8, refCount, true);
  view.setUint32(address + 12, allocationBytes, true);
  view.setUint32(address + 16, aux0, true);
  view.setUint32(address + 20, aux1, true);
  view.setUint32(address + 24, aux2, true);
  view.setUint32(address + 28, aux3, true);
}

function rawLayoutChecks(instance, memory) {
  const view = new DataView(memory.buffer);

  const object0 = 1024;
  writeHeader(view, object0, { aux1: 1 });
  view.setUint32(object0 + HEADER_BYTES, 0x5000, true);
  expect((instance.exports.fir_oproj_0_object(object0) >>> 0) === 0x5000,
    "resident object projection 0/object returned the wrong word");

  const tobject0 = 2048;
  writeHeader(view, tobject0, { aux1: 1 });
  view.setUint32(tobject0 + HEADER_BYTES, 17, true);
  expect((instance.exports.fir_oproj_0_tobject(tobject0) >>> 0) === 17,
    "resident object projection 0/tobject returned the wrong word");

  const tobject1 = 3072;
  writeHeader(view, tobject1, { aux1: 2 });
  view.setUint32(tobject1 + HEADER_BYTES + SLOT_BYTES, 29, true);
  expect((instance.exports.fir_oproj_1_tobject(tobject1) >>> 0) === 29,
    "resident object projection 1/tobject returned the wrong word");

  const tobject2 = 4096;
  writeHeader(view, tobject2, { aux1: 3 });
  view.setUint32(tobject2 + HEADER_BYTES + 2 * SLOT_BYTES, 41, true);
  expect((instance.exports.fir_oproj_2_tobject(tobject2) >>> 0) === 41,
    "resident object projection 2/tobject returned the wrong word");

  const scalar0 = 5120;
  writeHeader(view, scalar0, { aux3: 1 });
  view.setUint8(scalar0 + HEADER_BYTES, 0xa1);
  expect((instance.exports.fir_sproj_u8_0_0(scalar0) >>> 0) === 0xa1,
    "resident scalar projection 0/0 returned the wrong byte");

  const scalar1 = 6144;
  writeHeader(view, scalar1, { aux1: 1, aux3: 2 });
  view.setUint8(scalar1 + HEADER_BYTES + SLOT_BYTES, 0xb2);
  view.setUint8(scalar1 + HEADER_BYTES + SLOT_BYTES + 1, 0xc3);
  expect((instance.exports.fir_sproj_u8_1_0(scalar1) >>> 0) === 0xb2,
    "resident scalar projection 1/0 returned the wrong byte");
  expect((instance.exports.fir_sproj_u8_1_1(scalar1) >>> 0) === 0xc3,
    "resident scalar projection 1/1 returned the wrong byte");

  const scalar2 = 7168;
  writeHeader(view, scalar2, { aux1: 2, aux3: 1 });
  view.setUint8(scalar2 + HEADER_BYTES + 2 * SLOT_BYTES, 0xd4);
  expect((instance.exports.fir_sproj_u8_2_0(scalar2) >>> 0) === 0xd4,
    "resident scalar projection 2/0 returned the wrong byte");

  const scalar64 = 7680;
  const scalar64Value = 0xfedcba9876543210n;
  writeHeader(view, scalar64, { aux1: 1, aux3: 8 });
  view.setBigUint64(scalar64 + HEADER_BYTES + SLOT_BYTES, scalar64Value, true);
  expect(BigInt.asUintN(64, instance.exports.fir_sproj_u64_1_0(scalar64)) ===
      scalar64Value,
    "resident scalar projection 1/0 returned the wrong UInt64");

  const dead = 8192;
  writeHeader(view, dead, { flags: 0, aux1: 1 });
  const wrongKind = 9216;
  writeHeader(view, wrongKind, { kind: 4, aux1: 1 });
  expectTrap(() => instance.exports.fir_oproj_0_tobject(0),
    "resident projection zero sentinel");
  expectTrap(() => instance.exports.fir_oproj_0_tobject(6),
    "resident projection misaligned word");
  expectTrap(() => instance.exports.fir_oproj_0_tobject(17),
    "resident projection immediate word");
  expectTrap(() => instance.exports.fir_oproj_0_tobject(dead),
    "resident projection dead object");
  expectTrap(() => instance.exports.fir_oproj_0_tobject(wrongKind),
    "resident projection non-constructor object");
}

function concreteHostChecks(module, memoryExport) {
  const host = new ConcreteHost();
  return WebAssembly.instantiate(module, {}).then((instance) => {
    host.attachMemory(instance.exports[memoryExport]);

    const leaf = host.allocCtor({
      fields: ["tobject"],
      size: 1,
      usize: 0,
      ssize: 0,
      tag: "3",
    }, [host.encodeTagged(0n)]);
    const fields = [leaf, host.encodeTagged(7n), host.encodeTagged(11n)];
    const container = host.allocCtor({
      fields: ["object", "tobject", "tobject"],
      size: 3,
      usize: 0,
      ssize: 0,
      tag: "4",
    }, fields);
    expect((instance.exports.fir_oproj_0_object(container) >>> 0) === (leaf >>> 0),
      "resident object projection disagreed with the concrete host");
    expect((instance.exports.fir_oproj_1_tobject(container) >>> 0) ===
        (fields[1] >>> 0),
      "resident object projection 1 disagreed with the concrete host");
    expect((instance.exports.fir_oproj_2_tobject(container) >>> 0) ===
        (fields[2] >>> 0),
      "resident object projection 2 disagreed with the concrete host");

    const scalarCases = [
      [0, 0, 0x61, "fir_sproj_u8_0_0"],
      [1, 0, 0x72, "fir_sproj_u8_1_0"],
      [1, 1, 0x83, "fir_sproj_u8_1_1"],
      [2, 0, 0x94, "fir_sproj_u8_2_0"],
    ];
    for (const [width, offset, value, entry] of scalarCases) {
      const scalar = host.allocCtor({
        fields: Array(width).fill("tobject"),
        size: width,
        usize: 0,
        ssize: offset + 1,
        tag: "5",
      }, Array(width).fill(host.encodeTagged(0n)));
      host.scalarSet({
        kind: "scalarSet",
        width,
        offset,
        field: "uint8",
      }, [scalar, value]);
      expect((instance.exports[entry](scalar) >>> 0) === value,
        `${entry} disagreed with the concrete host`);
    }

    const uint64Value = BigInt.asIntN(64, 0x8123456789abcdefn);
    const scalar64 = host.allocCtor({
      fields: ["tobject"],
      size: 1,
      usize: 0,
      ssize: 8,
      tag: "6",
    }, [host.encodeTagged(0n)]);
    host.scalarSet({
      kind: "scalarSet",
      width: 1,
      offset: 0,
      field: "uint64",
    }, [scalar64, uint64Value]);
    expect(BigInt.asUintN(64,
      instance.exports.fir_sproj_u64_1_0(scalar64)) ===
        BigInt.asUintN(64, uint64Value),
    "fir_sproj_u64_1_0 disagreed with the concrete host");
  });
}

export async function checkResidentReadProjections(bytes, manifest) {
  expect(WebAssembly.validate(bytes),
    "resident read projections failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  const imports = WebAssembly.Module.imports(module);
  expect(imports.length === 0,
    `resident read projections retained ${imports.length} import(s)`);
  expect(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "resident read-projection descriptor retained imports");
  expect(manifest.memory === "memory",
    "resident read-projection memory export drifted");
  expect(Array.isArray(manifest.entries) &&
      manifest.entries.length === EXPECTED_ENTRIES.length &&
      manifest.entries.every((actual, index) =>
        Object.entries(EXPECTED_ENTRIES[index]).every(
          ([key, value]) => actual[key] === value,
        )),
    "resident read-projection entry inventory drifted");

  const exports = WebAssembly.Module.exports(module);
  for (const { entry } of EXPECTED_ENTRIES) {
    expect(exports.some(({ name, kind }) => name === entry && kind === "function"),
      `resident read-projection export ${entry} is missing`);
  }
  expect(exports.some(({ name, kind }) => name === manifest.memory && kind === "memory"),
    "resident read-projection memory export is missing");

  const instance = await WebAssembly.instantiate(module, {});
  const memory = instance.exports[manifest.memory];
  expect(memory instanceof WebAssembly.Memory,
    "resident read-projection memory export is not a memory");
  rawLayoutChecks(instance, memory);
  await concreteHostChecks(module, manifest.memory);
  return "PASS import-free Wasm-resident prettyM read projections\n" +
    "PASS resident read projections consume the concrete host heap";
}

export async function checkFetchedResidentReadProjections(path) {
  const [wasmResponse, manifestResponse] = await Promise.all([
    fetch(path),
    fetch(`${path}.json`),
  ]);
  expect(wasmResponse.ok,
    `failed to fetch resident read projections: ${wasmResponse.status}`);
  expect(manifestResponse.ok,
    `failed to fetch resident read-projection descriptor: ${manifestResponse.status}`);
  return checkResidentReadProjections(
    new Uint8Array(await wasmResponse.arrayBuffer()),
    await manifestResponse.json(),
  );
}
