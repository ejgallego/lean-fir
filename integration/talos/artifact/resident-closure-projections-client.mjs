import { ConcreteHost } from "./concrete-host.mjs";

const ENTRIES = [
  ["fir_cproj_0_object", 0, "object"],
  ["fir_cproj_0_tagged", 0, "tagged"],
  ["fir_cproj_0_tobject", 0, "tobject"],
  ["fir_cproj_0_uint8", 0, "uint8"],
  ["fir_cproj_1_object", 1, "object"],
  ["fir_cproj_1_tobject", 1, "tobject"],
  ["fir_cproj_1_uint8", 1, "uint8"],
  ["fir_cproj_1_uint32", 1, "uint32"],
  ["fir_cproj_2_object", 2, "object"],
  ["fir_cproj_2_tobject", 2, "tobject"],
  ["fir_cproj_3_object", 3, "object"],
  ["fir_cproj_3_tobject", 3, "tobject"],
  ["fir_cproj_4_object", 4, "object"],
  ["fir_cproj_5_float32", 5, "float32"],
  ["fir_cproj_6_float", 6, "float"],
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

const BITS = new DataView(new ArrayBuffer(8));

function sameCapture(kind, actual, expected) {
  if (kind === "float32") {
    BITS.setFloat32(0, actual, true);
    const actualBits = BITS.getUint32(0, true);
    BITS.setFloat32(0, expected, true);
    return actualBits === BITS.getUint32(0, true);
  }
  if (kind === "float") {
    BITS.setFloat64(0, actual, true);
    const actualBits = BITS.getBigUint64(0, true);
    BITS.setFloat64(0, expected, true);
    return actualBits === BITS.getBigUint64(0, true);
  }
  return (actual >>> 0) === (expected >>> 0);
}

function rawCapture(kind, ordinal) {
  if (kind === "float32") return Math.fround(-13.25 - ordinal);
  if (kind === "float") return -0;
  return 0x100001 + ordinal * 17;
}

function writeRawCapture(view, address, kind, value) {
  if (kind === "float32") {
    view.setFloat32(address, value, true);
    view.setUint32(address + 4, 0, true);
  } else if (kind === "float") {
    view.setFloat64(address, value, true);
  } else {
    view.setUint32(address, value, true);
    view.setUint32(address + 4, 0, true);
  }
}

function writeHeader(view, address, {
  kind = 2,
  flags = 2,
  refCount = 1,
  allocationBytes = 80,
  aux0 = 0,
  aux1 = 6,
  aux2 = 5,
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
  ENTRIES.forEach(([entry, index, result], ordinal) => {
    const address = 1024 + ordinal * 512;
    const expected = rawCapture(result, ordinal);
    writeHeader(view, address);
    writeRawCapture(view, address + HEADER_BYTES + SLOT_BYTES * index,
      result, expected);
    expect(sameCapture(result, instance.exports[entry](address), expected),
      `${entry} returned the wrong raw capture`);
  });

  const dead = 8192;
  writeHeader(view, dead, { flags: 0 });
  const wrongKind = 8704;
  writeHeader(view, wrongKind, { kind: 1 });
  expectTrap(() => instance.exports.fir_cproj_0_tobject(0),
    "resident closure projection zero sentinel");
  expectTrap(() => instance.exports.fir_cproj_0_tobject(6),
    "resident closure projection misaligned word");
  expectTrap(() => instance.exports.fir_cproj_0_tobject(17),
    "resident closure projection immediate word");
  expectTrap(() => instance.exports.fir_cproj_0_tobject(dead),
    "resident closure projection dead object");
  expectTrap(() => instance.exports.fir_cproj_0_tobject(wrongKind),
    "resident closure projection non-closure object");
}

function partialOperation(index, result, ordinal) {
  const fields = Array(index + 1).fill("tobject");
  fields[index] = result;
  return {
    kind: "partialApply",
    function: `resident.closure.${ordinal}`,
    arity: index + 2,
    fixed: index + 1,
    fields,
    result: "tobject",
  };
}

function concreteValue(host, kind, ordinal, leaf) {
  switch (kind) {
    case "object": return leaf;
    case "tagged": return host.encodeTagged(BigInt(20 + ordinal));
    case "tobject": return host.encodeTagged(BigInt(20 + ordinal));
    case "uint8": return 0x80 + ordinal;
    case "uint32": return (0xf0000000 + ordinal) | 0;
    case "float32": return Math.fround(ordinal + 0.25);
    case "float": return -(ordinal + 0.5);
    default: throw new Error(`unsupported closure capture test kind: ${kind}`);
  }
}

async function concreteHostChecks(module, memoryExport) {
  const operations = ENTRIES.map(([, index, result], ordinal) =>
    partialOperation(index, result, ordinal));
  const host = new ConcreteHost(operations.map((operation) => ({ operation })));
  const instance = await WebAssembly.instantiate(module, {});
  host.attachMemory(instance.exports[memoryExport]);
  const leaf = host.allocCtor({
    fields: ["tobject"],
    size: 1,
    usize: 0,
    ssize: 0,
    tag: "3",
  }, [host.encodeTagged(0n)]);

  ENTRIES.forEach(([entry, index, result], ordinal) => {
    const operation = operations[ordinal];
    const args = operation.fields.map((kind, fieldIndex) =>
      fieldIndex === index
        ? concreteValue(host, result, ordinal, leaf)
        : concreteValue(host, kind, ordinal + fieldIndex, leaf));
    const closure = host.partialApply(operation, args);
    expect(sameCapture(result, instance.exports[entry](closure), args[index]),
      `${entry} disagreed with the concrete host closure layout`);
  });
}

export async function checkResidentClosureProjections(bytes, manifest) {
  expect(WebAssembly.validate(bytes),
    "resident closure projections failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  expect(WebAssembly.Module.imports(module).length === 0,
    "resident closure projections retained imports");
  expect(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "resident closure-projection descriptor retained imports");
  expect(manifest.memory === "memory",
    "resident closure-projection memory export drifted");
  expect(Array.isArray(manifest.entries) && manifest.entries.length === ENTRIES.length,
    "resident closure-projection entry count drifted");
  ENTRIES.forEach(([entry, index, result], ordinal) => {
    const actual = manifest.entries[ordinal];
    expect(actual?.entry === entry && actual?.index === index && actual?.result === result,
      `resident closure-projection descriptor ${ordinal} drifted`);
  });

  const exports = WebAssembly.Module.exports(module);
  for (const [entry] of ENTRIES) {
    expect(exports.some(({ name, kind }) => name === entry && kind === "function"),
      `resident closure-projection export ${entry} is missing`);
  }
  expect(exports.some(({ name, kind }) => name === manifest.memory && kind === "memory"),
    "resident closure-projection memory export is missing");

  const instance = await WebAssembly.instantiate(module, {});
  const memory = instance.exports[manifest.memory];
  expect(memory instanceof WebAssembly.Memory,
    "resident closure-projection memory export is not a memory");
  rawLayoutChecks(instance, memory);
  await concreteHostChecks(module, manifest.memory);
  return "PASS import-free Wasm-resident prettyM closure projections\n" +
    "PASS resident closure projections consume the concrete host heap";
}

export async function checkFetchedResidentClosureProjections(path) {
  const [wasmResponse, manifestResponse] = await Promise.all([
    fetch(path),
    fetch(`${path}.json`),
  ]);
  expect(wasmResponse.ok,
    `failed to fetch resident closure projections: ${wasmResponse.status}`);
  expect(manifestResponse.ok,
    `failed to fetch resident closure-projection descriptor: ${manifestResponse.status}`);
  return checkResidentClosureProjections(
    new Uint8Array(await wasmResponse.arrayBuffer()),
    await manifestResponse.json(),
  );
}
