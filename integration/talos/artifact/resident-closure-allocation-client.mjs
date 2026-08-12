import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

function u32(memory, address) {
  return new DataView(memory.buffer).getUint32(address, true);
}

function u64(memory, address) {
  return new DataView(memory.buffer).getBigUint64(address, true);
}

function header(memory, address) {
  return Array.from({ length: 8 }, (_unused, index) =>
    u32(memory, address + 4 * index));
}

/**
 * Exercise the generation-only resident `partialApply` family without host
 * imports. The raw checks freeze W6's closure header and semantic slot layout;
 * ConcreteHost then independently decodes the same Wasm-resident allocations.
 */
export async function checkResidentClosureAllocation(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident closure-allocation module retained an import");

  const { exports } = await WebAssembly.instantiate(module, {});
  expect(exports.memory instanceof WebAssembly.Memory,
    "resident closure-allocation memory export is missing");
  equal(typeof exports.resident_closure_empty, "function",
    "resident empty-closure export is missing");
  equal(typeof exports.resident_closure_captured, "function",
    "resident captured-closure export is missing");
  equal(typeof exports.resident_closure_inside_loop, "function",
    "resident loop-closure export is missing");
  equal(typeof exports.resident_closure_tagged, "function",
    "resident tagged-closure export is missing");
  equal(typeof exports.fir_heap_frontier, "function",
    "resident closure-allocation frontier export is missing");

  const view = new DataView(exports.memory.buffer);
  view.setUint32(0, 0xdecafbad, true);

  const empty = exports.resident_closure_empty();
  equal(empty, 1024, "empty closure returned the wrong address");
  equal(exports.fir_heap_frontier(), 1056,
    "empty closure advanced the wrong extent");
  expect(header(exports.memory, empty).every((value, index) =>
    value === [2, 2, 1, 32, 1, 3, 0, 1][index]),
  `empty closure header drifted: ${header(exports.memory, empty)}`);
  equal(u32(exports.memory, 0), 0xdecafbad,
    "empty closure failed to restore the scratch word");

  const captured = exports.resident_closure_captured(
    43,
    255,
    0x0123456789abcdefn,
  );
  equal(captured, 1056, "captured closure returned the wrong address");
  equal(exports.fir_heap_frontier(), 1112,
    "captured closure advanced the wrong extent");
  expect(header(exports.memory, captured).every((value, index) =>
    value === [2, 2, 1, 56, 1, 4, 3, 2][index]),
  `captured closure header drifted: ${header(exports.memory, captured)}`);
  equal(u32(exports.memory, captured + 32), 43,
    "captured object slot drifted");
  equal(u32(exports.memory, captured + 36), 0,
    "captured object high padding is nonzero");
  equal(u32(exports.memory, captured + 40), 255,
    "captured UInt8 slot drifted");
  equal(u32(exports.memory, captured + 44), 0,
    "captured UInt8 high padding is nonzero");
  equal(u64(exports.memory, captured + 48), 0x0123456789abcdefn,
    "captured usize slot drifted");
  equal(u32(exports.memory, 0), 0xdecafbad,
    "captured closure failed to restore the scratch word");

  const insideLoop = exports.resident_closure_inside_loop();
  equal(insideLoop, 1112, "loop-nested closure returned the wrong address");
  equal(exports.fir_heap_frontier(), 1144,
    "loop-nested closure advanced the wrong extent");
  expect(header(exports.memory, insideLoop).every((value, index) =>
    value === [2, 2, 1, 32, 1, 3, 0, 1][index]),
  `loop-nested closure header drifted: ${header(exports.memory, insideLoop)}`);

  const tagged = exports.resident_closure_tagged();
  equal(tagged, 1144,
    "tagged object-family closure returned the wrong address");
  equal(exports.fir_heap_frontier(), 1176,
    "tagged object-family closure advanced the wrong extent");
  expect(header(exports.memory, tagged).every((value, index) =>
    value === [2, 2, 1, 32, 1, 3, 0, 1][index]),
  `tagged object-family closure header drifted: ${header(exports.memory, tagged)}`);
  equal(u32(exports.memory, 0), 0xdecafbad,
    "tagged closure failed to restore the scratch word");

  const { exports: concrete } = await WebAssembly.instantiate(module, {});
  const host = new ConcreteHost(
    [],
    undefined,
    undefined,
    [
      "ResidentClosureAllocation.unrelated",
      "ResidentClosureAllocation.target",
    ],
    [["uint32"], [], ["tobject", "uint8", "usize"]],
  );
  host.attachMemory(concrete.memory);
  host.attachResidentFrontier(
    concrete.fir_heap_frontier,
    concrete.fir_heap_set_frontier,
  );
  const concreteEmpty = concrete.resident_closure_empty();
  const concreteCaptured = concrete.resident_closure_captured(
    43,
    255,
    0x0123456789abcdefn,
  );
  const emptyMetadata = host.closureMetadata(concreteEmpty);
  equal(emptyMetadata.functionName, "ResidentClosureAllocation.target",
    "empty closure target ID drifted");
  expect(Array.isArray(emptyMetadata.fields) &&
    emptyMetadata.fields.length === 0,
  `empty closure descriptor drifted: ${emptyMetadata.fields}`);
  equal(emptyMetadata.header.aux1, 3, "empty closure arity drifted");
  equal(emptyMetadata.header.aux2, 0, "empty closure fixed count drifted");

  const capturedMetadata = host.closureMetadata(concreteCaptured);
  equal(capturedMetadata.functionName, "ResidentClosureAllocation.target",
    "captured closure target ID drifted");
  expect(JSON.stringify(capturedMetadata.fields) ===
    JSON.stringify(["tobject", "uint8", "usize"]),
  `captured closure descriptor drifted: ${capturedMetadata.fields}`);
  equal(capturedMetadata.header.aux1, 4, "captured closure arity drifted");
  equal(capturedMetadata.header.aux2, 3,
    "captured closure fixed count drifted");
  const projection = (index, result) => ({
    kind: "closureProj",
    function: "ResidentClosureAllocation.target",
    arity: 4,
    fixed: 3,
    index,
    result,
  });
  equal(host.closureProj(
    projection(0, "tobject"),
    [concreteCaptured],
  ), 43, "ConcreteHost object capture projection drifted");
  equal(host.closureProj(
    projection(1, "uint8"),
    [concreteCaptured],
  ), 255, "ConcreteHost UInt8 capture projection drifted");
  equal(host.closureProj(
    projection(2, "usize"),
    [concreteCaptured],
  ), 0x0123456789abcdefn,
  "ConcreteHost usize capture projection drifted");

  return "PASS zero-import resident closure allocation";
}

export async function checkFetchedResidentClosureAllocation(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentClosureAllocation(await response.arrayBuffer());
}
