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

function allocationCases(retained) {
  const floatBits = [
    [0, 0n],
    [0x80000000, 0x8000000000000000n],
    [1, 1n],
    [0x7f800000, 0x7ff0000000000000n],
    [0xff800000, 0xfff0000000000000n],
    [0x7fc12345, 0x7ff8123456789abcn],
    [0x7f812345, 0x7ff0123456789abcn],
    [0xff812345, 0xfff0123456789abcn],
  ];
  return [
    ["resident_closure_empty", [], [2, 2, 1, 32, 1, 3, 0, 1]],
    ["resident_closure_tagged", [], [2, 2, 1, 32, 1, 3, 0, 1]],
    ["resident_closure_shared_shape", [], [2, 2, 1, 32, 0, 5, 0, 1]],
    ["resident_closure_captured", [43, 255, 0x0123456789abcdefn],
      [2, 2, 1, 56, 1, 4, 3, 2]],
    ...["resident_closure_mixed_bits", "resident_closure_mixed_tobject_bits",
      "resident_closure_mixed_tagged_bits"].flatMap((entry) =>
      floatBits.map(([f32, f64]) => [
      entry,
      [retained, 43, 9, 0, 255, 65535, 0xfedcba98,
        0xfedcba9876543210n, 0x0123456789abcdefn, f32, f64],
      [2, 2, 1, 120, 1, 12, 11, 4],
    ])),
  ];
}

function expectedAllocation(args, words) {
  const expected = new Uint8Array(words[3]);
  const view = new DataView(expected.buffer);
  words.forEach((word, index) => view.setUint32(4 * index, word, true));
  args.forEach((value, index) => {
    const offset = 32 + 8 * index;
    if (typeof value === "bigint") view.setBigUint64(offset, value, true);
    else view.setUint32(offset, value, true);
  });
  return expected;
}

function expectBytes(memory, address, expected, message) {
  expect(expected.every((byte, index) => memory[address + index] === byte),
    message);
}

function checkPoisonedReallocation(exports) {
  // Keep a real object below the rewind checkpoint for the mixed object capture.
  const retained = exports.resident_closure_empty();
  const checkpoint = exports.fir_heap_frontier();
  const snapshots = [];
  for (const [entry, args, words] of allocationCases(retained)) {
    const extent = words[3];
    const memory = new Uint8Array(exports.memory.buffer);
    // Only bucket zero gets a sentinel: other reserved words are live recycler
    // heads and must remain empty. None of these extents hashes to bucket zero.
    new DataView(memory.buffer).setUint32(0, 0xdecafbad, true);
    const before = memory.slice(0, checkpoint);
    memory.fill(0xa5, checkpoint, checkpoint + extent + 16);
    const expected = expectedAllocation(args, words);
    equal(exports[entry](...args), checkpoint, `${entry}: reused address`);
    equal(exports.fir_heap_frontier(), checkpoint + extent,
      `${entry}: allocation extent`);
    expect(expected.every((byte, index) => memory[checkpoint + index] === byte),
      `${entry}: exact header/capture/padding bytes differ after poisoned reuse`);
    expect(before.every((byte, index) => memory[index] === byte),
      `${entry}: reserved memory or retained object changed`);
    expect(memory.subarray(checkpoint + extent, checkpoint + extent + 16)
      .every((byte) => byte === 0xa5), `${entry}: wrote beyond its allocation`);
    snapshots.push(Array.from(memory.slice(checkpoint, checkpoint + extent)));
    // All output bytes have been inspected/copied; no new graph is retained.
    exports.fir_heap_rewind(checkpoint);
    equal(exports.fir_heap_frontier(), checkpoint, `${entry}: rewind frontier`);
  }
  return snapshots;
}

function checkReleasedReallocation(exports) {
  equal(typeof exports.resident_dec_checked, "function",
    "fixture is missing the real resident release entry");
  equal(exports.fir_heap_recycle, undefined,
    "fixture exposed the private recycler instead of using resident release");
  const retained = exports.resident_closure_empty();
  // A persistent input makes repeated owning mixed closures valid without
  // manufacturing dead headers or changing the retained object's reference count.
  new DataView(exports.memory.buffer).setUint32(retained + 4, 3, true);
  const checkpoint = exports.fir_heap_frontier();
  const snapshots = [];
  for (const [entry, args, words] of allocationCases(retained)) {
    const extent = words[3];
    const expected = expectedAllocation(args, words);
    const memory = new Uint8Array(exports.memory.buffer);
    const prefix = memory.slice(0, checkpoint);
    const first = exports[entry](...args);
    equal(first, checkpoint, `${entry}: initial arena address`);
    if (extent === 32) {
      // Header-only blocks are deliberately ineligible in the accepted recycler.
      exports.resident_dec_checked(first);
      expect(header(exports.memory, first).every((word, i) =>
        word === [255, 0, 0, extent, 0, 0, 0, 0][i]),
      `${entry}: header-only retirement is not canonical`);
      memory.fill(0xa5, checkpoint + extent, checkpoint + 2 * extent + 16);
      const next = exports[entry](...args);
      equal(next, checkpoint + extent, `${entry}: recycled a header-only block`);
      equal(exports.fir_heap_frontier(), checkpoint + 2 * extent,
        `${entry}: header-only fallback frontier`);
      expectBytes(memory, next, expected, `${entry}: header-only initialized bytes`);
      snapshots.push(Array.from(memory.slice(next, next + extent)));
      exports.resident_dec_checked(next);
    } else {
      const second = exports[entry](...args);
      equal(second, first + extent, `${entry}: second arena address`);
      const frontier = exports.fir_heap_frontier();
      exports.resident_dec_checked(first);
      exports.resident_dec_checked(second);
      const bucket = (((extent / 8) - 1) & 255) * 4;
      equal(u32(exports.memory, bucket), second, `${entry}: release missed reuse list`);
      equal(u32(exports.memory, second + 32), first, `${entry}: nonempty reuse link`);
      for (const address of [first, second]) {
        expect(header(exports.memory, address).every((word, i) =>
          word === [255, 0, 0, extent, 0, 0, 0, 0][i]),
        `${entry}: release did not leave a canonical dead header`);
        // Only dead payload is poisoned; preserve both the canonical header
        // and the real first-word free-list link. No index/header fabrication.
        memory.fill(0xa5, address + 36, address + extent);
      }
      memory.fill(0xa5, frontier, frontier + 16);
      for (const address of [second, first]) {
        equal(exports[entry](...args), address, `${entry}: exact recycled address`);
        equal(exports.fir_heap_frontier(), frontier,
          `${entry}: recycled allocation grew frontier`);
        expectBytes(memory, address, expected,
          `${entry}: recycled header/capture/padding bytes`);
        snapshots.push(Array.from(memory.slice(address, address + extent)));
      }
      equal(u32(exports.memory, bucket), 0, `${entry}: reuse list was not consumed`);
      exports.resident_dec_checked(second);
      exports.resident_dec_checked(first);
    }
    expect(memory.subarray(checkpoint + 2 * extent, checkpoint + 2 * extent + 16)
      .every((byte) => byte === 0xa5), `${entry}: recycled allocation crossed canary`);
    // Every output was copied, every scratch closure released, and only the
    // persistent input lies below the checkpoint. Rewind clears the reuse index.
    exports.fir_heap_rewind(checkpoint);
    equal(exports.fir_heap_frontier(), checkpoint, `${entry}: final checkpoint`);
    expectBytes(memory, 0, prefix, `${entry}: retained prefix changed after reuse`);
  }
  return snapshots;
}

/**
 * Exercise the generation-only resident `partialApply` family without host
 * imports. The raw checks freeze W6's closure header and semantic slot layout;
 * ConcreteHost then independently decodes the same Wasm-resident allocations.
 */
export async function checkResidentClosureAllocation(bytes, referenceBytes) {
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
  equal(typeof exports.resident_closure_shared_shape, "function",
    "resident shared-shape closure export is missing");
  equal(typeof exports.resident_closure_mixed_bits, "function",
    "resident bit-exact mixed-capture export is missing");
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
    "empty closure changed the reserved word");

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
    "captured closure changed the reserved word");

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

  const sharedShape = exports.resident_closure_shared_shape();
  equal(sharedShape, 1176,
    "shared-shape closure returned the wrong address");
  equal(exports.fir_heap_frontier(), 1208,
    "shared-shape closure advanced the wrong extent");
  expect(header(exports.memory, sharedShape).every((value, index) =>
    value === [2, 2, 1, 32, 0, 5, 0, 1][index]),
  `shared-shape closure metadata drifted: ${header(exports.memory, sharedShape)}`);
  equal(u32(exports.memory, 0), 0xdecafbad,
    "shared-shape closure changed the reserved word");

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
  const concreteSharedShape = concrete.resident_closure_shared_shape();
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
  const sharedShapeMetadata = host.closureMetadata(concreteSharedShape);
  equal(sharedShapeMetadata.functionName,
    "ResidentClosureAllocation.unrelated",
    "shared helper failed to preserve its call-site target ID");
  expect(Array.isArray(sharedShapeMetadata.fields) &&
    sharedShapeMetadata.fields.length === 0,
  `shared closure descriptor drifted: ${sharedShapeMetadata.fields}`);
  equal(sharedShapeMetadata.header.aux1, 5,
    "shared helper failed to preserve its call-site arity");
  equal(sharedShapeMetadata.header.aux2, 0,
    "shared closure fixed count drifted");
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

  const poisoned = await WebAssembly.instantiate(module, {});
  const checkpointSnapshots = checkPoisonedReallocation(poisoned.exports);
  const recycled = await WebAssembly.instantiate(module, {});
  const recycledSnapshots = checkReleasedReallocation(recycled.exports);

  if (referenceBytes !== undefined) {
    const reference = await WebAssembly.compile(referenceBytes);
    equal(WebAssembly.Module.imports(reference).length, 0, "reference retained an import");
    const baselineCheckpoint = await WebAssembly.instantiate(reference, {});
    const baselineRecycled = await WebAssembly.instantiate(reference, {});
    equal(JSON.stringify(checkpointSnapshots),
      JSON.stringify(checkPoisonedReallocation(baselineCheckpoint.exports)),
      "full initialized extents differ from the accepted full-zero checkpoint path");
    equal(JSON.stringify(recycledSnapshots),
      JSON.stringify(checkReleasedReallocation(baselineRecycled.exports)),
      "full initialized extents differ from the accepted full-zero recycler path");
  }

  return "PASS zero-import closure allocation, poisoned checkpoint and released-block reuse";
}

export async function checkFetchedResidentClosureAllocation(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentClosureAllocation(await response.arrayBuffer());
}
