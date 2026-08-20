const expectedExports = [
  ["FirArrayProbe.readRepeated", "function"],
  ["FirArrayProbe.buildOnly", "function"],
  ["FirArrayProbe.updateUnique", "function"],
  ["FirArrayProbe.updateShared", "function"],
  ["fir_heap_frontier", "function"],
  ["fir_heap_set_frontier", "function"],
  ["fir_heap_rewind", "function"],
  ["fir_heap_alloc", "function"],
  ["memory", "memory"],
];

const KIND_OPAQUE = 8;
const LIVE_PERSISTENT = 3;
const ARRAY_MARKER = 0x41525259;
const HEADER_BYTES = 32;
const ELEMENT_BYTES = 8;
const MAX_IMMEDIATE = 0x7fffffff;

function requireCondition(condition, message) {
  if (!condition) throw new Error(message);
}

function natural(value, label) {
  requireCondition(Number.isSafeInteger(value) && value >= 0 &&
    value <= MAX_IMMEDIATE, `${label} must be an immediate Lean Nat`);
  return (2 * value + 1) >>> 0;
}

function uint32(value, label) {
  requireCondition(Number.isSafeInteger(value) && value >= 0 &&
    value <= 0xffffffff, `${label} must be a UInt32`);
  return value >>> 0;
}

function boxedImmediateUInt32(value, label) {
  const checked = uint32(value, label);
  requireCondition(checked <= MAX_IMMEDIATE,
    `${label} exceeds the probe's allocation-free boxed UInt32 boundary`);
  return (2 * checked + 1) >>> 0;
}

function checkedIndex(index, size) {
  natural(index, "index");
  requireCondition(index < size, `index ${index} is outside size ${size}`);
  return index;
}

function pageCount(memory) {
  return memory.buffer.byteLength / 65536;
}

function expectedShared(rounds) {
  return Number((1n + 7n * BigInt(rounds)) & 0xffffffffn);
}

export async function createArrayProbe({ bytes, module, values,
    now = () => globalThis.performance?.now?.() ?? Date.now() }) {
  requireCondition((bytes === undefined) !== (module === undefined),
    "provide exactly one of bytes or module");
  requireCondition(Array.isArray(values) && values.length > 0,
    "values must be a nonempty JavaScript Array");
  const compiled = module ?? await WebAssembly.compile(bytes);
  requireCondition(WebAssembly.Module.imports(compiled).length === 0,
    "Array probe must have zero imports");
  const actualExports = WebAssembly.Module.exports(compiled)
    .map(({ name, kind }) => [name, kind]);
  requireCondition(JSON.stringify(actualExports) === JSON.stringify(expectedExports),
    `Array probe exports changed: ${JSON.stringify(actualExports)}`);
  const { exports } = await WebAssembly.instantiate(compiled, {});
  requireCondition(exports.memory instanceof WebAssembly.Memory,
    "Array probe does not own exported memory");

  const allocationBytes = HEADER_BYTES + ELEMENT_BYTES * values.length;
  const arrayAddress = exports.fir_heap_alloc(allocationBytes) >>> 0;
  requireCondition(arrayAddress >= 1024 && arrayAddress % 8 === 0,
    `resident allocator returned invalid Array address ${arrayAddress}`);
  const view = new DataView(exports.memory.buffer);
  for (const [offset, value] of [
    [0, KIND_OPAQUE],
    [4, LIVE_PERSISTENT],
    [8, 0],
    [12, allocationBytes],
    [16, ARRAY_MARKER],
    [20, values.length],
    [24, values.length],
    [28, 0],
  ]) view.setUint32(arrayAddress + offset, value, true);
  values.forEach((value, index) => {
    view.setUint32(arrayAddress + HEADER_BYTES + ELEMENT_BYTES * index,
      boxedImmediateUInt32(value, `values[${index}]`), true);
    view.setUint32(arrayAddress + HEADER_BYTES + ELEMENT_BYTES * index + 4,
      0, true);
  });
  const checkpoint = exports.fir_heap_frontier() >>> 0;
  let alive = true;

  function execute(name, args, expected) {
    requireCondition(alive, "Array probe is disposed");
    const frontierBefore = exports.fir_heap_frontier() >>> 0;
    requireCondition(frontierBefore === checkpoint,
      `scratch frontier ${frontierBefore} differs from checkpoint ${checkpoint}`);
    const pagesBefore = pageCount(exports.memory);
    const started = now();
    let value;
    let peakFrontier;
    let pagesAfterExecute;
    let executeFinished;
    let finished;
    let failure;
    try {
      value = exports[name](...args) >>> 0;
      executeFinished = now();
      peakFrontier = exports.fir_heap_frontier() >>> 0;
      pagesAfterExecute = pageCount(exports.memory);
      requireCondition(value === expected,
        `${name} returned ${value}, expected ${expected}`);
    } catch (error) {
      executeFinished = now();
      peakFrontier = exports.fir_heap_frontier() >>> 0;
      pagesAfterExecute = pageCount(exports.memory);
      failure = error;
    } finally {
      exports.fir_heap_rewind(checkpoint);
      finished = now();
    }
    const postRewindFrontier = exports.fir_heap_frontier() >>> 0;
    if (postRewindFrontier !== checkpoint) {
      alive = false;
      throw new Error(`${name} failed to rewind to ${checkpoint}`);
    }
    if (failure !== undefined) throw failure;
    return {
      value,
      timings: {
        executeMs: executeFinished - started,
        rewindMs: finished - executeFinished,
        totalMs: finished - started,
      },
      memory: {
        frontierBefore,
        peakFrontier,
        postRewindFrontier,
        allocatedBytes: peakFrontier - frontierBefore,
        pagesBefore,
        pagesAfterExecute,
        pagesAfterRewind: pageCount(exports.memory),
      },
    };
  }

  return Object.freeze({
    get checkpoint() { return checkpoint; },
    get inputBytes() { return allocationBytes; },
    readRepeated(index, rounds) {
      checkedIndex(index, values.length);
      natural(rounds, "rounds");
      const expected = Number((BigInt(values[index]) * BigInt(rounds)) &
        0xffffffffn);
      return execute("FirArrayProbe.readRepeated",
        [arrayAddress, natural(index, "index"), natural(rounds, "rounds")],
        expected);
    },
    buildOnly(size, index) {
      requireCondition(size > 0, "size must be positive");
      checkedIndex(index, size);
      return execute("FirArrayProbe.buildOnly",
        [natural(size, "size"), natural(index, "index")], 1);
    },
    updateUnique(size, index, rounds) {
      requireCondition(size > 0, "size must be positive");
      checkedIndex(index, size);
      natural(rounds, "rounds");
      return execute("FirArrayProbe.updateUnique", [natural(size, "size"),
        natural(index, "index"), natural(rounds, "rounds")],
      rounds === 0 ? 1 : 7);
    },
    updateShared(size, index, rounds) {
      requireCondition(size > 0, "size must be positive");
      checkedIndex(index, size);
      natural(rounds, "rounds");
      return execute("FirArrayProbe.updateShared", [natural(size, "size"),
        natural(index, "index"), natural(rounds, "rounds")],
      expectedShared(rounds));
    },
    dispose() {
      alive = false;
    },
  });
}
