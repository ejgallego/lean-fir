function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function exportedFunction(instance, name) {
  const value = instance.exports[name];
  expect(typeof value === "function", `${name} export is not callable`);
  return value;
}

function expectTrap(action, message) {
  try {
    action();
  } catch (error) {
    expect(error instanceof WebAssembly.RuntimeError,
      `${message}: expected WebAssembly.RuntimeError, got ${error}`);
    return;
  }
  throw new Error(`${message}: call unexpectedly returned`);
}

export async function checkResidentAllocator(bytes) {
  expect(WebAssembly.validate(bytes),
    "resident allocator module failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  expect(WebAssembly.Module.imports(module).length === 0,
    "resident allocator module retained an import");
  const { exports } = await WebAssembly.instantiate(module, {});
  const memory = exports.memory;
  expect(memory instanceof WebAssembly.Memory,
    "resident allocator memory export is missing");

  const frontier = exportedFunction({ exports }, "fir_heap_frontier");
  const setFrontier = exportedFunction({ exports }, "fir_heap_set_frontier");
  const allocate = exportedFunction({ exports }, "fir_heap_alloc");
  const store8 = exportedFunction({ exports }, "fir_heap_store8");
  const store16 = exportedFunction({ exports }, "fir_heap_store16");
  const store32 = exportedFunction({ exports }, "fir_heap_store32");
  const store64 = exportedFunction({ exports }, "fir_heap_store64");

  expect((frontier() >>> 0) === 1024,
    "resident allocator lost its heap-base initializer");
  const first = allocate(40) >>> 0;
  const second = allocate(40) >>> 0;
  expect(first === 1024 && second === 1064 && (frontier() >>> 0) === 1104,
    "resident allocator did not advance by aligned allocation sizes");

  store32(first, 0xdeadbeef);
  store64(first + 8, 0xfedcba9876543210n);
  store16(first + 16, 0xbeef);
  store8(first + 18, 0xab);
  let view = new DataView(memory.buffer);
  expect(view.getUint32(first, true) === 0xdeadbeef,
    "resident allocator raw 32-bit store drifted");
  expect(view.getBigUint64(first + 8, true) === 0xfedcba9876543210n,
    "resident allocator raw 64-bit store drifted");
  expect(view.getUint16(first + 16, true) === 0xbeef &&
      view.getUint8(first + 18) === 0xab,
  "resident allocator raw narrow stores drifted");

  for (const bytes of [0, 31, 33]) {
    expectTrap(() => allocate(bytes),
      `resident allocator accepted invalid allocation size ${bytes}`);
  }
  expectTrap(() => allocate(0xfffffff8),
    "resident allocator accepted an overflowing allocation");
  expect((frontier() >>> 0) === 1104,
    "failed allocation changed the resident frontier");

  expectTrap(() => setFrontier(1023),
    "resident frontier setter accepted an address below heap base");
  expectTrap(() => setFrontier(1103),
    "resident frontier setter accepted an unaligned address");
  expectTrap(() => setFrontier(1096),
    "resident frontier setter rewound the heap");
  expectTrap(() => setFrontier(65536 + 8),
    "resident frontier setter accepted unavailable memory");
  expect((frontier() >>> 0) === 1104,
    "failed frontier update changed the resident frontier");

  setFrontier(65528);
  const crossing = allocate(40) >>> 0;
  expect(crossing === 65528 && (frontier() >>> 0) === 65568,
    "resident allocator returned the wrong page-crossing address");
  expect(memory.buffer.byteLength === 2 * 65536,
    "resident allocator did not grow memory across the page boundary");
  view = new DataView(memory.buffer);
  store32(crossing + 32, 0x12345678);
  expect(view.getUint32(crossing + 32, true) === 0x12345678,
    "resident allocator store failed after memory growth");
  expectTrap(() => store8(memory.buffer.byteLength, 1),
    "resident raw store did not preserve Wasm bounds traps");

  return "PASS zero-import Wasm-resident allocator, frontier, growth, and raw stores";
}

export async function checkFetchedResidentAllocator(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentAllocator(await response.arrayBuffer());
}
