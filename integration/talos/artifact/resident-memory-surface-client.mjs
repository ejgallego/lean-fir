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

export async function checkResidentMemorySurface(bytes) {
  expect(WebAssembly.validate(bytes),
    "resident memory-surface module failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  expect(WebAssembly.Module.imports(module).length === 0,
    "resident memory-surface module retained an import");
  const instance = await WebAssembly.instantiate(module, {});
  const memory = instance.exports.memory;
  expect(memory instanceof WebAssembly.Memory,
    "resident memory-surface memory export is missing");
  const arithmetic = exportedFunction(instance, "residentArithmetic");
  const store8 = exportedFunction(instance, "residentStore8");
  const store16 = exportedFunction(instance, "residentStore16");
  const store32 = exportedFunction(instance, "residentStore32");
  const store64 = exportedFunction(instance, "residentStore64");
  const size = exportedFunction(instance, "residentMemorySize");
  const grow = exportedFunction(instance, "residentMemoryGrow");

  expect((arithmetic() >>> 0) === 1,
    "resident i32 add/sub/lt_u sequence drifted");
  expect((size() >>> 0) === 1,
    "resident memory did not start at one page");
  expect((store8(1024, 0x1ff) >>> 0) === 0xff,
    "resident i32.store8/load8_u roundtrip failed");
  expect((store16(1032, 0x1beef) >>> 0) === 0xbeef,
    "resident i32.store16/load16_u roundtrip failed");
  expect((store32(1040, 0xdeadbeef) >>> 0) === 0xdeadbeef,
    "resident i32.store roundtrip failed");
  expect(BigInt.asUintN(64, store64(1048, 0xfedcba9876543210n)) ===
      0xfedcba9876543210n,
  "resident i64.store roundtrip failed");

  expect((grow(1) >>> 0) === 1,
    "resident memory.grow did not return the old page count");
  expect((size() >>> 0) === 2 && memory.buffer.byteLength === 2 * 65536,
    "resident memory.size did not observe memory growth");
  return "PASS Wasm-resident arithmetic, typed stores, and memory growth";
}

export async function checkFetchedResidentMemorySurface(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentMemorySurface(await response.arrayBuffer());
}
