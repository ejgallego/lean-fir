function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function equal(actual, expected, message) {
  expect(actual === expected,
    `${message}: expected ${expected}, got ${actual}`);
}

/** Exercise target platform queries without a host-runtime fallback. */
export async function checkResidentPlatform(bytes) {
  const module = await WebAssembly.compile(bytes);
  equal(WebAssembly.Module.imports(module).length, 0,
    "resident platform module retained an import");
  const moduleExports = WebAssembly.Module.exports(module);
  expect(moduleExports.some(({ name, kind }) =>
    name === "memory" && kind === "memory"), "missing module-owned memory");
  const { exports } = await WebAssembly.instantiate(module, {});
  equal(typeof exports.fir_ext_System_Platform_getNumBits, "function",
    "missing System.Platform.getNumBits helper");
  equal(exports.fir_ext_System_Platform_getNumBits(1) >>> 0, 129,
    "System.Platform.getNumBits physical Nat result");
}
