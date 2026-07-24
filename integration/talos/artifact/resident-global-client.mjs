function expect(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

export async function checkResidentGlobal(bytes) {
  expect(WebAssembly.validate(bytes),
    "resident global module failed WebAssembly validation");
  const module = new WebAssembly.Module(bytes);
  expect(WebAssembly.Module.imports(module).length === 0,
    "resident global module retained an import");
  const exports = WebAssembly.Module.exports(module);
  expect(exports.some(({ name, kind }) =>
    name === "residentGlobal" && kind === "function"),
  "resident global getter export is missing");
  expect(exports.some(({ name, kind }) =>
    name === "residentGlobalSet" && kind === "function"),
  "resident global setter export is missing");

  const instance = await WebAssembly.instantiate(module, {});
  const get = instance.exports.residentGlobal;
  const set = instance.exports.residentGlobalSet;
  expect((get() >>> 0) === 1024,
    "resident global lost its nonzero initializer");
  set(2048);
  expect((get() >>> 0) === 2048,
    "resident global is not mutable");
  return "PASS typed initialized mutable Wasm-resident global";
}

export async function checkFetchedResidentGlobal(url) {
  const response = await fetch(url);
  expect(response.ok, `failed to fetch ${url}: HTTP ${response.status}`);
  return checkResidentGlobal(await response.arrayBuffer());
}
