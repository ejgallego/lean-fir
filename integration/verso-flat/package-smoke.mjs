import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  PRETTY_M_BROWSER_API_VERSION,
  PrettyFormat as F,
  createPrettyMAdapter,
} from "./prettyM-browser-adapter.mjs";

const bytes = readFileSync(new URL("./prettyM.wasm", import.meta.url));
const manifest = JSON.parse(readFileSync(
  new URL("./prettyM.wasm.json", import.meta.url), "utf8"));
const build = JSON.parse(readFileSync(
  new URL("./BUILD.json", import.meta.url), "utf8"));

assert.equal(PRETTY_M_BROWSER_API_VERSION, "fir.prettyM.flat.browser/v1");
const module = await WebAssembly.compile(bytes);
assert.deepEqual(WebAssembly.Module.imports(module), []);
assert.deepEqual(WebAssembly.Module.exports(module).map(({ name, kind }) =>
  ({ name, kind })), [
  { name: manifest.entry, kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);

const adapter = await createPrettyMAdapter({ bytes, manifest, build });
const result = adapter.render({
  format: F.tag(5, F.text("α")),
  width: 80,
  indent: 0,
  column: 0,
});
assert.deepEqual(result.rendered, {
  text: "α",
  events: [
    { offset: 0, kind: 0, value: 5 },
    { offset: 2, kind: 1, value: 1 },
  ],
});
for (const phase of ["normalizeMs", "allocateMs", "encodeMs", "prepareMs",
  "executeMs", "decodeMs", "totalMs"]) {
  assert.ok(Number.isFinite(result.timings[phase]) && result.timings[phase] >= 0,
    `${phase} must be a nonnegative timing`);
}
assert.equal(result.memory.residentAllocationCalls, 1);
console.log(JSON.stringify({
  ok: true,
  apiVersion: PRETTY_M_BROWSER_API_VERSION,
  wasmBytes: bytes.byteLength,
  wasmSha256: build.artifact.sha256,
  imports: WebAssembly.Module.imports(module).length,
  functionExports: build.functionExports,
  textBytes: 2,
  events: 2,
}));

