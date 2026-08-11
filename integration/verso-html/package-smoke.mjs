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

assert.equal(PRETTY_M_BROWSER_API_VERSION, "fir.prettyM.html.browser/v1");
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

let tick = 0;
const adapter = await createPrettyMAdapter({
  bytes,
  manifest,
  build,
  now: () => tick++,
});
const request = {
  format: F.tag(5, F.text('α<&"')),
  annotations: [{
    tag: 5,
    annotation: { cssClass: 'kw<&"', binding: 'b<&"' },
  }],
  width: 80,
  indent: 0,
  column: 0,
};
const prepared = adapter.prepare(request);
assert.equal(prepared.state, "prepared");
const executed = adapter.execute(prepared);
assert.equal(executed.state, "executed");
const result = adapter.decode(executed);
assert.equal(result.html,
  '<span class="kw&lt;&amp;&quot; token" data-binding="b&lt;&amp;&quot;">' +
  'α&lt;&amp;&quot;</span>');
assert.equal(result.memory.annotationEntries, 1);
assert.equal(result.memory.residentAllocationCalls, 2);
assert.ok(result.memory.frontierAfterDecode >= result.memory.frontierAfterPrepare);
for (const phase of ["normalizeMs", "allocateMs", "encodeMs", "prepareMs",
  "executeMs", "decodeMs", "totalMs"]) {
  assert.ok(Number.isFinite(result.timings[phase]) && result.timings[phase] >= 0,
    `${phase} must be a nonnegative timing`);
}

const plain = adapter.render({
  format: F.group(F.append(F.text("hello"),
    F.append(F.line(), F.text("λ")))),
  annotations: [],
  width: 4,
  indent: 2,
  column: 0,
});
assert.equal(plain.html, "hello\n  λ");

const nested = adapter.render({
  format: F.tag(1, F.append(F.text("a"), F.tag(2, F.text("b")))),
  annotations: [
    { tag: 1, annotation: { cssClass: "outer", binding: null } },
    { tag: 2, annotation: { cssClass: "inner", binding: "β" } },
  ],
  width: 80,
});
assert.equal(nested.html,
  '<span class="outer token">a</span>' +
  '<span class="inner token" data-binding="β">b</span>');

// Large enough to force memory growth while remaining a bounded package smoke.
// The source owner tracks the separate >= 1 MiB throughput case because the
// current source-level character-at-a-time escape loop is quadratic.
// Keep this below the separately tracked throughput case. The source entry's
// immutable character-at-a-time escaping is currently quadratic in the
// output length, so package correctness should not consume hundreds of MiB.
const growthAdapter = await createPrettyMAdapter({ bytes, manifest, build });
const largeText = "λ<&\"".repeat(512);
const large = growthAdapter.render({
  format: F.text(largeText),
  annotations: [],
  width: 1_000_000,
});
assert.equal(large.html.length, "λ&lt;&amp;&quot;".repeat(512).length);
assert.ok(large.memory.pagesAfterExecute > large.memory.pagesBefore,
  "large escaped output did not grow module memory");

let lastFrontier = nested.memory.frontierAfterDecode;
for (let index = 0; index < 32; index += 1) {
  const repeated = adapter.render(request);
  assert.equal(repeated.html, result.html);
  assert.ok(repeated.memory.frontierBefore >= lastFrontier,
    "repeated render rewound the instance-lifetime arena");
  lastFrontier = repeated.memory.frontierAfterDecode;
}

console.log(JSON.stringify({
  ok: true,
  apiVersion: PRETTY_M_BROWSER_API_VERSION,
  wasmBytes: bytes.byteLength,
  wasmSha256: build.artifact.sha256,
  imports: WebAssembly.Module.imports(module).length,
  functionExports: build.functionExports,
  residentAllocationCalls: result.memory.residentAllocationCalls,
  repeatedCalls: 32,
  boundedGrowthInputChars: largeText.length,
}));
