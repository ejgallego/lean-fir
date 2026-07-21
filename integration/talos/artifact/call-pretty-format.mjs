import assert from "node:assert/strict";
import fs from "node:fs";

import { formatExternalRegistry } from "../../../scripts/wasm_format_externals.mjs";
import { SemanticHost } from "../../../scripts/wasm_semantic_host.mjs";

const artifactPath = process.argv[2];
assert.ok(artifactPath, "usage: node call-pretty-format.mjs ARTIFACT.wasm");

const bytes = fs.readFileSync(artifactPath);
const manifest = JSON.parse(fs.readFileSync(`${artifactPath}.json`, "utf8"));
assert.ok(WebAssembly.validate(bytes), `${artifactPath} failed WebAssembly validation`);
assert.equal(manifest.result, "object");
assert.deepStrictEqual(manifest.params, ["tobject", "tobject", "tobject", "tobject"]);
assert.ok(!Object.hasOwn(manifest, "fixture"));
assert.ok(!Object.hasOwn(manifest, "arguments"));
assert.ok(!Object.hasOwn(manifest, "initialRuntime"));

// This descriptor intentionally contains no reproducible build-time
// invocation. A caller allocates ordinary semantic runtime values and passes
// their opaque handles directly to the reusable module.
const host = new SemanticHost(undefined, formatExternalRegistry);
const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
const prettyM = instance.exports[manifest.entry];
assert.equal(typeof prettyM, "function");

const tagged = (payload) => ({ kind: "tagged", payload: BigInt(payload) });
const scalarUInt8 = (value) => ({
  kind: "scalar",
  scalarKind: "uint8",
  value: BigInt(value),
});
const ctor = (tag, objectFields, scalarFields = []) => host.alloc({
  kind: "ctor",
  tag: BigInt(tag),
  objectFields,
  usizeFields: [],
  scalarFields,
});

// These are the eight Lean 4.32 `Std.Format` constructors. The helpers expose
// only their runtime layout; they do not introduce a second format AST.
const nil = () => tagged(0);
const line = () => tagged(1);
const align = (force) => ctor(2, [], [{
  width: 0,
  offset: 0,
  value: scalarUInt8(force ? 1 : 0),
}]);
const text = (value) => ctor(3, [host.alloc({ kind: "string", value })]);
const nest = (indent, body) => ctor(4, [host.natural(indent), body]);
const append = (left, right) => ctor(5, [left, right]);
const group = (body, behavior = 0) => ctor(6, [body], [{
  // The semantic runtime key is (object-field count, byte offset).
  width: 1,
  offset: 0,
  value: scalarUInt8(behavior),
}]);
const tag = (kind, body) => ctor(7, [host.natural(kind), body]);

function callPretty(format, width, indent = 0, column = 0) {
  const args = [format, host.natural(width), host.natural(indent), host.natural(column)]
    .map((value) => host.encode("tobject", value));
  const result = host.decode("object", prettyM(...args));
  assert.equal(result.kind, "heap");
  const object = host.liveCell(result.location).object;
  assert.equal(object.kind, "string");
  return object.value;
}

// One module instance accepts unrelated caller-created heaps. Neither call
// reads the build-time `initialRuntime` or its attached arguments.
const hello = () => append(text("hello"), nest(2, append(line(), text("world"))));
assert.equal(callPretty(hello(), 12), "hello\n  world");
assert.equal(callPretty(hello(), 7), "hello\n  world");

// Exercise every constructor from JavaScript, including both scalar-bearing
// layouts, a tag value, Unicode text, and a caller-provided starting column.
const allConstructors = append(
  append(
    append(nil(), tag(7, group(append(append(text("α"), line()), text("β"))))),
    line(),
  ),
  nest(2, append(
    append(append(append(text("."), align(false)), text("γ")), line()),
    text("δ\nε"),
  )),
);
assert.equal(callPretty(allConstructors, 80), "α β\n. γ\n  δ\n  ε");

assert.ok(!host.trace.some((event) => event.name === "panicCore" ||
  event.name === "instInhabitedOfMonad._redArg"));

// A longer standalone group reuses `spaceUptoLine._closed_0`; this is the
// regression that originally exposed missing recursive cache persistence.
const grouped = () => group(append(append(text("left"), line()), text("right")));
assert.equal(callPretty(grouped(), 80), "left right");
assert.equal(callPretty(grouped(), 5), "left\nright");

console.log(`PASS reusable JavaScript prettyM client (${manifest.entry})`);
