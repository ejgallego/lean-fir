import assert from "../../../scripts/wasm_assert.mjs";

function equalParams(actual, expected) {
  return actual.length === expected.length &&
    actual.every((kind, index) => kind === expected[index]);
}

/**
 * Exercise a loaded prettyM module through Lean 4.32's raw Format layouts.
 * The helpers below describe constructor memory only; they are not a second
 * format AST or a source-level adapter.
 */
export function checkPrettyFormatModule({ manifest, host, entry: prettyM }) {
  assert.equal(manifest.result, "object");
  assert.ok(equalParams(manifest.params, ["tobject", "tobject", "tobject", "tobject"]),
    "prettyM module has the wrong raw parameter ABI");

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

  const hello = () => append(text("hello"), nest(2, append(line(), text("world"))));
  assert.equal(callPretty(hello(), 12), "hello\n  world");
  assert.equal(callPretty(hello(), 7), "hello\n  world");

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

  // Reuse `spaceUptoLine._closed_0`; this guards recursive cache persistence.
  const grouped = () => group(append(append(text("left"), line()), text("right")));
  assert.equal(callPretty(grouped(), 80), "left right");
  assert.equal(callPretty(grouped(), 5), "left\nright");

  return `PASS reusable JavaScript prettyM client (${manifest.entry})`;
}
