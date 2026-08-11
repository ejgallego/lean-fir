import assert from "../../../scripts/wasm_assert.mjs";

function equalParams(actual, expected) {
  return actual.length === expected.length &&
    actual.every((kind, index) => kind === expected[index]);
}

/**
 * Exercise prettyM through the concrete Wasm memory ABI. These helpers only
 * spell Lean 4.33's raw Format constructor layouts and packed-byte positions.
 */
export function checkConcretePrettyFormatModule({
  manifest,
  host,
  instance,
  entry: prettyM,
}) {
  assert.equal(manifest.result, "object");
  assert.ok(equalParams(manifest.params, ["tobject", "tobject", "tobject", "tobject"]),
    "concrete prettyM module has the wrong raw parameter ABI");

  const tagged = (payload) => host.encode("tobject", {
    kind: "tagged",
    payload: BigInt(payload),
  });
  const natural = (value) => {
    const physical = host.allocateNatural(BigInt(value));
    return host.encode("tobject", host.decode("tobject", physical));
  };
  const string = (value) => {
    const physical = host.allocateString(value);
    return host.encode("object", host.decode("object", physical));
  };
  const ctor = (name, tag, fields, fieldKinds, scalarBytes = []) => {
    const result = host.allocCtor({
      kind: "allocCtor",
      name,
      result: "tobject",
      size: fields.length,
      usize: 0,
      ssize: scalarBytes.length,
      tag: String(tag),
      fields: fieldKinds,
    }, fields);
    scalarBytes.forEach((value, offset) => {
      host.scalarSet({
        kind: "scalarSet",
        width: fields.length,
        offset,
        field: "uint8",
      }, [result, value]);
    });
    return result;
  };

  const nil = () => tagged(0);
  const line = () => tagged(1);
  const align = (force) =>
    ctor("Std.Format.align", 2, [], [], [force ? 1 : 0]);
  const text = (value) =>
    ctor("Std.Format.text", 3, [string(value)], ["object"]);
  const nest = (indent, body) =>
    ctor("Std.Format.nest", 4, [natural(indent), body], ["tobject", "tobject"]);
  const append = (left, right) =>
    ctor("Std.Format.append", 5, [left, right], ["tobject", "tobject"]);
  const group = (body, behavior = 0) =>
    ctor("Std.Format.group", 6, [body], ["tobject"], [behavior]);
  const tag = (kind, body) =>
    ctor("Std.Format.tag", 7, [natural(kind), body], ["tobject", "tobject"]);

  function callPretty(format, width, indent = 0, column = 0) {
    const args = [format, natural(width), natural(indent), natural(column)];
    const setFrontier = instance.exports.fir_heap_set_frontier;
    if (setFrontier !== undefined) {
      assert.equal(typeof setFrontier, "function");
      setFrontier(host.heapCursor);
    }
    const result = prettyM(...args) >>> 0;
    host.synchronizeResidentFrontierBeforeImport();
    assert.equal(host.classify(result), "heap",
      "concrete prettyM result must be heap-backed");
    return host.readString(result);
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

  const grouped = () => group(append(append(text("left"), line()), text("right")));
  assert.equal(callPretty(grouped(), 80), "left right");
  assert.equal(callPretty(grouped(), 5), "left\nright");

  return `PASS concrete raw-layout prettyM client (${manifest.entry})`;
}
