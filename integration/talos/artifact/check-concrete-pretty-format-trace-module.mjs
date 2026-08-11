import assert from "../../../scripts/wasm_assert.mjs";

const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const CONSTRUCTOR_KIND = 1;
const NATURAL_KIND = 5;

function equalParams(actual, expected) {
  return actual.length === expected.length &&
    actual.every((kind, index) => kind === expected[index]);
}

function constructor(host, word, expectedTag, expectedFields, label) {
  assert.equal(host.classify(word), "heap", `${label} must be heap-backed`);
  const header = host.readHeader(word);
  assert.equal(header.kind, CONSTRUCTOR_KIND, `${label} must be a constructor`);
  assert.equal(header.aux0, expectedTag, `${label} constructor tag changed`);
  assert.equal(header.aux1, expectedFields, `${label} object-field count changed`);
  assert.equal(header.aux2, 0, `${label} unexpectedly has usize fields`);
  assert.equal(header.aux3, 0, `${label} unexpectedly has scalar bytes`);
  return Array.from({ length: expectedFields }, (_, index) =>
    host.readWordSlot(word + HEADER_BYTES + SLOT_BYTES * index));
}

function natural(host, word, label) {
  if (host.classify(word) === "immediate") {
    return host.decodeImmediate(word);
  }
  assert.equal(host.classify(word), "heap", `${label} has an invalid Nat word`);
  const header = host.readHeader(word);
  assert.equal(header.kind, NATURAL_KIND, `${label} must be a Nat`);
  return host.readNatural(word, header);
}

function string(host, word, label) {
  assert.equal(host.classify(word), "heap", `${label} must be a String object`);
  return host.readString(word);
}

function decodeEvent(host, word) {
  const [kind, text, value] = constructor(host, word, 0, 3, "pretty trace event");
  const decoded = {
    kind: Number(natural(host, kind, "pretty trace event kind")),
    text: string(host, text, "pretty trace event text"),
    value: natural(host, value, "pretty trace event value"),
  };
  assert.ok(decoded.kind >= 0 && decoded.kind <= 3,
    `unknown pretty trace event kind ${decoded.kind}`);
  if (decoded.kind === 0) {
    assert.equal(decoded.value, 0n, "output event must have a zero numeric payload");
  } else {
    assert.equal(decoded.text, "", "numeric event must have an empty text payload");
  }
  return decoded;
}

function decodeEventList(host, root) {
  const eventsRev = [];
  const seen = new Set();
  let word = root;
  while (host.classify(word) !== "immediate") {
    assert.equal(host.classify(word), "heap", "pretty trace event list is malformed");
    assert.ok(!seen.has(word), "pretty trace event list contains a cycle");
    seen.add(word);
    const [head, tail] = constructor(host, word, 1, 2, "pretty trace list cons");
    eventsRev.push(decodeEvent(host, head));
    word = tail;
  }
  assert.equal(host.decodeImmediate(word), 0n, "pretty trace list has a non-nil tail");
  return eventsRev.reverse();
}

/** Decode the deliberately raw `{ text, eventsRev }` result representation. */
export function decodeConcretePrettyTrace(host, physicalResult) {
  assert.equal(host.classify(physicalResult), "heap",
    "pretty trace result must be heap-backed");
  const address = Number(physicalResult) >>> 0;
  const [text, eventsRev] = constructor(host, address, 0, 2, "pretty trace result");
  return {
    text: string(host, text, "pretty trace text"),
    events: decodeEventList(host, eventsRev),
  };
}

function renderedText(events) {
  let result = "";
  for (const event of events) {
    if (event.kind === 0) {
      result += event.text;
    } else if (event.kind === 1) {
      result += `\n${" ".repeat(Number(event.value))}`;
    }
  }
  return result;
}

const event = (kind, text = "", value = 0n) => ({ kind, text, value });
const coverageOracle = [
  event(3),
  event(2, "", 7n),
  event(0, "α"),
  event(3),
  event(0, " "),
  event(3),
  event(0, "β"),
  event(3, "", 1n),
  event(1),
  event(3),
  event(0, "."),
  event(3),
  event(0, " "),
  event(3),
  event(0, "γ"),
  event(3),
  event(1, "", 2n),
  event(3),
  event(0, "δ"),
  event(1, "", 2n),
  event(0, "ε"),
  event(3),
];

/**
 * Exercise the styled facade using only Lean 4.33's raw Format and result
 * layouts. The expected event sequence is also guarded by the native Lean
 * oracle in `FirWasmSourceExample.lean`.
 */
export function checkConcretePrettyFormatTraceModule({
  manifest,
  host,
  instance,
  entry: prettyM,
}) {
  assert.equal(manifest.result, "object");
  assert.ok(equalParams(manifest.params, ["tobject", "tobject", "tobject", "tobject"]),
    "styled prettyM module has the wrong raw parameter ABI");

  const tagged = (payload) => host.encode("tobject", {
    kind: "tagged",
    payload: BigInt(payload),
  });
  const naturalArgument = (value) => {
    const physical = host.allocateNatural(BigInt(value));
    return host.encode("tobject", host.decode("tobject", physical));
  };
  const stringArgument = (value) => {
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
  const align = (force) => ctor("Std.Format.align", 2, [], [], [force ? 1 : 0]);
  const text = (value) =>
    ctor("Std.Format.text", 3, [stringArgument(value)], ["object"]);
  const nest = (indent, body) =>
    ctor("Std.Format.nest", 4, [naturalArgument(indent), body], ["tobject", "tobject"]);
  const append = (left, right) =>
    ctor("Std.Format.append", 5, [left, right], ["tobject", "tobject"]);
  const group = (body, behavior = 0) =>
    ctor("Std.Format.group", 6, [body], ["tobject"], [behavior]);
  const tag = (kind, body) =>
    ctor("Std.Format.tag", 7, [naturalArgument(kind), body], ["tobject", "tobject"]);

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
  const args = [
    allConstructors,
    naturalArgument(80),
    naturalArgument(0),
    naturalArgument(0),
  ];
  const setFrontier = instance.exports.fir_heap_set_frontier;
  assert.equal(typeof setFrontier, "function");
  setFrontier(host.heapCursor);
  const trace = decodeConcretePrettyTrace(host, prettyM(...args));

  assert.equal(trace.text, "α β\n. γ\n  δ\n  ε");
  assert.equal(renderedText(trace.events), trace.text);
  assert.deepStrictEqual(trace.events, coverageOracle);
  assert.ok(!host.trace.some((entry) => entry.name === "panicCore" ||
    entry.name === "instInhabitedOfMonad._redArg"));

  return `PASS concrete styled prettyM trace (${manifest.entry})`;
}
