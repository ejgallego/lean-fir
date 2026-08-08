import {
  PrettyFormat as F,
  createPrettyMAdapter,
  fetchPrettyMAdapter,
} from "./prettyM-browser-adapter.mjs";

function requireCondition(condition, message) {
  if (!condition) {
    throw new Error(`prettyM browser adapter check: ${message}`);
  }
}

function expectFailure(action, fragment) {
  try {
    action();
  } catch (error) {
    requireCondition(String(error).includes(fragment),
      `expected failure containing ${fragment}, got ${error}`);
    return;
  }
  throw new Error(`prettyM browser adapter check: expected ${fragment} failure`);
}

function equalEvents(actual, expected) {
  return actual.length === expected.length &&
    actual.every((event, index) => {
      const oracle = expected[index];
      return event.kind === oracle.kind &&
        event.text === oracle.text &&
        event.value === oracle.value;
    });
}

function coverageFormat() {
  return F.append(
    F.append(
      F.append(
        F.nil(),
        F.tag(7, F.group(F.append(
          F.append(F.text("α"), F.line()),
          F.text("β"),
        ))),
      ),
      F.line(),
    ),
    F.nest(2, F.append(
      F.append(
        F.append(
          F.append(F.text("."), F.align(false)),
          F.text("γ"),
        ),
        F.line(),
      ),
      F.text("δ\nε"),
    )),
  );
}

const event = (kind, text = "", value = 0n) => ({ kind, text, value });
const coverageEvents = [
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

const hugeNumeric = (1n << 130n) + 17n;
const walkerStressNumeric = (1n << (64n * 8192n)) + 17n;

function numericCoverageFormat(value = hugeNumeric) {
  return F.append(
    F.tag(value, F.text("tag")),
    F.append(
      F.nest(value, F.text("+")),
      F.nest(-value, F.text("-")),
    ),
  );
}

const numericCoverageEvents = (value) => [
  event(2, "", value),
  event(0, "tag"),
  event(3, "", 1n),
  event(0, "+"),
  event(3),
  event(0, "-"),
  event(3),
];

const stressUtf8Bytes = 1024 * 1024;
const stressText = "λ".repeat(stressUtf8Bytes / 2);
const stressRepeatedCalls = 32;
const coldBalancedDepth = 10;

function balancedAppendTree(depth) {
  if (depth === 0) {
    return F.text("x");
  }
  const child = balancedAppendTree(depth - 1);
  return F.append(child, child);
}

function checkColdBalancedResult(result) {
  const leafCount = 1 << coldBalancedDepth;
  requireCondition(result.memory.formatNodes === 2 * leafCount - 1,
    "cold balanced append tree node count changed");
  requireCondition(result.trace.text === "x".repeat(leafCount),
    "cold balanced append tree text changed");
  requireCondition(result.trace.events.length === 2 * leafCount &&
    result.trace.events.every((entry, index) =>
      index % 2 === 0 ?
        entry.kind === 0 && entry.text === "x" && entry.value === 0n :
        entry.kind === 3 && entry.text === "" && entry.value === 0n),
  "cold balanced append tree event stream changed");
  checkTimings(result);
}

function checkUtf8ReplacementResult(result, previous) {
  const expected = "A😀�B�";
  requireCondition(result.trace.text === expected,
    "UTF-8 replacement text changed");
  requireCondition(equalEvents(result.trace.events, [
    event(0, expected),
    event(3),
  ]), "UTF-8 replacement event stream changed");
  checkTimings(result);
  requireCondition(result.memory.frontierBefore >=
      previous.memory.frontierAfterDecode,
    "UTF-8 replacement render did not synchronize the resident frontier");
}

function checkTimings(result) {
  for (const [name, value] of Object.entries(result.timings)) {
    requireCondition(Number.isFinite(value) && value >= 0,
      `timing ${name} is invalid`);
  }
}

function checkResult(result, previous) {
  requireCondition(result.trace.text === "α β\n. γ\n  δ\n  ε",
    "styled text projection changed");
  requireCondition(equalEvents(result.trace.events, coverageEvents),
    "styled event sequence changed");
  checkTimings(result);
  requireCondition(result.memory.residentAllocationCalls === 1,
    "adapter did not use one bulk resident allocation");
  requireCondition(result.memory.inputBytes > 0 &&
    result.memory.frontierAfterPrepare ===
      result.memory.frontierBefore + result.memory.inputBytes,
  "adapter input frontier accounting changed");
  requireCondition(result.memory.frontierAfterDecode >=
    result.memory.frontierAfterExecute,
  "decode rewound the resident frontier");
  if (previous !== undefined) {
    requireCondition(result.memory.frontierBefore >=
      previous.memory.frontierAfterDecode,
    "repeated render did not synchronize the resident frontier");
  }
}

function checkNumericResult(result, previous, value = hugeNumeric,
    label = "arbitrary-precision numeric coverage") {
  requireCondition(result.trace.text === "tag+-",
    `${label} text projection changed`);
  requireCondition(equalEvents(result.trace.events, numericCoverageEvents(value)),
    `${label} styled event sequence changed`);
  checkTimings(result);
  requireCondition(result.memory.residentAllocationCalls === 1,
    `${label} did not use one bulk resident allocation`);
  requireCondition(result.memory.frontierBefore >=
    previous.memory.frontierAfterDecode,
  `${label} did not synchronize the resident frontier`);
}

function checkTaggedResult(result, text, tag, previous, label) {
  requireCondition(result.trace.text === text,
    `${label} text projection changed`);
  requireCondition(equalEvents(result.trace.events, [
    event(2, "", tag),
    event(0, text),
    event(3, "", 1n),
  ]), `${label} styled event sequence changed`);
  checkTimings(result);
  requireCondition(result.memory.residentAllocationCalls === 1,
    `${label} did not use one bulk resident allocation`);
  requireCondition(result.memory.frontierBefore >=
    previous.memory.frontierAfterDecode,
  `${label} did not synchronize the resident frontier`);
}

function exerciseStress(adapter, previous) {
  const large = adapter.render({
    format: F.tag(hugeNumeric, F.text(stressText)),
    width: hugeNumeric,
  });
  checkTaggedResult(large, stressText, hugeNumeric, previous,
    "1 MiB UTF-8 coverage");
  requireCondition(large.memory.inputBytes >= stressUtf8Bytes,
    "1 MiB UTF-8 coverage did not encode the complete input");
  requireCondition(large.memory.pagesAfterDecode > large.memory.pagesBefore,
    "1 MiB UTF-8 coverage did not grow module-owned memory");

  let current = large;
  for (let index = 0; index < stressRepeatedCalls; index += 1) {
    const text = `repeat-${index}`;
    const tag = hugeNumeric + BigInt(index);
    const next = adapter.render({
      format: F.tag(tag, F.text(text)),
      width: hugeNumeric,
    });
    checkTaggedResult(next, text, tag, current,
      `repeated coverage call ${index}`);
    current = next;
  }
  return current;
}

export async function checkPrettyMBrowserAdapter({
  bytes,
  manifest,
  build,
}) {
  const adapter = await createPrettyMAdapter({ bytes, manifest, build });
  const coldBalanced = adapter.render({
    format: balancedAppendTree(coldBalancedDepth),
    width: 80,
  });
  checkColdBalancedResult(coldBalanced);
  const input = coverageFormat();
  const first = adapter.render({ format: input, width: 80 });
  checkResult(first, coldBalanced);
  const utf8Replacement = adapter.render({
    format: F.text("A😀\ud800B\udc00"),
    width: 80,
  });
  checkUtf8ReplacementResult(utf8Replacement, first);
  const prepared = adapter.prepare({
    format: input,
    width: (1n << 130n) + 17n,
    indent: "0",
    column: 0n,
  });
  const executed = adapter.execute(prepared);
  const second = adapter.decode(executed);
  checkResult(second, utf8Replacement);
  const numeric = adapter.render({
    format: numericCoverageFormat(),
    width: 80,
  });
  checkNumericResult(numeric, second);
  const numericStress = adapter.render({
    format: numericCoverageFormat(walkerStressNumeric),
    width: walkerStressNumeric,
  });
  checkNumericResult(numericStress, numeric, walkerStressNumeric,
    "8,192-limb numeric walker coverage");
  expectFailure(() => adapter.execute(prepared), "already been consumed");
  expectFailure(() => adapter.decode(executed), "already been decoded");
  const cyclic = { kind: "group", body: undefined };
  cyclic.body = cyclic;
  expectFailure(() => adapter.prepare({ format: cyclic, width: 80 }),
    "contains a cycle");
  exerciseStress(adapter, numericStress);
  return "PASS production browser prettyM adapter with stack-safe stress";
}

export async function checkFetchedPrettyMBrowserAdapter(artifactUrl) {
  const adapter = await fetchPrettyMAdapter(artifactUrl);
  const coldBalanced = adapter.render({
    format: balancedAppendTree(coldBalancedDepth),
    width: 80,
  });
  checkColdBalancedResult(coldBalanced);
  const first = adapter.render({ format: coverageFormat(), width: 80 });
  checkResult(first, coldBalanced);
  const utf8Replacement = adapter.render({
    format: F.text("A😀\ud800B\udc00"),
    width: 80,
  });
  checkUtf8ReplacementResult(utf8Replacement, first);
  const prepared = adapter.prepare({
    format: coverageFormat(),
    width: "1361129467683753853853498429727072845841",
  });
  const second = adapter.decode(adapter.execute(prepared));
  checkResult(second, utf8Replacement);
  const numeric = adapter.render({
    format: numericCoverageFormat(),
    width: 80,
  });
  checkNumericResult(numeric, second);
  const numericStress = adapter.render({
    format: numericCoverageFormat(walkerStressNumeric),
    width: walkerStressNumeric,
  });
  checkNumericResult(numericStress, numeric, walkerStressNumeric,
    "8,192-limb numeric walker coverage");
  exerciseStress(adapter, numericStress);
  return "PASS fetched production browser prettyM adapter with stack-safe stress";
}
