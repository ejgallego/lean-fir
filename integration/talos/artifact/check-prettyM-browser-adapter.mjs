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

function numericCoverageFormat() {
  return F.append(
    F.tag(hugeNumeric, F.text("tag")),
    F.append(
      F.nest(hugeNumeric, F.text("+")),
      F.nest(-hugeNumeric, F.text("-")),
    ),
  );
}

const numericCoverageEvents = [
  event(2, "", hugeNumeric),
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

function checkNumericResult(result, previous) {
  requireCondition(result.trace.text === "tag+-",
    "arbitrary-precision numeric text projection changed");
  requireCondition(equalEvents(result.trace.events, numericCoverageEvents),
    "arbitrary-precision styled event sequence changed");
  requireCondition(result.memory.residentAllocationCalls === 1,
    "numeric coverage did not use one bulk resident allocation");
  requireCondition(result.memory.frontierBefore >=
    previous.memory.frontierAfterDecode,
  "numeric coverage did not synchronize the resident frontier");
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
  const input = coverageFormat();
  const first = adapter.render({ format: input, width: 80 });
  checkResult(first);
  const prepared = adapter.prepare({
    format: input,
    width: (1n << 130n) + 17n,
    indent: "0",
    column: 0n,
  });
  const executed = adapter.execute(prepared);
  const second = adapter.decode(executed);
  checkResult(second, first);
  const numeric = adapter.render({
    format: numericCoverageFormat(),
    width: 80,
  });
  checkNumericResult(numeric, second);
  expectFailure(() => adapter.execute(prepared), "already been consumed");
  expectFailure(() => adapter.decode(executed), "already been decoded");
  const cyclic = { kind: "group", body: undefined };
  cyclic.body = cyclic;
  expectFailure(() => adapter.prepare({ format: cyclic, width: 80 }),
    "contains a cycle");
  exerciseStress(adapter, numeric);
  return "PASS production browser prettyM adapter with stack-safe stress";
}

export async function checkFetchedPrettyMBrowserAdapter(artifactUrl) {
  const adapter = await fetchPrettyMAdapter(artifactUrl);
  const first = adapter.render({ format: coverageFormat(), width: 80 });
  checkResult(first);
  const prepared = adapter.prepare({
    format: coverageFormat(),
    width: "1361129467683753853853498429727072845841",
  });
  const second = adapter.decode(adapter.execute(prepared));
  checkResult(second, first);
  const numeric = adapter.render({
    format: numericCoverageFormat(),
    width: 80,
  });
  checkNumericResult(numeric, second);
  exerciseStress(adapter, numeric);
  return "PASS fetched production browser prettyM adapter with stack-safe stress";
}
