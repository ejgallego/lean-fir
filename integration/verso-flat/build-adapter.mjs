import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const sourcePath = join(directory, "../talos/artifact/prettyM-browser-adapter.mjs");
const outputPath = process.argv[2] ?? join(directory, "_build/prettyM-browser-adapter.mjs");
let source = readFileSync(sourcePath, "utf8");

function replaceExactly(before, after, label) {
  const first = source.indexOf(before);
  if (first < 0 || source.indexOf(before, first + before.length) >= 0) {
    throw new Error(`Flat adapter specialization expected exactly one ${label}`);
  }
  source = source.slice(0, first) + after + source.slice(first + before.length);
}

replaceExactly(
  'export const PRETTY_M_BROWSER_API_VERSION = "fir.prettyM.browser/v1";',
  'export const PRETTY_M_BROWSER_API_VERSION = "fir.prettyM.flat.browser/v1";',
  "browser API declaration",
);
replaceExactly(
  "const STRING_UTF8_MARKER = 1;",
  "const STRING_UTF8_MARKER = 1;\nconst ARRAY_MARKER = 0x41525259;",
  "String marker declaration",
);
replaceExactly(
  "  integer: 6,\n});",
  "  integer: 6,\n  opaque: 8,\n});",
  "runtime kind table",
);

const readArray = `
function readArray(view, word, label, maximumNodes) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.opaque && header.aux0 === ARRAY_MARKER &&
    header.aux1 <= maximumNodes && header.aux2 >= header.aux1 &&
    HEADER_BYTES + SLOT_BYTES * header.aux1 <= header.bytes,
  \`\${label} is not a resident Array\`);
  return Array.from({ length: header.aux1 }, (_, index) =>
    readWord(view, header.address + HEADER_BYTES + SLOT_BYTES * index,
      \`\${label}[\${index}]\`));
}

function readSafeNatural(view, word, label) {
  const value = readNatural(view, word, label);
  requireCondition(value <= BigInt(Number.MAX_SAFE_INTEGER),
    \`\${label} exceeds JavaScript's safe integer range\`);
  return Number(value);
}

`;
replaceExactly(
  "function encodeNumberPlan(plan, allocate, view) {",
  readArray + "function encodeNumberPlan(plan, allocate, view) {",
  "numeric encoder boundary",
);

const decodeStart = source.indexOf("  decode(executed) {");
const renderStart = source.indexOf("\n  render(request) {", decodeStart);
if (decodeStart < 0 || renderStart < 0 ||
    source.indexOf("  decode(executed) {", decodeStart + 1) >= 0) {
  throw new Error("Flat adapter specialization could not isolate decode method");
}
const flatDecode = `  decode(executed) {
    requireCondition(executed?.[EXECUTED] === this,
      "decode received a handle from another adapter");
    requireCondition(executed.state === "executed",
      "execution handle has already been decoded");
    const started = this.now();
    const view = new DataView(this.memory.buffer);
    const [textWord, eventsWord] = readConstructor(
      view, executed.physicalResult, 0, 2, "Rendered");
    const text = readString(view, textWord, this.decoder, "Rendered.text");
    const eventWords = readArray(
      view, eventsWord, "Rendered.events", this.maximumNodes);
    const events = eventWords.map((eventWord, index) => {
      const fields = readConstructor(
        view, eventWord, 0, 3, \`Rendered.events[\${index}]\`);
      const event = {
        offset: readSafeNatural(view, fields[0],
          \`Rendered.events[\${index}].offset\`),
        kind: readSafeNatural(view, fields[1],
          \`Rendered.events[\${index}].kind\`),
        value: readSafeNatural(view, fields[2],
          \`Rendered.events[\${index}].value\`),
      };
      requireCondition(event.kind >= 0 && event.kind <= 2,
        \`Rendered event kind \${event.kind} is invalid\`);
      return event;
    });
    const decodeMs = elapsed(this.now, started);
    executed.state = "decoded";
    const timings = { ...executed.timings, decodeMs };
    timings.totalMs = timings.prepareMs + timings.executeMs + timings.decodeMs;
    return {
      rendered: { text, events },
      timings,
      memory: {
        ...executed.memory,
        frontierAfterDecode: this.synchronizeFrontier(),
        pagesAfterDecode: this.memory.buffer.byteLength / PAGE_BYTES,
      },
    };
  }
`;
source = source.slice(0, decodeStart) + flatDecode + source.slice(renderStart);
source = source.replaceAll("PrettyTrace object result", "Rendered object result");
source = source.replaceAll("styled trace", "flat rendered value");
source = source.replaceAll("production prettyM module", "production Flat prettyM module");

mkdirSync(dirname(outputPath), { recursive: true });
writeFileSync(outputPath, source);
console.log(`wrote ${Buffer.byteLength(source)} bytes to ${outputPath}`);

