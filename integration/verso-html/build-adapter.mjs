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
    throw new Error(`HTML adapter specialization expected exactly one ${label}`);
  }
  source = source.slice(0, first) + after + source.slice(first + before.length);
}

replaceExactly(
  'export const PRETTY_M_BROWSER_API_VERSION = "fir.prettyM.browser/v1";',
  'export const PRETTY_M_BROWSER_API_VERSION = "fir.prettyM.html.browser/v1";',
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
replaceExactly(
  "    manifest.params.length === 4 &&\n    manifest.params.every((kind) => kind === \"tobject\"),\n  \"module descriptor must expose Format × Nat × Nat × Nat\");",
  "    manifest.params.length === 5 &&\n    manifest.params[0] === \"tobject\" &&\n    manifest.params[1] === \"object\" &&\n    manifest.params.slice(2).every((kind) => kind === \"tobject\"),\n  \"module descriptor must expose Format × Array TaggedAnnotation × Nat × Nat × Nat\");",
  "physical parameter ABI",
);
replaceExactly(
  "    \"module descriptor must expose a PrettyTrace object result\");",
  "    \"module descriptor must expose an HTML String object result\");",
  "result ABI description",
);
replaceExactly(
  "export class PrettyMAdapter {",
  "class PrettyMHtmlBaseAdapter {",
  "base adapter class",
);

const htmlSupport = `
function normalizeAnnotations(value, maximumNodes) {
  requireCondition(Array.isArray(value), "annotations must be an Array");
  requireCondition(value.length <= maximumNodes,
    "annotations exceeds " + maximumNodes + " entries");
  const tags = new Set();
  let totalBytes = align8(HEADER_BYTES + SLOT_BYTES * value.length);
  const entries = value.map((entry, index) => {
    requireCondition(entry !== null && typeof entry === "object" &&
      !Array.isArray(entry), "annotations[" + index + "] must be an object");
    requireCondition(Object.keys(entry).length === 2 &&
      Object.hasOwn(entry, "tag") && Object.hasOwn(entry, "annotation"),
    "annotations[" + index + "] must contain exactly tag and annotation");
    const tag = naturalPlan(natural(entry.tag, "annotations[" + index + "].tag"));
    const tagKey = tag.value.toString();
    requireCondition(!tags.has(tagKey),
      "annotations contains duplicate tag " + tagKey);
    tags.add(tagKey);
    const annotation = entry.annotation;
    requireCondition(annotation !== null && typeof annotation === "object" &&
      !Array.isArray(annotation),
    "annotations[" + index + "].annotation must be an object");
    requireCondition(Object.keys(annotation).every((key) =>
      key === "cssClass" || key === "binding") &&
      Object.hasOwn(annotation, "cssClass"),
    "annotations[" + index + "].annotation has an invalid shape");
    requireCondition(typeof annotation.cssClass === "string",
      "annotations[" + index + "].annotation.cssClass must be a string");
    const binding = annotation.binding === undefined ? null : annotation.binding;
    requireCondition(binding === null || typeof binding === "string",
      "annotations[" + index + "].annotation.binding must be null or a string");
    const cssBytes = utf8Length(annotation.cssClass);
    const cssStringBytes = align8(HEADER_BYTES + cssBytes);
    const bindingBytes = binding === null ? 0 : utf8Length(binding);
    const bindingStringBytes = binding === null ? 0 :
      align8(HEADER_BYTES + bindingBytes);
    const optionBytes = binding === null ? 0 : 40;
    const bytes = tag.bytes + 48 + 48 + cssStringBytes +
      bindingStringBytes + optionBytes;
    totalBytes = checkedTotal(totalBytes, bytes, "annotations input");
    return {
      tag,
      cssClass: annotation.cssClass,
      cssBytes,
      cssStringBytes,
      binding,
      bindingBytes,
      bindingStringBytes,
      optionBytes,
    };
  });
  return { entries, totalBytes };
}

function encodeStringValue(adapter, view, take, value, payloadBytes, bytes) {
  const address = take(bytes);
  writeHeader(view, address, {
    kind: KIND.string,
    bytes,
    aux0: STRING_UTF8_MARKER,
    aux1: payloadBytes,
  });
  const payload = new Uint8Array(
    adapter.memory.buffer, address + HEADER_BYTES, bytes - HEADER_BYTES);
  const encoded = adapter.encoder.encodeInto(value, payload);
  requireCondition(encoded.read === value.length && encoded.written === payloadBytes,
    "TextEncoder did not encode a complete annotation String");
  payload.fill(0, encoded.written);
  return address;
}

class PrettyMHtmlAdapter extends PrettyMHtmlBaseAdapter {
  encodeAnnotations(normalized) {
    const frontierBefore = this.synchronizeFrontier();
    const allocateStarted = this.now();
    const block = u32(this.allocate(normalized.totalBytes));
    const allocateMs = elapsed(this.now, allocateStarted);
    requireCondition(block === frontierBefore,
      "resident annotation allocator returned an unexpected address");
    const frontierAfter = this.synchronizeFrontier();
    requireCondition(frontierAfter === frontierBefore + normalized.totalBytes,
      "resident annotation allocator advanced by the wrong size");
    const encodeStarted = this.now();
    const view = new DataView(this.memory.buffer);
    let cursor = block;
    let rawObjects = 0;
    const take = (bytes) => {
      requireCondition(bytes >= HEADER_BYTES && bytes % 8 === 0,
        "annotation suballocation size is invalid");
      const result = cursor;
      cursor += bytes;
      requireCondition(cursor <= block + normalized.totalBytes,
        "annotation encoder exceeded its bulk allocation");
      rawObjects += 1;
      return result;
    };
    const arrayWord = take(align8(
      HEADER_BYTES + SLOT_BYTES * normalized.entries.length));
    const encodedEntries = normalized.entries.map((entry) => {
      const taggedWord = take(48);
      const annotationWord = take(48);
      const tagWord = encodeNumberPlan(entry.tag, take, view);
      const cssWord = encodeStringValue(this, view, take,
        entry.cssClass, entry.cssBytes, entry.cssStringBytes);
      let bindingWord = immediateWord(0n);
      if (entry.binding !== null) {
        const stringWord = encodeStringValue(this, view, take,
          entry.binding, entry.bindingBytes, entry.bindingStringBytes);
        bindingWord = take(entry.optionBytes);
        writeHeader(view, bindingWord, {
          kind: KIND.constructor,
          bytes: entry.optionBytes,
          aux0: 1,
          aux1: 1,
        });
        writeWord(view, bindingWord + HEADER_BYTES, stringWord);
      }
      writeHeader(view, annotationWord, {
        kind: KIND.constructor,
        bytes: 48,
        aux0: 0,
        aux1: 2,
      });
      writeWord(view, annotationWord + HEADER_BYTES, cssWord);
      writeWord(view, annotationWord + HEADER_BYTES + SLOT_BYTES, bindingWord);
      writeHeader(view, taggedWord, {
        kind: KIND.constructor,
        bytes: 48,
        aux0: 0,
        aux1: 2,
      });
      writeWord(view, taggedWord + HEADER_BYTES, tagWord);
      writeWord(view, taggedWord + HEADER_BYTES + SLOT_BYTES, annotationWord);
      return taggedWord;
    });
    writeHeader(view, arrayWord, {
      kind: KIND.opaque,
      flags: PERSISTENT_LIVE_FLAGS,
      rc: 0,
      bytes: align8(HEADER_BYTES + SLOT_BYTES * encodedEntries.length),
      aux0: ARRAY_MARKER,
      aux1: encodedEntries.length,
      aux2: encodedEntries.length,
    });
    encodedEntries.forEach((word, index) =>
      writeWord(view, arrayWord + HEADER_BYTES + SLOT_BYTES * index, word));
    requireCondition(cursor === block + normalized.totalBytes,
      "annotation encoder did not consume its complete bulk allocation");
    return {
      word: arrayWord,
      allocateMs,
      encodeMs: elapsed(this.now, encodeStarted),
      frontierAfter,
      inputBytes: normalized.totalBytes,
      rawObjects,
    };
  }

  prepare({ format, annotations = [], width, indent = 0, column = 0 }) {
    const started = this.now();
    const normalizeStarted = this.now();
    const normalizedAnnotations = normalizeAnnotations(
      annotations, this.maximumNodes);
    const annotationsNormalizeMs = elapsed(this.now, normalizeStarted);
    const prepared = super.prepare({ format, width, indent, column });
    const encodedAnnotations = this.encodeAnnotations(normalizedAnnotations);
    prepared.args.splice(1, 0, i32(encodedAnnotations.word));
    prepared.timings.normalizeMs += annotationsNormalizeMs;
    prepared.timings.allocateMs += encodedAnnotations.allocateMs;
    prepared.timings.encodeMs += encodedAnnotations.encodeMs;
    prepared.timings.prepareMs = elapsed(this.now, started);
    prepared.memory.frontierAfterPrepare = encodedAnnotations.frontierAfter;
    prepared.memory.pagesAfterPrepare = this.memory.buffer.byteLength / PAGE_BYTES;
    prepared.memory.inputBytes += encodedAnnotations.inputBytes;
    prepared.memory.residentAllocationCalls += 1;
    prepared.memory.rawObjects += encodedAnnotations.rawObjects;
    prepared.memory.annotationEntries = normalizedAnnotations.entries.length;
    return prepared;
  }

  decode(executed) {
    requireCondition(executed?.[EXECUTED] === this,
      "decode received a handle from another adapter");
    requireCondition(executed.state === "executed",
      "execution handle has already been decoded");
    const started = this.now();
    const view = new DataView(this.memory.buffer);
    const html = readString(view, executed.physicalResult,
      this.decoder, "formatHtmlForRuntime result");
    const decodeMs = elapsed(this.now, started);
    executed.state = "decoded";
    const timings = { ...executed.timings, decodeMs };
    timings.totalMs = timings.prepareMs + timings.executeMs + timings.decodeMs;
    return {
      html,
      timings,
      memory: {
        ...executed.memory,
        frontierAfterDecode: this.synchronizeFrontier(),
        pagesAfterDecode: this.memory.buffer.byteLength / PAGE_BYTES,
      },
    };
  }
}

`;

replaceExactly(
  "/**\n * Instantiate the production adapter from transport-neutral inputs.\n */",
  htmlSupport + "/**\n * Instantiate the production adapter from transport-neutral inputs.\n */",
  "adapter factory boundary",
);
replaceExactly(
  "  return new PrettyMAdapter({",
  "  return new PrettyMHtmlAdapter({",
  "adapter construction",
);
source = source.replaceAll("PrettyTrace object result", "HTML String object result");
source = source.replaceAll("styled trace", "escaped HTML String");
source = source.replaceAll("production prettyM module", "production HTML prettyM module");

mkdirSync(dirname(outputPath), { recursive: true });
writeFileSync(outputPath, source);
console.log(`wrote ${Buffer.byteLength(source)} bytes to ${outputPath}`);
