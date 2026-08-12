import { loadEmscriptenModule } from "./emscripten-loader.mjs";
import {
  PrettyFormat,
  PrettyMWireInternals as Wire,
} from "./prettyM-emscripten-adapter.mjs";

export { PrettyFormat };
export const PRETTY_M_BROWSER_API_VERSION =
  "fir.prettyM.html.emscripten.browser/v1";
export const PRETTY_M_INPUT_LAYOUT_VERSION =
  "lean-4.32-Std.Format.compact/v1";
export const PRETTY_M_EMSCRIPTEN_WIRE_VERSION =
  "fir.prettyM.html.emscripten-wire/v1";
export const PRETTY_M_OUTPUT_VERSION = "verso-token-html/v1";

const DEFAULT_MAXIMUM_NODES = 1_000_000;
const DEFAULT_MAXIMUM_BYTES = 64 * 1024 * 1024;
const REQUIRED_EXPORTS = Object.freeze([
  "fir_lcnf_c_pretty_html_input_alloc",
  "fir_lcnf_c_pretty_html_render",
  "fir_lcnf_c_pretty_html_result_ptr",
  "fir_lcnf_c_pretty_html_result_len",
  "fir_lcnf_c_pretty_html_release",
]);

function fail(message) {
  throw new Error(`FIR Emscripten prettyM HTML adapter: ${message}`);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function defaultNow() {
  if (
    globalThis.performance &&
    typeof globalThis.performance.now === "function"
  ) {
    return globalThis.performance.now();
  }
  return Date.now();
}

function elapsed(now, started) {
  const result = now() - started;
  return Number.isFinite(result) && result >= 0 ? result : 0;
}

function ownKeys(value, required, optional = []) {
  const allowed = new Set([...required, ...optional]);
  for (const key of required) {
    requireCondition(Object.hasOwn(value, key), `request is missing ${key}`);
  }
  for (const key of Object.keys(value)) {
    requireCondition(allowed.has(key), `request has unknown property ${key}`);
  }
}

function normalizeAnnotations(value) {
  requireCondition(Array.isArray(value), "annotations must be an array");
  requireCondition(
    value.length <= DEFAULT_MAXIMUM_NODES,
    `annotations exceed ${DEFAULT_MAXIMUM_NODES} entries`,
  );
  const seen = new Set();
  return value.map((entry, index) => {
    requireCondition(
      entry !== null && typeof entry === "object" && !Array.isArray(entry),
      `annotations[${index}] must be an object`,
    );
    ownKeys(entry, ["tag", "annotation"]);
    const tag = Wire.natural(entry.tag, `annotations[${index}].tag`);
    const key = tag.toString();
    requireCondition(!seen.has(key), `duplicate annotation tag ${key}`);
    seen.add(key);
    const annotation = entry.annotation;
    requireCondition(
      annotation !== null &&
        typeof annotation === "object" &&
        !Array.isArray(annotation),
      `annotations[${index}].annotation must be an object`,
    );
    ownKeys(annotation, ["cssClass"], ["binding"]);
    requireCondition(
      typeof annotation.cssClass === "string",
      `annotations[${index}].cssClass must be a string`,
    );
    const binding = annotation.binding ?? null;
    requireCondition(
      binding === null || typeof binding === "string",
      `annotations[${index}].binding must be a string or null`,
    );
    return { tag, cssClass: annotation.cssClass, binding };
  });
}

function encodeRequest(request, maximumNodes, maximumBytes, encoder) {
  requireCondition(
    request !== null && typeof request === "object" && !Array.isArray(request),
    "render request must be an object",
  );
  ownKeys(
    request,
    ["format", "annotations", "width"],
    ["indent", "column"],
  );
  const writer = new Wire.ByteWriter(maximumBytes);
  writer.bytes(Uint8Array.of(0x46, 0x50, 0x48, 0x31));
  Wire.writeNatural(writer, Wire.natural(request.width, "width"));
  Wire.writeNatural(writer, Wire.natural(request.indent ?? 0, "indent"));
  Wire.writeNatural(writer, Wire.natural(request.column ?? 0, "column"));
  const formatNodes = Wire.writeFormat(
    writer,
    encoder,
    request.format,
    maximumNodes,
  );
  const annotations = normalizeAnnotations(request.annotations);
  writer.u32(annotations.length);
  for (const annotation of annotations) {
    Wire.writeNatural(writer, annotation.tag);
    Wire.writeString(writer, encoder, annotation.cssClass);
    writer.u8(annotation.binding === null ? 0 : 1);
    if (annotation.binding !== null) {
      Wire.writeString(writer, encoder, annotation.binding);
    }
  }
  return {
    bytes: writer.finish(),
    formatNodes,
    annotationEntries: annotations.length,
  };
}

class ByteReader {
  constructor(bytes, decoder) {
    this.bytes = bytes;
    this.decoder = decoder;
    this.position = 0;
  }

  require(count, label) {
    requireCondition(
      this.position + count <= this.bytes.length,
      `${label} exceeds the wire response`,
    );
  }

  u8(label) {
    this.require(1, label);
    return this.bytes[this.position++];
  }

  u32(label) {
    this.require(4, label);
    const position = this.position;
    this.position += 4;
    return (
      this.bytes[position] +
      this.bytes[position + 1] * 0x100 +
      this.bytes[position + 2] * 0x10000 +
      this.bytes[position + 3] * 0x1000000
    );
  }

  expect(value, label) {
    requireCondition(this.u8(label) === value, `invalid ${label}`);
  }

  string(label) {
    const length = this.u32(`${label} length`);
    this.require(length, label);
    const start = this.position;
    this.position += length;
    try {
      return this.decoder.decode(this.bytes.subarray(start, this.position));
    } catch (error) {
      fail(`${label} is not valid UTF-8: ${error}`);
    }
  }

  done() {
    requireCondition(
      this.position === this.bytes.length,
      "wire response has trailing bytes",
    );
  }
}

function decodeResponse(bytes, decoder) {
  const reader = new ByteReader(bytes, decoder);
  reader.expect(0x46, "magic");
  reader.expect(0x48, "magic");
  reader.expect(0x52, "magic");
  reader.expect(0x31, "version");
  const status = reader.u8("status");
  if (status === 1) {
    const message = reader.string("error");
    reader.done();
    fail(`Lean prettyM HTML rejected the request: ${message}`);
  }
  requireCondition(status === 0, `wire response status ${status} is invalid`);
  const html = reader.string("HTML");
  reader.done();
  return html;
}

function validateManifest(manifest) {
  requireCondition(
    manifest?.profile === "emscripten",
    "manifest is not an Emscripten artifact",
  );
  const exports = new Set(manifest.abi?.exports);
  for (const symbol of REQUIRED_EXPORTS) {
    requireCondition(exports.has(symbol), `manifest does not declare ${symbol}`);
  }
  requireCondition(
    manifest.abi?.runtimeMethods?.includes("HEAPU8"),
    "manifest does not declare the HEAPU8 bulk-transfer view",
  );
}

export class EmscriptenPrettyMHtmlAdapter {
  constructor(
    loaded,
    {
      maximumNodes = DEFAULT_MAXIMUM_NODES,
      maximumBytes = DEFAULT_MAXIMUM_BYTES,
      now = defaultNow,
    } = {},
  ) {
    requireCondition(
      Number.isSafeInteger(maximumNodes) && maximumNodes > 0,
      "maximumNodes must be a positive safe integer",
    );
    requireCondition(
      Number.isSafeInteger(maximumBytes) &&
        maximumBytes > 0 &&
        maximumBytes <= DEFAULT_MAXIMUM_BYTES,
      `maximumBytes must be between 1 and ${DEFAULT_MAXIMUM_BYTES}`,
    );
    validateManifest(loaded.manifest);
    requireCondition(
      loaded.module.HEAPU8 instanceof Uint8Array,
      "Emscripten module does not expose HEAPU8",
    );
    this.loaded = loaded;
    this.module = loaded.module;
    this.exports = loaded.exports;
    this.maximumNodes = maximumNodes;
    this.maximumBytes = maximumBytes;
    this.now = now;
    this.encoder = new TextEncoder();
    this.decoder = new TextDecoder("utf-8", { fatal: true });
    this.disposed = false;
    this.rendering = false;
  }

  render(request) {
    requireCondition(!this.disposed, "adapter has been disposed");
    requireCondition(!this.rendering, "render is not reentrant");
    this.rendering = true;
    try {
      const encodeStarted = this.now();
      const encoded = encodeRequest(
        request,
        this.maximumNodes,
        this.maximumBytes,
        this.encoder,
      );
      const encodeMs = elapsed(this.now, encodeStarted);
      const heapBytesBefore = this.module.HEAPU8.byteLength;
      const inputPointer =
        this.exports.fir_lcnf_c_pretty_html_input_alloc(
          encoded.bytes.length,
        ) >>> 0;
      requireCondition(inputPointer !== 0, "could not allocate wire request");
      this.module.HEAPU8.set(encoded.bytes, inputPointer);

      const executeStarted = this.now();
      const executionStatus =
        this.exports.fir_lcnf_c_pretty_html_render(encoded.bytes.length) >>> 0;
      const executeMs = elapsed(this.now, executeStarted);
      requireCondition(
        executionStatus === 0,
        `C bridge failed with status ${executionStatus}`,
      );
      const resultPointer =
        this.exports.fir_lcnf_c_pretty_html_result_ptr() >>> 0;
      const resultLength =
        this.exports.fir_lcnf_c_pretty_html_result_len() >>> 0;
      requireCondition(
        resultLength <= this.module.HEAPU8.byteLength &&
          resultPointer <= this.module.HEAPU8.byteLength - resultLength,
        "C bridge returned an out-of-bounds result",
      );
      const response = this.module.HEAPU8.slice(
        resultPointer,
        resultPointer + resultLength,
      );
      const decodeStarted = this.now();
      const html = decodeResponse(response, this.decoder);
      const decodeMs = elapsed(this.now, decodeStarted);
      return {
        html,
        timings: {
          encodeMs,
          executeMs,
          decodeMs,
          totalMs: encodeMs + executeMs + decodeMs,
        },
        memory: {
          requestBytes: encoded.bytes.length,
          responseBytes: response.length,
          formatNodes: encoded.formatNodes,
          annotationEntries: encoded.annotationEntries,
          heapBytesBefore,
          heapBytesAfter: this.module.HEAPU8.byteLength,
        },
      };
    } finally {
      this.rendering = false;
    }
  }

  dispose() {
    if (!this.disposed) {
      this.exports.fir_lcnf_c_pretty_html_release();
      this.disposed = true;
    }
  }
}

export async function loadEmscriptenPrettyMHtmlAdapter(
  manifestSource,
  options = {},
) {
  const loaded = await loadEmscriptenModule(manifestSource, options.loader);
  return new EmscriptenPrettyMHtmlAdapter(loaded, options);
}
