/**
 * Browser-safe adapter for the packaged Lean 4.32 `Std.Format.prettyM` facade.
 *
 * The public input is a compact discriminated union. The adapter validates and
 * measures it, performs one bulk allocation through the module's resident
 * allocator, writes the actual Lean runtime representation into module-owned
 * memory, transfers that representation to `prettyM`, and decodes the returned
 * styled trace into JavaScript values.
 */

export const PRETTY_M_BROWSER_API_VERSION = "fir.prettyM.browser/v1";
export const PRETTY_M_INPUT_LAYOUT_VERSION =
  "lean-4.32-Std.Format.compact/v1";
export const PRETTY_M_OWNERSHIP_VERSION =
  "fir.prettyM.module-owned-transfer/v1";

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const MAX_IMMEDIATE_PAYLOAD = 0x7fffffffn;
const MAX_TAGGED_PAYLOAD = 0x7fffffffffffffffn;
const MIN_SIGNED_32 = -0x80000000n;
const MAX_SIGNED_32 = 0x7fffffffn;
const MAX_UINT32 = 0xffffffff;
const STRING_UTF8_MARKER = 1;
const INTEGER_SIGN_MAGNITUDE_MARKER = 1;
const LIVE_FLAGS = 2;
const PERSISTENT_LIVE_FLAGS = 3;

const KIND = Object.freeze({
  constructor: 1,
  string: 4,
  natural: 5,
  integer: 6,
});

const PREPARED = Symbol("fir.prettyM.prepared");
const EXECUTED = Symbol("fir.prettyM.executed");

function fail(message) {
  throw new Error(`FIR prettyM browser adapter: ${message}`);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function align8(bytes) {
  return Math.ceil(bytes / 8) * 8;
}

function u32(value) {
  return Number(value) >>> 0;
}

function i32(value) {
  return Number(value) | 0;
}

function defaultNow() {
  if (globalThis.performance &&
      typeof globalThis.performance.now === "function") {
    return globalThis.performance.now();
  }
  return Date.now();
}

function elapsed(now, started) {
  const result = now() - started;
  return Number.isFinite(result) && result >= 0 ? result : 0;
}

const FORMAT_KEYS = Object.freeze({
  nil: { required: ["kind"], allowed: new Set(["kind"]) },
  line: { required: ["kind"], allowed: new Set(["kind"]) },
  align: {
    required: ["kind", "force"],
    allowed: new Set(["kind", "force"]),
  },
  text: {
    required: ["kind", "text"],
    allowed: new Set(["kind", "text"]),
  },
  nest: {
    required: ["kind", "indent", "body"],
    allowed: new Set(["kind", "indent", "body"]),
  },
  append: {
    required: ["kind", "left", "right"],
    allowed: new Set(["kind", "left", "right"]),
  },
  group: {
    required: ["kind", "body"],
    allowed: new Set(["kind", "body", "behavior"]),
  },
  tag: {
    required: ["kind", "tag", "body"],
    allowed: new Set(["kind", "tag", "body"]),
  },
});

function ownKeys(value, spec) {
  for (const key of spec.required) {
    requireCondition(Object.hasOwn(value, key),
      `Format.${value.kind ?? "?"} is missing property ${key}`);
  }
  for (const key of Object.keys(value)) {
    requireCondition(spec.allowed.has(key),
      `Format.${value.kind ?? "?"} has unknown property ${key}`);
  }
}

function utf8Length(value) {
  let bytes = 0;
  for (let index = 0; index < value.length; index += 1) {
    const code = value.charCodeAt(index);
    if (code <= 0x7f) {
      bytes += 1;
    } else if (code <= 0x7ff) {
      bytes += 2;
    } else if (code >= 0xd800 && code <= 0xdbff &&
        index + 1 < value.length) {
      const next = value.charCodeAt(index + 1);
      if (next >= 0xdc00 && next <= 0xdfff) {
        bytes += 4;
        index += 1;
      } else {
        bytes += 3;
      }
    } else {
      bytes += 3;
    }
  }
  return bytes;
}

function natural(value, label) {
  let result;
  if (typeof value === "bigint") {
    result = value;
  } else if (typeof value === "number") {
    requireCondition(Number.isSafeInteger(value),
      `${label} number must be a safe integer`);
    result = BigInt(value);
  } else if (typeof value === "string") {
    requireCondition(/^(0|[1-9][0-9]*)$/.test(value),
      `${label} string must be a canonical unsigned decimal integer`);
    result = BigInt(value);
  } else {
    fail(`${label} must be a bigint, safe integer, or canonical decimal string`);
  }
  requireCondition(result >= 0n, `${label} must be nonnegative`);
  return result;
}

function integer(value, label) {
  let result;
  if (typeof value === "bigint") {
    result = value;
  } else if (typeof value === "number") {
    requireCondition(Number.isSafeInteger(value),
      `${label} number must be a safe integer`);
    result = BigInt(value);
  } else if (typeof value === "string") {
    requireCondition(/^(0|-?[1-9][0-9]*)$/.test(value),
      `${label} string must be a canonical signed decimal integer`);
    result = BigInt(value);
  } else {
    fail(`${label} must be a bigint, safe integer, or canonical decimal string`);
  }
  return result;
}

function limbs(value) {
  const result = [];
  let remaining = value;
  do {
    result.push(BigInt.asUintN(64, remaining));
    remaining >>= 64n;
  } while (remaining !== 0n);
  return result;
}

function immediateWord(payload) {
  requireCondition(payload >= 0n && payload <= MAX_IMMEDIATE_PAYLOAD,
    `immediate payload ${payload} does not fit wasm32`);
  return Number(payload * 2n + 1n) >>> 0;
}

function naturalPlan(value) {
  if (value <= MAX_IMMEDIATE_PAYLOAD) {
    return { representation: "immediate", value, bytes: 0 };
  }
  if (value <= MAX_TAGGED_PAYLOAD) {
    return { representation: "tagged-box", value, bytes: 40 };
  }
  const magnitude = limbs(value);
  return {
    representation: "natural",
    value,
    limbs: magnitude,
    bytes: align8(HEADER_BYTES + SLOT_BYTES * magnitude.length),
  };
}

function integerPlan(value) {
  if (value >= MIN_SIGNED_32 && value <= MAX_SIGNED_32) {
    const payload = BigInt.asUintN(32, value);
    if (payload <= MAX_IMMEDIATE_PAYLOAD) {
      return { representation: "immediate", value: payload, bytes: 0 };
    }
    return { representation: "tagged-box", value: payload, bytes: 40 };
  }
  const negative = value < 0n;
  const magnitude = limbs(negative ? -value : value);
  return {
    representation: "integer",
    value,
    negative,
    limbs: magnitude,
    bytes: align8(HEADER_BYTES + SLOT_BYTES * magnitude.length),
  };
}

function checkedTotal(current, extra, label) {
  const result = current + extra;
  requireCondition(Number.isSafeInteger(result) &&
    result >= 0 && result <= MAX_UINT32,
  `${label} exceeds the wasm32 address space`);
  return result;
}

function normalizeBehavior(value) {
  if (value === undefined || value === "allOrNone" || value === 0) return 0;
  if (value === "fill" || value === 1) return 1;
  fail("Format.group behavior must be allOrNone, fill, 0, or 1");
}

function normalizeFormat(root, maximumNodes) {
  const holder = {};
  const active = new WeakSet();
  const nodes = [];
  let totalBytes = 0;
  const stack = [{ phase: "enter", value: root, parent: holder, key: "root" }];

  while (stack.length !== 0) {
    const frame = stack.pop();
    if (frame.phase === "exit") {
      active.delete(frame.value);
      continue;
    }

    const value = frame.value;
    requireCondition(value !== null && typeof value === "object" &&
      !Array.isArray(value),
    "Format node must be an object");
    requireCondition(!active.has(value), "Format input contains a cycle");
    active.add(value);
    requireCondition(typeof value.kind === "string",
      "Format node kind must be a string");
    requireCondition(nodes.length < maximumNodes,
      `Format input exceeds ${maximumNodes} nodes`);

    let node;
    switch (value.kind) {
      case "nil":
      case "line":
        ownKeys(value, FORMAT_KEYS[value.kind]);
        node = { kind: value.kind, bytes: 0 };
        break;
      case "align":
        ownKeys(value, FORMAT_KEYS.align);
        requireCondition(typeof value.force === "boolean",
          "Format.align force must be boolean");
        node = { kind: "align", force: value.force, bytes: 40 };
        totalBytes = checkedTotal(totalBytes, node.bytes, "Format input");
        break;
      case "text": {
        ownKeys(value, FORMAT_KEYS.text);
        requireCondition(typeof value.text === "string",
          "Format.text text must be a string");
        const textBytes = utf8Length(value.text);
        const stringBytes = align8(HEADER_BYTES + textBytes);
        node = {
          kind: "text",
          text: value.text,
          textBytes,
          bytes: 40,
          stringBytes,
        };
        totalBytes = checkedTotal(totalBytes,
          node.bytes + stringBytes, "Format input");
        break;
      }
      case "nest": {
        ownKeys(value, FORMAT_KEYS.nest);
        const indentPlan = integerPlan(integer(value.indent,
          "Format.nest indent"));
        node = {
          kind: "nest",
          indent: indentPlan,
          body: undefined,
          bytes: 48,
        };
        totalBytes = checkedTotal(totalBytes,
          node.bytes + indentPlan.bytes, "Format input");
        break;
      }
      case "append":
        ownKeys(value, FORMAT_KEYS.append);
        node = {
          kind: "append",
          left: undefined,
          right: undefined,
          bytes: 48,
        };
        totalBytes = checkedTotal(totalBytes, node.bytes, "Format input");
        break;
      case "group":
        ownKeys(value, FORMAT_KEYS.group);
        node = {
          kind: "group",
          behavior: normalizeBehavior(value.behavior),
          body: undefined,
          bytes: 48,
        };
        totalBytes = checkedTotal(totalBytes, node.bytes, "Format input");
        break;
      case "tag": {
        ownKeys(value, FORMAT_KEYS.tag);
        const tagPlan = naturalPlan(natural(value.tag, "Format.tag tag"));
        node = {
          kind: "tag",
          tag: tagPlan,
          body: undefined,
          bytes: 48,
        };
        totalBytes = checkedTotal(totalBytes,
          node.bytes + tagPlan.bytes, "Format input");
        break;
      }
      default:
        fail(`unknown Format kind ${value.kind}`);
    }

    frame.parent[frame.key] = node;
    nodes.push(node);
    stack.push({ phase: "exit", value });
    switch (value.kind) {
      case "nest":
      case "group":
      case "tag":
        stack.push({
          phase: "enter",
          value: value.body,
          parent: node,
          key: "body",
        });
        break;
      case "append":
        stack.push({
          phase: "enter",
          value: value.right,
          parent: node,
          key: "right",
        });
        stack.push({
          phase: "enter",
          value: value.left,
          parent: node,
          key: "left",
        });
        break;
      default:
        break;
    }
  }

  return { root: holder.root, nodes, totalBytes };
}

function requiredFunction(exports, name) {
  const result = exports[name];
  requireCondition(typeof result === "function",
    `module is missing function export ${name}`);
  return result;
}

function requiredMemory(exports) {
  requireCondition(exports.memory instanceof WebAssembly.Memory,
    "module is missing its exported memory");
  return exports.memory;
}

function writeHeader(view, address, {
  kind,
  flags = LIVE_FLAGS,
  rc = 1,
  bytes,
  aux0 = 0,
  aux1 = 0,
  aux2 = 0,
  aux3 = 0,
}) {
  view.setUint32(address, u32(kind), true);
  view.setUint32(address + 4, u32(flags), true);
  view.setUint32(address + 8, u32(rc), true);
  view.setUint32(address + 12, u32(bytes), true);
  view.setUint32(address + 16, u32(aux0), true);
  view.setUint32(address + 20, u32(aux1), true);
  view.setUint32(address + 24, u32(aux2), true);
  view.setUint32(address + 28, u32(aux3), true);
}

function writeWord(view, address, word) {
  view.setUint32(address, u32(word), true);
  view.setUint32(address + 4, 0, true);
}

function readU32(view, address, label) {
  requireCondition(Number.isInteger(address) && address >= 0 &&
    address + 4 <= view.byteLength,
  `${label} read is outside module memory`);
  return view.getUint32(address, true);
}

function classify(word) {
  const value = u32(word);
  if (value === 0) return "sentinel";
  if (value % 2 === 1) return "immediate";
  if (value % 8 === 0) return "heap";
  return "invalid";
}

function readHeader(view, word, label) {
  const address = u32(word);
  requireCondition(classify(address) === "heap",
    `${label} has invalid address ${address}`);
  const flags = readU32(view, address + 4, label);
  const result = {
    address,
    kind: readU32(view, address, label),
    persistent: (flags & 1) !== 0,
    live: (flags & 2) !== 0,
    rc: readU32(view, address + 8, label),
    bytes: readU32(view, address + 12, label),
    aux0: readU32(view, address + 16, label),
    aux1: readU32(view, address + 20, label),
    aux2: readU32(view, address + 24, label),
    aux3: readU32(view, address + 28, label),
  };
  requireCondition(result.live, `${label} is not live`);
  requireCondition(result.bytes >= HEADER_BYTES && result.bytes % 8 === 0 &&
    address + result.bytes <= view.byteLength,
  `${label} has a malformed allocation extent`);
  return result;
}

function readWord(view, address, label) {
  const result = readU32(view, address, label);
  requireCondition(readU32(view, address + 4, label) === 0,
    `${label} has nonzero word padding`);
  return result;
}

function readConstructor(view, word, tag, fields, label) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.constructor,
    `${label} is not a constructor`);
  requireCondition(header.aux0 === tag,
    `${label} has constructor tag ${header.aux0}, expected ${tag}`);
  requireCondition(header.aux1 === fields &&
    header.aux2 === 0 && header.aux3 === 0,
  `${label} has an unexpected constructor layout`);
  return Array.from({ length: fields }, (_, index) =>
    readWord(view, header.address + HEADER_BYTES + SLOT_BYTES * index,
      `${label} field ${index}`));
}

function readNatural(view, word, label) {
  const physical = u32(word);
  if (classify(physical) === "immediate") {
    return BigInt(physical >>> 1);
  }
  const header = readHeader(view, physical, label);
  requireCondition(header.kind === KIND.natural,
    `${label} is not a Natural`);
  if (header.persistent && header.aux0 === 1) {
    requireCondition(header.aux1 === 1 && header.bytes === 40,
      `${label} has a malformed tagged Natural`);
    return view.getBigUint64(header.address + HEADER_BYTES, true);
  }
  requireCondition(!header.persistent && header.aux0 === 2 &&
    header.aux1 > 0 &&
    header.bytes === align8(HEADER_BYTES + SLOT_BYTES * header.aux1),
  `${label} has a malformed multi-limb Natural`);
  let result = 0n;
  for (let index = header.aux1 - 1; index >= 0; --index) {
    result = (result << 64n) +
      view.getBigUint64(header.address + HEADER_BYTES + SLOT_BYTES * index, true);
  }
  return result;
}

function readString(view, word, decoder, label) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.string &&
    header.aux0 === STRING_UTF8_MARKER &&
    header.aux2 === 0 && header.aux3 === 0,
  `${label} is not a canonical UTF-8 String`);
  requireCondition(HEADER_BYTES + header.aux1 <= header.bytes,
    `${label} payload exceeds its allocation`);
  return decoder.decode(new Uint8Array(
    view.buffer, header.address + HEADER_BYTES, header.aux1));
}

function encodeNumberPlan(plan, allocate, view) {
  if (plan.representation === "immediate") {
    return immediateWord(plan.value);
  }
  const address = allocate(plan.bytes);
  if (plan.representation === "tagged-box") {
    writeHeader(view, address, {
      kind: KIND.natural,
      flags: PERSISTENT_LIVE_FLAGS,
      rc: 0,
      bytes: plan.bytes,
      aux0: 1,
      aux1: 1,
    });
    view.setBigUint64(address + HEADER_BYTES,
      BigInt.asUintN(64, plan.value), true);
    return address;
  }
  if (plan.representation === "natural") {
    writeHeader(view, address, {
      kind: KIND.natural,
      bytes: plan.bytes,
      aux0: 2,
      aux1: plan.limbs.length,
    });
  } else if (plan.representation === "integer") {
    writeHeader(view, address, {
      kind: KIND.integer,
      bytes: plan.bytes,
      aux0: INTEGER_SIGN_MAGNITUDE_MARKER,
      aux1: plan.limbs.length,
      aux2: plan.negative ? 1 : 0,
    });
  } else {
    fail(`unknown numeric representation ${plan.representation}`);
  }
  for (let index = 0; index < plan.limbs.length; index += 1) {
    view.setBigUint64(address + HEADER_BYTES + SLOT_BYTES * index,
      plan.limbs[index], true);
  }
  return address;
}

function validateBuild(build, manifest) {
  requireCondition(build && typeof build === "object" && !Array.isArray(build),
    "BUILD.json must contain an object");
  requireCondition(build.entry === manifest.entry,
    "BUILD.json and module descriptor entry names disagree");
  const capability = build.capabilities?.browserAdapter;
  requireCondition(capability?.apiVersion === PRETTY_M_BROWSER_API_VERSION,
    `BUILD.json does not declare ${PRETTY_M_BROWSER_API_VERSION}`);
  requireCondition(build.capabilities?.inputLayout?.version ===
    PRETTY_M_INPUT_LAYOUT_VERSION,
  `BUILD.json does not declare ${PRETTY_M_INPUT_LAYOUT_VERSION}`);
  requireCondition(build.capabilities?.ownership?.version ===
    PRETTY_M_OWNERSHIP_VERSION,
  `BUILD.json does not declare ${PRETTY_M_OWNERSHIP_VERSION}`);
}

function validateManifest(manifest) {
  requireCondition(manifest && typeof manifest === "object" &&
    !Array.isArray(manifest), "module descriptor must contain an object");
  requireCondition(typeof manifest.entry === "string" &&
    manifest.entry.length !== 0, "module descriptor entry must be nonempty");
  requireCondition(Array.isArray(manifest.params) &&
    manifest.params.length === 4 &&
    manifest.params.every((kind) => kind === "tobject"),
  "module descriptor must expose Format × Nat × Nat × Nat");
  requireCondition(manifest.result === "object",
    "module descriptor must expose a PrettyTrace object result");
  requireCondition(Array.isArray(manifest.imports) &&
    manifest.imports.length === 0,
  "production prettyM adapter requires a zero-import descriptor");
}

/**
 * Helpers for constructing the documented compact input type.
 *
 * Consumers may use these helpers or create equivalent plain objects.
 */
export const PrettyFormat = Object.freeze({
  nil: () => ({ kind: "nil" }),
  line: () => ({ kind: "line" }),
  align: (force = false) => ({ kind: "align", force }),
  text: (text) => ({ kind: "text", text }),
  nest: (indent, body) => ({ kind: "nest", indent, body }),
  append: (left, right) => ({ kind: "append", left, right }),
  group: (body, behavior = "allOrNone") =>
    ({ kind: "group", body, behavior }),
  tag: (tag, body) => ({ kind: "tag", tag, body }),
});

export class PrettyMAdapter {
  constructor({ instance, manifest, build, startupTimings, now, maximumNodes }) {
    this.instance = instance;
    this.manifest = manifest;
    this.build = build;
    this.startupTimings = Object.freeze({ ...startupTimings });
    this.now = now;
    this.maximumNodes = maximumNodes;
    this.encoder = new TextEncoder();
    this.decoder = new TextDecoder("utf-8", { fatal: true });
    this.memory = requiredMemory(instance.exports);
    this.frontier = requiredFunction(instance.exports, "fir_heap_frontier");
    this.setFrontier =
      requiredFunction(instance.exports, "fir_heap_set_frontier");
    this.allocate = requiredFunction(instance.exports, "fir_heap_alloc");
    this.entry = requiredFunction(instance.exports, manifest.entry);
    this.lastFrontier = this.synchronizeFrontier();
  }

  synchronizeFrontier() {
    const resident = u32(this.frontier());
    requireCondition(resident >= HEAP_BASE && resident % 8 === 0,
      `resident frontier ${resident} is invalid`);
    if (this.lastFrontier !== undefined) {
      requireCondition(resident >= this.lastFrontier,
        `resident frontier rewound from ${this.lastFrontier} to ${resident}`);
    }
    this.setFrontier(resident);
    this.lastFrontier = resident;
    return resident;
  }

  prepare({
    format,
    width,
    indent = 0,
    column = 0,
  }) {
    const prepareStarted = this.now();
    const normalizeStarted = this.now();
    const normalized = normalizeFormat(format, this.maximumNodes);
    const widthPlan = naturalPlan(natural(width, "width"));
    const indentPlan = naturalPlan(natural(indent, "indent"));
    const columnPlan = naturalPlan(natural(column, "column"));
    let totalBytes = normalized.totalBytes;
    for (const plan of [widthPlan, indentPlan, columnPlan]) {
      totalBytes = checkedTotal(totalBytes, plan.bytes, "prettyM input");
    }
    const normalizeMs = elapsed(this.now, normalizeStarted);

    const frontierBefore = this.synchronizeFrontier();
    const pagesBefore = this.memory.buffer.byteLength / PAGE_BYTES;
    const allocateStarted = this.now();
    const block = totalBytes === 0 ? frontierBefore :
      u32(this.allocate(totalBytes));
    const allocateMs = elapsed(this.now, allocateStarted);
    requireCondition(block === frontierBefore,
      `resident allocator returned ${block}, expected frontier ${frontierBefore}`);
    const frontierAfterAllocation = this.synchronizeFrontier();
    requireCondition(frontierAfterAllocation === frontierBefore + totalBytes,
      "resident allocator advanced by the wrong bulk input size");

    const encodeStarted = this.now();
    const view = new DataView(this.memory.buffer);
    let cursor = block;
    let rawObjects = 0;
    const take = (bytes) => {
      requireCondition(bytes >= HEADER_BYTES && bytes % 8 === 0,
        `raw suballocation size ${bytes} is invalid`);
      const result = cursor;
      cursor += bytes;
      requireCondition(cursor <= block + totalBytes,
        "raw input encoder exceeded its bulk allocation");
      rawObjects += 1;
      return result;
    };

    for (const node of normalized.nodes) {
      if (node.kind === "nil") {
        node.word = immediateWord(0n);
      } else if (node.kind === "line") {
        node.word = immediateWord(1n);
      } else {
        node.word = take(node.bytes);
        if (node.kind === "text") {
          node.textWord = take(node.stringBytes);
          writeHeader(view, node.textWord, {
            kind: KIND.string,
            bytes: node.stringBytes,
            aux0: STRING_UTF8_MARKER,
            aux1: node.textBytes,
          });
          const payload = new Uint8Array(
            this.memory.buffer,
            node.textWord + HEADER_BYTES,
            node.stringBytes - HEADER_BYTES,
          );
          const encoded = this.encoder.encodeInto(node.text, payload);
          requireCondition(encoded.read === node.text.length &&
            encoded.written === node.textBytes,
          "TextEncoder did not encode the complete Format.text payload");
          payload.fill(0, encoded.written);
        } else if (node.kind === "nest") {
          node.indentWord = encodeNumberPlan(node.indent, take, view);
        } else if (node.kind === "tag") {
          node.tagWord = encodeNumberPlan(node.tag, take, view);
        }
      }
    }

    for (const node of normalized.nodes) {
      switch (node.kind) {
        case "nil":
        case "line":
          break;
        case "align":
          writeHeader(view, node.word, {
            kind: KIND.constructor,
            bytes: node.bytes,
            aux0: 2,
            aux3: 1,
          });
          view.setUint32(
            node.word + HEADER_BYTES, node.force ? 1 : 0, true);
          view.setUint32(node.word + HEADER_BYTES + 4, 0, true);
          break;
        case "text":
          writeHeader(view, node.word, {
            kind: KIND.constructor,
            bytes: node.bytes,
            aux0: 3,
            aux1: 1,
          });
          writeWord(view, node.word + HEADER_BYTES, node.textWord);
          break;
        case "nest":
          writeHeader(view, node.word, {
            kind: KIND.constructor,
            bytes: node.bytes,
            aux0: 4,
            aux1: 2,
          });
          writeWord(view, node.word + HEADER_BYTES, node.indentWord);
          writeWord(view, node.word + HEADER_BYTES + SLOT_BYTES, node.body.word);
          break;
        case "append":
          writeHeader(view, node.word, {
            kind: KIND.constructor,
            bytes: node.bytes,
            aux0: 5,
            aux1: 2,
          });
          writeWord(view, node.word + HEADER_BYTES, node.left.word);
          writeWord(view, node.word + HEADER_BYTES + SLOT_BYTES, node.right.word);
          break;
        case "group":
          writeHeader(view, node.word, {
            kind: KIND.constructor,
            bytes: node.bytes,
            aux0: 6,
            aux1: 1,
            aux3: 1,
          });
          writeWord(view, node.word + HEADER_BYTES, node.body.word);
          view.setUint32(
            node.word + HEADER_BYTES + SLOT_BYTES, node.behavior, true);
          view.setUint32(
            node.word + HEADER_BYTES + SLOT_BYTES + 4, 0, true);
          break;
        case "tag":
          writeHeader(view, node.word, {
            kind: KIND.constructor,
            bytes: node.bytes,
            aux0: 7,
            aux1: 2,
          });
          writeWord(view, node.word + HEADER_BYTES, node.tagWord);
          writeWord(view, node.word + HEADER_BYTES + SLOT_BYTES, node.body.word);
          break;
        default:
          fail(`raw encoder reached unknown Format kind ${node.kind}`);
      }
    }

    const widthWord = encodeNumberPlan(widthPlan, take, view);
    const indentWord = encodeNumberPlan(indentPlan, take, view);
    const columnWord = encodeNumberPlan(columnPlan, take, view);
    requireCondition(cursor === block + totalBytes,
      `raw input encoder used ${cursor - block} of ${totalBytes} bytes`);
    const encodeMs = elapsed(this.now, encodeStarted);
    const pagesAfterPrepare = this.memory.buffer.byteLength / PAGE_BYTES;

    return {
      [PREPARED]: this,
      state: "prepared",
      args: [
        i32(normalized.root.word),
        i32(widthWord),
        i32(indentWord),
        i32(columnWord),
      ],
      timings: {
        normalizeMs,
        allocateMs,
        encodeMs,
        prepareMs: elapsed(this.now, prepareStarted),
      },
      memory: {
        frontierBefore,
        frontierAfterPrepare: frontierAfterAllocation,
        pagesBefore,
        pagesAfterPrepare,
        inputBytes: totalBytes,
        residentAllocationCalls: totalBytes === 0 ? 0 : 1,
        rawObjects,
        formatNodes: normalized.nodes.length,
      },
    };
  }

  execute(prepared) {
    requireCondition(prepared?.[PREPARED] === this,
      "execute received a handle from another adapter");
    requireCondition(prepared.state === "prepared",
      "prepared handle has already been consumed");
    const frontierBeforeExecute = this.synchronizeFrontier();
    requireCondition(frontierBeforeExecute >=
      prepared.memory.frontierAfterPrepare,
    "resident frontier lost prepared input");
    const started = this.now();
    const physicalResult = u32(this.entry(...prepared.args));
    const executeMs = elapsed(this.now, started);
    const frontierAfterExecute = this.synchronizeFrontier();
    prepared.state = "executed";
    return {
      [EXECUTED]: this,
      state: "executed",
      physicalResult,
      timings: {
        ...prepared.timings,
        executeMs,
      },
      memory: {
        ...prepared.memory,
        frontierBeforeExecute,
        frontierAfterExecute,
        pagesAfterExecute: this.memory.buffer.byteLength / PAGE_BYTES,
      },
    };
  }

  decode(executed) {
    requireCondition(executed?.[EXECUTED] === this,
      "decode received a handle from another adapter");
    requireCondition(executed.state === "executed",
      "execution handle has already been decoded");
    const started = this.now();
    const view = new DataView(this.memory.buffer);
    const [textWord, eventsWord] = readConstructor(
      view, executed.physicalResult, 0, 2, "PrettyTrace");
    const text = readString(view, textWord, this.decoder, "PrettyTrace.text");
    const events = [];
    const seen = new Set();
    let list = eventsWord;
    while (classify(list) !== "immediate") {
      requireCondition(events.length < this.maximumNodes,
        `PrettyTrace exceeds ${this.maximumNodes} events`);
      requireCondition(!seen.has(list), "PrettyTrace event list contains a cycle");
      seen.add(list);
      const [eventWord, tail] =
        readConstructor(view, list, 1, 2, "PrettyTrace.eventsRev cons");
      const [kindWord, eventTextWord, valueWord] =
        readConstructor(view, eventWord, 0, 3, "PrettyTrace event");
      const kind = Number(readNatural(view, kindWord, "PrettyTrace event kind"));
      requireCondition(Number.isInteger(kind) && kind >= 0 && kind <= 3,
        `PrettyTrace event kind ${kind} is invalid`);
      const eventText =
        readString(view, eventTextWord, this.decoder, "PrettyTrace event text");
      const value = readNatural(view, valueWord, "PrettyTrace event value");
      requireCondition(kind !== 0 || value === 0n,
        "PrettyTrace output event has a numeric payload");
      requireCondition(kind === 0 || eventText === "",
        "PrettyTrace numeric event has a text payload");
      events.push({ kind, text: eventText, value });
      list = tail;
    }
    requireCondition((list >>> 1) === 0,
      "PrettyTrace event list has a non-nil immediate tail");
    events.reverse();
    const decodeMs = elapsed(this.now, started);
    executed.state = "decoded";
    const timings = {
      ...executed.timings,
      decodeMs,
    };
    timings.totalMs = timings.prepareMs + timings.executeMs + timings.decodeMs;
    return {
      trace: { text, events },
      timings,
      memory: {
        ...executed.memory,
        frontierAfterDecode: this.synchronizeFrontier(),
        pagesAfterDecode: this.memory.buffer.byteLength / PAGE_BYTES,
      },
    };
  }

  render(request) {
    return this.decode(this.execute(this.prepare(request)));
  }
}

/**
 * Instantiate the production adapter from transport-neutral inputs.
 */
export async function createPrettyMAdapter({
  bytes,
  manifest,
  build,
  now = defaultNow,
  maximumNodes = 1_000_000,
  startupTimings = {},
}) {
  requireCondition(bytes instanceof ArrayBuffer || ArrayBuffer.isView(bytes),
    "bytes must be an ArrayBuffer or an ArrayBuffer view");
  requireCondition(typeof now === "function", "now must be callable");
  requireCondition(Number.isSafeInteger(maximumNodes) && maximumNodes > 0,
    "maximumNodes must be a positive safe integer");
  validateManifest(manifest);
  validateBuild(build, manifest);

  const compileStarted = now();
  const module = await WebAssembly.compile(bytes);
  const compileMs = elapsed(now, compileStarted);
  requireCondition(WebAssembly.Module.imports(module).length === 0,
    "production prettyM module must have zero imports");
  const instantiateStarted = now();
  const instance = await WebAssembly.instantiate(module, {});
  const instantiateMs = elapsed(now, instantiateStarted);
  return new PrettyMAdapter({
    instance,
    manifest,
    build,
    now,
    maximumNodes,
    startupTimings: {
      fetchMs: startupTimings.fetchMs ?? 0,
      compileMs,
      instantiateMs,
      totalMs: (startupTimings.fetchMs ?? 0) + compileMs + instantiateMs,
    },
  });
}

function browserBaseUrl() {
  return globalThis.location?.href ?? "file:///";
}

/**
 * Fetch `prettyM.wasm`, its descriptor, and sibling `BUILD.json`, then create
 * the same adapter in a browser Window or Worker.
 */
export async function fetchPrettyMAdapter(artifactUrl, {
  fetchImpl = globalThis.fetch,
  descriptorUrl,
  buildUrl,
  now = defaultNow,
  maximumNodes = 1_000_000,
} = {}) {
  requireCondition(typeof fetchImpl === "function",
    "fetchPrettyMAdapter requires the Fetch API");
  const moduleUrl = new URL(artifactUrl, browserBaseUrl());
  const descriptor = descriptorUrl === undefined
    ? new URL(`${moduleUrl.href}.json`)
    : new URL(descriptorUrl, browserBaseUrl());
  const buildMetadata = buildUrl === undefined
    ? new URL("BUILD.json", moduleUrl)
    : new URL(buildUrl, browserBaseUrl());
  const started = now();
  const [moduleResponse, descriptorResponse, buildResponse] = await Promise.all([
    fetchImpl(moduleUrl),
    fetchImpl(descriptor),
    fetchImpl(buildMetadata),
  ]);
  requireCondition(moduleResponse.ok,
    `failed to fetch ${moduleUrl}: HTTP ${moduleResponse.status}`);
  requireCondition(descriptorResponse.ok,
    `failed to fetch ${descriptor}: HTTP ${descriptorResponse.status}`);
  requireCondition(buildResponse.ok,
    `failed to fetch ${buildMetadata}: HTTP ${buildResponse.status}`);
  const [bytes, manifest, build] = await Promise.all([
    moduleResponse.arrayBuffer(),
    descriptorResponse.json(),
    buildResponse.json(),
  ]);
  return createPrettyMAdapter({
    bytes,
    manifest,
    build,
    now,
    maximumNodes,
    startupTimings: { fetchMs: elapsed(now, started) },
  });
}
