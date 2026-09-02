/** Browser adapter for the FIR-native VBP Verso preview widget. */

export const VBP_VERSO_VIEWER_ADAPTER_API_VERSION =
  "fir.vbp-verso-viewer.browser/v1";
export const VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION =
  "lean-4.34-Lean.Vir.Infoview.RpcJson/v1";
export const VBP_VERSO_VIEWER_OWNERSHIP_VERSION =
  "fir.vbp-verso-viewer.instance-arena/v1";
export const LEAN_COMPONENT_RUNTIME_PROVIDER_API =
  "lean-vir/component-runtime-provider/v1";

export const VBP_VERSO_VIEWER_MOUNT_ENTRY =
  "VersoBlueprint.Experimental.VirPreview.Widget.mount";
export const VBP_VERSO_VIEWER_UNMOUNT_ENTRY =
  "VersoBlueprint.Experimental.VirPreview.Widget.unmount";
export const VBP_VERSO_VIEWER_RELEASE_OWNED_ENTRY = "fir_dec_once";

const BRIDGE = Object.freeze({
  component: "FirVbpVersoViewer.Bridge.invokeComponent",
  event: "FirVbpVersoViewer.Bridge.invokeEvent",
  state: "FirVbpVersoViewer.Bridge.invokeStringStateUpdate",
  effectSetup: "FirVbpVersoViewer.Bridge.invokeEffectSetup",
  effectCleanup: "FirVbpVersoViewer.Bridge.invokeEffectCleanup",
});

export const VBP_VERSO_VIEWER_BRIDGE_ENTRIES =
  Object.freeze(Object.values(BRIDGE));

const PAGE_BYTES = 65536;
const HEAP_BASE = 1024;
const HEADER_BYTES = 32;
const SLOT_BYTES = 8;
const LIVE_FLAGS = 2;
const STRING_MARKER = 1;
const INTEGER_MARKER = 1;
const ARRAY_MARKER = 0x41525259;
const HOST_RESOURCE_MARKER = 0x4a534852;
const FLOAT_BOX_MARKER = 7;
const MAX_IMMEDIATE = 0x7fffffffn;
const MAX_TAGGED = 0x7fffffffffffffffn;
const MIN_SIGNED_32 = -0x80000000n;
const MAX_SIGNED_32 = 0x7fffffffn;
const MAX_UINT32 = 0xffffffff;

const KIND = Object.freeze({
  constructor: 1,
  closure: 2,
  boxed: 3,
  string: 4,
  natural: 5,
  integer: 6,
  opaque: 8,
});

const HOST_IMPORTS = Object.freeze({
  "Lean.Vir.JsValue.ofString": "js.string",
  "Lean.Vir.React.Root.unmountSelectorJs": "react.root.unmountSelector",
  "Lean.Vir.JsValue.toBool": "js.bool.value",
  "Lean.Vir.React.Props.empty": "react.props.empty",
  "Lean.Vir.React.Props.setKeyJs": "react.props.setKey",
  "Lean.Vir.React.Props.setRef": "react.props.setRef",
  "Lean.Vir.React.Property.toJs": "js.value.react.property",
  "Lean.Vir.React.Props.setProperty": "react.props.setProperty",
  "Lean.Vir.React.EventHandler.toJs": "js.value.react.eventHandler",
  "Lean.Vir.React.Props.setEventHandler": "react.props.setEventHandler",
  "Lean.Vir.Js.Array.empty": "js.array.empty",
  "Lean.Vir.Js.Array.push": "js.array.push",
  "Lean.Vir.React.ElementType.tagJs": "react.elementType.tag",
  "Lean.Vir.React.Node.createElement": "react.node.createElement",
  "Lean.Vir.Browser.Performance.nowJs": "browser.performance.now",
  "Lean.Vir.JsValue.toFloat": "js.float.value",
  "Lean.Vir.React.Hooks.useRef": "react.useRef",
  "Lean.Vir.React.Ref.get": "react.ref.get",
  "Lean.Vir.JsValue.toString": "js.string.value",
  "Lean.Vir.React.Ref.set": "react.ref.set",
  "Lean.Vir.React.Hooks.DependencyList.empty": "react.deps.empty",
  "Lean.Vir.React.Hooks.DependencyList.push": "react.deps.push",
  "Lean.Vir.React.Hooks.useLeanEffectWithoutDepsJs": "react.useLeanEffect",
  "Lean.Vir.React.Hooks.useLeanEffectWithDepsJs": "react.useLeanEffectWithDeps",
  "Lean.Vir.React.Hooks.useState": "react.useState",
  "Lean.Vir.React.StateTuple.value": "react.stateTuple.value",
  "Lean.Vir.React.StateTuple.setter": "react.stateTuple.setter",
  "Lean.Vir.React.Node.textJs": "react.node.text",
  "Lean.Vir.React.StateSetter.modify": "react.state.modify",
  "Lean.Vir.Browser.Event.getCurrentTarget": "browser.event.currentTarget",
  "Lean.Vir.Js.Nullable.isNullJs": "js.nullable.isNull",
  "Lean.Vir.Js.Nullable.get": "js.nullable.value",
  "Lean.Vir.Browser.Event.getTarget": "browser.event.target",
  "Lean.Vir.Browser.HTMLInputElement.fromElementNullable":
    "browser.htmlInputElement.fromElement",
  "Lean.Vir.Browser.HTMLInputElement.getChecked":
    "browser.htmlInputElement.getChecked",
  "Lean.Vir.React.Node.componentThunkJs": "react.node.component",
  "Lean.Vir.React.Node.fragmentWithKeyJs": "react.node.fragment",
  "Lean.Vir.Browser.Performance.usedHeapBytesNullable":
    "browser.performance.usedHeapBytes",
  "Lean.Vir.JsValue.toNat": "js.nat.value",
  "Lean.Vir.Browser.Performance.heapLimitBytesNullable":
    "browser.performance.heapLimitBytes",
  "Lean.Vir.React.Root.renderComponentIntoSelectorThunkJs":
    "react.root.renderComponentIntoSelector",
});

export const VBP_VERSO_VIEWER_HOST_IMPORTS = Object.freeze(
  Object.entries(HOST_IMPORTS).map(([declaration, binding]) =>
    Object.freeze({ declaration, binding })),
);

const EXPLICIT_RESULT = Object.freeze({
  "Lean.Vir.JsValue.toBool": "bool",
  "Lean.Vir.JsValue.toFloat": "float",
  "Lean.Vir.JsValue.toString": "string",
  "Lean.Vir.JsValue.toNat": "natural",
});

function fail(message) {
  throw new Error(`FIR VBP Verso viewer adapter: ${message}`);
}

function requireCondition(condition, message) {
  if (!condition) fail(message);
}

function requireObject(value, label) {
  requireCondition(value !== null && typeof value === "object" &&
    !Array.isArray(value), `${label} must be an object`);
  return value;
}

function requireString(value, label) {
  requireCondition(typeof value === "string", `${label} must be a string`);
  return value;
}

function u32(value) {
  return Number(value) >>> 0;
}

function align8(value) {
  return Math.ceil(value / 8) * 8;
}

function immediate(tag) {
  requireCondition(Number.isSafeInteger(tag) && tag >= 0 && tag <= 0x7fffffff,
    `immediate payload ${tag} is invalid`);
  return u32(2 * tag + 1);
}

function defaultNow() {
  return typeof globalThis.performance?.now === "function" ?
    globalThis.performance.now() : Date.now();
}

function elapsed(now, started) {
  const value = now() - started;
  return Number.isFinite(value) && value >= 0 ? value : 0;
}

function writeHeader(view, address, { kind, bytes, flags = LIVE_FLAGS,
  rc = 1, aux0 = 0, aux1 = 0, aux2 = 0, aux3 = 0 }) {
  [kind, flags, rc, bytes, aux0, aux1, aux2, aux3].forEach((word, index) =>
    view.setUint32(address + 4 * index, u32(word), true));
}

function writeWord(view, address, value) {
  view.setUint32(address, u32(value), true);
  view.setUint32(address + 4, 0, true);
}

function classify(word) {
  const value = u32(word);
  if (value === 0) return "sentinel";
  if ((value & 1) === 1) return "immediate";
  if (value % 8 === 0) return "heap";
  return "invalid";
}

function readU32(view, address, label) {
  requireCondition(Number.isInteger(address) && address >= 0 &&
    address + 4 <= view.byteLength, `${label} is outside module memory`);
  return view.getUint32(address, true);
}

function readWord(view, address, label) {
  const word = readU32(view, address, label);
  requireCondition(readU32(view, address + 4, label) === 0,
    `${label} has nonzero word padding`);
  return word;
}

function readHeader(view, word, label) {
  const address = u32(word);
  requireCondition(classify(address) === "heap",
    `${label} has invalid address ${address}`);
  const flags = readU32(view, address + 4, label);
  const header = {
    address,
    kind: readU32(view, address, label),
    flags,
    rc: readU32(view, address + 8, label),
    bytes: readU32(view, address + 12, label),
    aux0: readU32(view, address + 16, label),
    aux1: readU32(view, address + 20, label),
    aux2: readU32(view, address + 24, label),
    aux3: readU32(view, address + 28, label),
  };
  requireCondition((flags & LIVE_FLAGS) !== 0 && header.bytes >= HEADER_BYTES &&
    header.bytes % 8 === 0 && address + header.bytes <= view.byteLength,
  `${label} has a malformed live allocation`);
  return header;
}

function readConstructor(view, word, tag, fields, scalarBytes, label) {
  if (fields === 0 && scalarBytes === 0) {
    requireCondition(classify(word) === "immediate" &&
      (u32(word) >>> 1) === tag, `${label} has the wrong nullary tag`);
    return { fields: [], scalarAddress: 0 };
  }
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.constructor && header.aux0 === tag &&
    header.aux1 === fields && header.aux2 === 0 && header.aux3 === scalarBytes &&
    HEADER_BYTES + SLOT_BYTES * fields + scalarBytes <= header.bytes,
  `${label} has an unexpected constructor layout`);
  return {
    fields: Array.from({ length: fields }, (_, index) =>
      readWord(view, header.address + HEADER_BYTES + SLOT_BYTES * index,
        `${label}.field[${index}]`)),
    scalarAddress: header.address + HEADER_BYTES + SLOT_BYTES * fields,
  };
}

function readString(view, word, decoder, label) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.string && header.aux0 === STRING_MARKER &&
    header.aux2 === 0 && header.aux3 === 0 &&
    HEADER_BYTES + header.aux1 <= header.bytes,
  `${label} is not a canonical UTF-8 String`);
  return decoder.decode(new Uint8Array(view.buffer,
    header.address + HEADER_BYTES, header.aux1));
}

function readNatural(view, word, label) {
  if (classify(word) === "immediate") return BigInt(u32(word) >>> 1);
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.natural,
    `${label} is not a Natural`);
  if ((header.flags & 1) !== 0 && header.aux0 === 1) {
    requireCondition(header.aux1 === 1 && header.bytes === 40,
      `${label} has a malformed tagged Natural`);
    return view.getBigUint64(header.address + HEADER_BYTES, true);
  }
  requireCondition(header.aux0 === 2 && header.aux1 > 0 &&
    header.bytes === align8(HEADER_BYTES + SLOT_BYTES * header.aux1),
  `${label} has a malformed multi-limb Natural`);
  let result = 0n;
  for (let index = header.aux1 - 1; index >= 0; --index) {
    result = (result << 64n) + view.getBigUint64(
      header.address + HEADER_BYTES + SLOT_BYTES * index, true);
  }
  return result;
}

function readInteger(view, word, label) {
  if (classify(word) === "immediate") return BigInt(u32(word) >>> 1);
  const header = readHeader(view, word, label);
  if (header.kind === KIND.natural && (header.flags & 1) !== 0 &&
      header.aux0 === 1 && header.aux1 === 1 && header.bytes === 40) {
    return BigInt.asIntN(32,
      view.getBigUint64(header.address + HEADER_BYTES, true));
  }
  requireCondition(header.kind === KIND.integer && header.aux0 === INTEGER_MARKER &&
    header.aux1 > 0 && (header.aux2 === 0 || header.aux2 === 1),
  `${label} is not a canonical Integer`);
  let magnitude = 0n;
  for (let index = header.aux1 - 1; index >= 0; --index) {
    magnitude = (magnitude << 64n) + view.getBigUint64(
      header.address + HEADER_BYTES + SLOT_BYTES * index, true);
  }
  return header.aux2 === 1 ? -magnitude : magnitude;
}

function readArray(view, word, label, maximumNodes) {
  const header = readHeader(view, word, label);
  requireCondition(header.kind === KIND.opaque && header.aux0 === ARRAY_MARKER &&
    header.aux1 <= maximumNodes && header.aux2 >= header.aux1 &&
    HEADER_BYTES + SLOT_BYTES * header.aux1 <= header.bytes,
  `${label} is not a resident Array`);
  return Array.from({ length: header.aux1 }, (_, index) =>
    readWord(view, header.address + HEADER_BYTES + SLOT_BYTES * index,
      `${label}[${index}]`));
}

function numberOrString(value) {
  return value >= BigInt(Number.MIN_SAFE_INTEGER) &&
      value <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(value) : value.toString();
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

function parseNatural(value, label) {
  let result;
  if (typeof value === "bigint") result = value;
  else if (typeof value === "number" && Number.isSafeInteger(value)) result = BigInt(value);
  else if (typeof value === "string" && /^(0|[1-9][0-9]*)$/u.test(value)) result = BigInt(value);
  else fail(`${label} must be a nonnegative integer`);
  requireCondition(result >= 0n, `${label} must be nonnegative`);
  return result;
}

function parseInteger(value, label) {
  if (typeof value === "bigint") return value;
  if (typeof value === "number" && Number.isSafeInteger(value)) return BigInt(value);
  if (typeof value === "string" && /^(0|-?[1-9][0-9]*)$/u.test(value)) return BigInt(value);
  fail(`${label} must be an integer`);
}

class LeanWriter {
  constructor(runtime, { maximumNodes = 100000 } = {}) {
    this.runtime = runtime;
    this.maximumNodes = maximumNodes;
    this.nodes = 0;
    this.bytes = 0;
    this.allocations = 0;
  }

  allocate(bytes, label) {
    requireCondition(bytes >= HEADER_BYTES && bytes % 8 === 0,
      `${label} allocation size is invalid`);
    const address = this.runtime.allocateRaw(bytes, label);
    new Uint8Array(this.runtime.memory.buffer, address, bytes).fill(0);
    this.bytes += bytes;
    this.allocations++;
    return address;
  }

  count(label) {
    this.nodes++;
    requireCondition(this.nodes <= this.maximumNodes,
      `${label} exceeds ${this.maximumNodes} nodes`);
  }

  string(value, label) {
    const source = requireString(value, label);
    const payload = this.runtime.encoder.encode(source);
    const bytes = align8(HEADER_BYTES + payload.length);
    const address = this.allocate(bytes, label);
    const view = this.runtime.view();
    writeHeader(view, address, { kind: KIND.string, bytes,
      aux0: STRING_MARKER, aux1: payload.length });
    new Uint8Array(this.runtime.memory.buffer,
      address + HEADER_BYTES, payload.length).set(payload);
    return address;
  }

  natural(value, label) {
    const n = parseNatural(value, label);
    if (n <= MAX_IMMEDIATE) return immediate(Number(n));
    if (n <= MAX_TAGGED) {
      const address = this.allocate(40, label);
      writeHeader(this.runtime.view(), address, { kind: KIND.natural,
        flags: 3, rc: 0, bytes: 40, aux0: 1, aux1: 1 });
      this.runtime.view().setBigUint64(address + HEADER_BYTES, n, true);
      return address;
    }
    const words = limbs(n);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * words.length);
    const address = this.allocate(bytes, label);
    const view = this.runtime.view();
    writeHeader(view, address, { kind: KIND.natural, bytes,
      aux0: 2, aux1: words.length });
    words.forEach((word, index) => view.setBigUint64(
      address + HEADER_BYTES + SLOT_BYTES * index, word, true));
    return address;
  }

  integer(value, label) {
    const n = parseInteger(value, label);
    if (n >= MIN_SIGNED_32 && n <= MAX_SIGNED_32) {
      const payload = BigInt.asUintN(32, n);
      if (payload <= MAX_IMMEDIATE) return immediate(Number(payload));
      const address = this.allocate(40, label);
      writeHeader(this.runtime.view(), address, { kind: KIND.natural,
        flags: 3, rc: 0, bytes: 40, aux0: 1, aux1: 1 });
      this.runtime.view().setBigUint64(address + HEADER_BYTES, payload, true);
      return address;
    }
    const negative = n < 0n;
    const words = limbs(negative ? -n : n);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * words.length);
    const address = this.allocate(bytes, label);
    const view = this.runtime.view();
    writeHeader(view, address, { kind: KIND.integer, bytes,
      aux0: INTEGER_MARKER, aux1: words.length, aux2: negative ? 1 : 0 });
    words.forEach((word, index) => view.setBigUint64(
      address + HEADER_BYTES + SLOT_BYTES * index, word, true));
    return address;
  }

  boxedFloat(value, label) {
    requireCondition(typeof value === "number" && Number.isFinite(value),
      `${label} must be a finite Number`);
    const address = this.allocate(40, label);
    const view = this.runtime.view();
    writeHeader(view, address, { kind: KIND.boxed, bytes: 40,
      aux0: FLOAT_BOX_MARKER, aux1: 8 });
    view.setFloat64(address + HEADER_BYTES, value, true);
    return address;
  }

  ctor(tag, fields, scalars, label) {
    this.count(label);
    requireCondition(Array.isArray(fields) && scalars instanceof Uint8Array,
      `${label} constructor payload is invalid`);
    if (fields.length === 0 && scalars.length === 0) return immediate(tag);
    const bytes = align8(HEADER_BYTES + SLOT_BYTES * fields.length + scalars.length);
    const address = this.allocate(bytes, label);
    const view = this.runtime.view();
    writeHeader(view, address, { kind: KIND.constructor, bytes,
      aux0: tag, aux1: fields.length, aux3: scalars.length });
    fields.forEach((field, index) => writeWord(view,
      address + HEADER_BYTES + SLOT_BYTES * index, field));
    new Uint8Array(this.runtime.memory.buffer,
      address + HEADER_BYTES + SLOT_BYTES * fields.length,
      scalars.length).set(scalars);
    return address;
  }

  list(words, label) {
    let tail = immediate(0);
    for (let index = words.length - 1; index >= 0; --index) {
      tail = this.ctor(1, [words[index], tail], new Uint8Array(),
        `${label}[${index}]`);
    }
    return tail;
  }

  rpcJson(value, label = "RpcJson", depth = 0) {
    requireCondition(depth <= 256, `${label} exceeds maximum depth 256`);
    const node = requireObject(value, label);
    switch (node.kind) {
      case "null":
        return this.ctor(0, [], new Uint8Array(), label);
      case "bool": {
        requireCondition(typeof node.value === "boolean",
          `${label}.value must be Boolean`);
        return this.ctor(1, [], Uint8Array.of(node.value ? 1 : 0), label);
      }
      case "number": {
        const fields = requireObject(node.fields, `${label}.fields`);
        return this.ctor(2, [
          this.integer(fields.mantissa, `${label}.fields.mantissa`),
          this.natural(fields.exponent, `${label}.fields.exponent`),
        ], new Uint8Array(), label);
      }
      case "string":
        return this.ctor(3, [this.string(node.value, `${label}.value`)],
          new Uint8Array(), label);
      case "array": {
        requireCondition(Array.isArray(node.value), `${label}.value must be an Array`);
        const items = node.value.map((item, index) =>
          this.rpcJson(item, `${label}.value[${index}]`, depth + 1));
        return this.ctor(4, [this.list(items, `${label}.value`)],
          new Uint8Array(), label);
      }
      case "object": {
        requireCondition(Array.isArray(node.value), `${label}.value must be an Array`);
        const entries = node.value.map((entry, index) => {
          const pair = requireObject(entry, `${label}.value[${index}]`);
          return this.ctor(0, [
            this.string(pair.fst, `${label}.value[${index}].fst`),
            this.rpcJson(pair.snd, `${label}.value[${index}].snd`, depth + 1),
          ], new Uint8Array(), `${label}.value[${index}]`);
        });
        return this.ctor(5, [this.list(entries, `${label}.value`)],
          new Uint8Array(), label);
      }
      default:
        fail(`${label}.kind ${String(node.kind)} is unsupported`);
    }
  }
}

class FirVbpRuntime {
  constructor({ module, manifest, build, hostBindings, now, maximumNodes }) {
    this.module = module;
    this.manifest = manifest;
    this.build = build;
    this.hostBindings = requireObject(hostBindings, "hostBindings");
    this.now = now;
    this.maximumNodes = maximumNodes;
    this.encoder = new TextEncoder();
    this.decoder = new TextDecoder("utf-8", { fatal: true });
    this.resources = new Map();
    this.callbackRoots = new Set();
    this.mountedSelectors = new Set();
    this.nextResourceId = 1;
    this.disposed = false;
    this.instance = null;
    this.lastCall = null;
  }

  importObject() {
    const imports = {};
    for (const name of Object.keys(HOST_IMPORTS)) {
      imports[name] = (...args) => this.invokeImport(name, args);
    }
    return { "lean.extern": imports };
  }

  attach(instance) {
    this.instance = instance;
    this.exports = instance.exports;
    this.memory = this.requiredMemory("memory");
    this.frontier = this.requiredFunction("fir_heap_frontier");
    this.setFrontier = this.requiredFunction("fir_heap_set_frontier");
    this.allocate = this.requiredFunction("fir_heap_alloc");
    this.synchronizeFrontier();
  }

  requiredFunction(name) {
    const value = this.exports?.[name];
    requireCondition(typeof value === "function",
      `module is missing function export ${name}`);
    return value;
  }

  requiredMemory(name) {
    const value = this.exports?.[name];
    requireCondition(value instanceof WebAssembly.Memory,
      `module is missing memory export ${name}`);
    return value;
  }

  requireLive() {
    requireCondition(!this.disposed && this.instance !== null,
      "runtime is disposed or invalid");
  }

  view() {
    return new DataView(this.memory.buffer);
  }

  synchronizeFrontier() {
    const value = u32(this.frontier());
    requireCondition(value >= HEAP_BASE && value % 8 === 0,
      `resident frontier ${value} is invalid`);
    this.setFrontier(value);
    this.lastFrontier = value;
    return value;
  }

  allocateRaw(bytes, label) {
    this.requireLive();
    const address = u32(this.allocate(bytes));
    requireCondition(address >= HEAP_BASE && address % 8 === 0 &&
      address + bytes <= this.memory.buffer.byteLength,
    `${label} allocation returned invalid address ${address}`);
    this.lastFrontier = this.synchronizeFrontier();
    return address;
  }

  allocateResource(value, label = "host resource") {
    requireCondition(value !== null && value !== undefined,
      `${label} must be a non-null host resource`);
    const address = this.allocateRaw(HEADER_BYTES, label);
    writeHeader(this.view(), address, { kind: KIND.opaque,
      bytes: HEADER_BYTES, aux0: HOST_RESOURCE_MARKER,
      aux1: this.nextResourceId++ });
    this.resources.set(address, value);
    return address;
  }

  resolveResource(word, label, { take = false } = {}) {
    const address = u32(word);
    const value = this.resources.get(address);
    requireCondition(value !== undefined,
      `${label} does not name a live host resource (${address})`);
    if (take) this.resources.delete(address);
    return value;
  }

  hostBinding(name) {
    const target = HOST_IMPORTS[name];
    const binding = this.hostBindings[target];
    requireCondition(typeof binding === "function",
      `host binding ${target} for ${name} is unavailable`);
    return binding;
  }

  invokeImport(name, args) {
    this.requireLive();
    const binding = this.hostBinding(name);
    let result;
    switch (name) {
      case "Lean.Vir.JsValue.ofString":
        result = binding(readString(this.view(), args[0], this.decoder,
          "JsValue.ofString argument"));
        break;
      case "Lean.Vir.React.Property.toJs":
        result = binding(this.decodeProperty(args[0]));
        break;
      case "Lean.Vir.React.EventHandler.toJs":
        result = binding(this.decodeEventHandler(args[0]));
        break;
      case "Lean.Vir.JsValue.toBool":
      case "Lean.Vir.JsValue.toFloat":
      case "Lean.Vir.JsValue.toString":
      case "Lean.Vir.JsValue.toNat":
        result = binding(this.resolveResource(args[0], `${name} argument`));
        break;
      case "Lean.Vir.React.Hooks.useLeanEffectWithoutDepsJs":
        result = binding(this.createCallback("effectSetup", args[0]));
        break;
      case "Lean.Vir.React.Hooks.useLeanEffectWithDepsJs":
        result = binding(this.resolveResource(args[0], `${name} deps`),
          this.createCallback("effectSetup", args[1]));
        break;
      case "Lean.Vir.React.StateSetter.modify":
        result = binding(this.resolveResource(args[1], `${name} setter`),
          this.createCallback("state", args[2]));
        break;
      case "Lean.Vir.React.Node.componentThunkJs":
        result = binding(this.resolveResource(args[0], `${name} componentType`),
          this.createCallback("component", args[1]));
        break;
      case "Lean.Vir.React.Root.renderComponentIntoSelectorThunkJs":
        result = binding(
          this.resolveResource(args[0], `${name} selector`),
          this.resolveResource(args[1], `${name} componentType`),
          this.createCallback("component", args[2]));
        break;
      default: {
        const descriptor = this.manifest.imports.find(
          (candidate) => candidate.name === name)?.operation;
        requireCondition(descriptor !== undefined,
          `module descriptor is missing import ${name}`);
        const values = [];
        descriptor.params.forEach((kind, index) => {
          if (kind !== "erased") {
            values.push(this.resolveResource(args[index],
              `${name} argument ${index}`));
          }
        });
        result = binding(...values);
        break;
      }
    }
    return this.encodeImportResult(name, result);
  }

  encodeImportResult(name, value) {
    let payload;
    switch (EXPLICIT_RESULT[name]) {
      case "bool":
        requireCondition(typeof value === "boolean",
          `${HOST_IMPORTS[name]} must return Boolean`);
        payload = immediate(value ? 1 : 0);
        break;
      case "float":
        payload = new LeanWriter(this).boxedFloat(value,
          `${HOST_IMPORTS[name]} result`);
        break;
      case "string":
        payload = new LeanWriter(this).string(value,
          `${HOST_IMPORTS[name]} result`);
        break;
      case "natural":
        payload = new LeanWriter(this).natural(value,
          `${HOST_IMPORTS[name]} result`);
        break;
      default:
        payload = value === undefined ? immediate(0) :
          this.allocateResource(value, `${HOST_IMPORTS[name]} result`);
        break;
    }
    return new LeanWriter(this).ctor(0, [payload], new Uint8Array(),
      `${HOST_IMPORTS[name]} EStateM.Result.ok`);
  }

  unwrapRuntimeResult(word, label) {
    const view = this.view();
    const header = readHeader(view, word, `${label} result`);
    requireCondition(header.kind === KIND.constructor && header.aux1 === 1 &&
      header.aux2 === 0 && header.aux3 === 0,
    `${label} returned a malformed EStateM.Result`);
    if (header.aux0 === 0) {
      return readWord(view, header.address + HEADER_BYTES,
        `${label} result value`);
    }
    requireCondition(header.aux0 === 1,
      `${label} returned EStateM.Result tag ${header.aux0}`);
    fail(`${label} returned a Lean runtime error`);
  }

  decodeProperty(word) {
    const view = this.view();
    const { fields } = readConstructor(view, word, 0, 2, 0, "Property");
    return {
      name: readString(view, fields[0], this.decoder, "Property.name"),
      value: this.decodePropValue(fields[1]),
    };
  }

  decodePropValue(word) {
    const view = this.view();
    const tag = classify(word) === "immediate" ? u32(word) >>> 1 :
      readHeader(view, word, "PropValue").aux0;
    switch (tag) {
      case 0: {
        const { fields } = readConstructor(view, word, 0, 1, 0, "PropValue.string");
        return { kind: "string",
          value: readString(view, fields[0], this.decoder, "PropValue.string.value") };
      }
      case 1: {
        const value = readConstructor(view, word, 1, 0, 1, "PropValue.bool");
        return { kind: "bool", value: view.getUint8(value.scalarAddress) !== 0 };
      }
      case 2: {
        const { fields } = readConstructor(view, word, 2, 1, 0, "PropValue.int");
        return { kind: "int", value: numberOrString(
          readInteger(view, fields[0], "PropValue.int.value")) };
      }
      case 3: {
        const value = readConstructor(view, word, 3, 0, 8, "PropValue.float");
        return { kind: "float", value: view.getFloat64(value.scalarAddress, true) };
      }
      case 4: {
        const { fields } = readConstructor(view, word, 4, 1, 0, "PropValue.style");
        return { kind: "style", value: readArray(view, fields[0],
          "PropValue.style.value", this.maximumNodes).map((entry, index) => {
            const item = readConstructor(view, entry, 0, 2, 0,
              `PropValue.style.value[${index}]`).fields;
            return {
              name: readString(view, item[0], this.decoder,
                `PropValue.style.value[${index}].name`),
              value: readString(view, item[1], this.decoder,
                `PropValue.style.value[${index}].value`),
            };
          }) };
      }
      case 5: {
        const { fields } = readConstructor(view, word, 5, 1, 0, "PropValue.classList");
        return { kind: "classList", value: readArray(view, fields[0],
          "PropValue.classList.value", this.maximumNodes).map((item, index) =>
            readString(view, item, this.decoder,
              `PropValue.classList.value[${index}]`)) };
      }
      default:
        fail(`PropValue has unsupported tag ${tag}`);
    }
  }

  decodeEventHandler(word) {
    const view = this.view();
    const { fields } = readConstructor(view, word, 0, 2, 0, "EventHandler");
    return {
      name: readString(view, fields[0], this.decoder, "EventHandler.name"),
      callback: this.createCallback("event", fields[1]),
    };
  }

  createCallback(kind, closureWord) {
    const closure = u32(closureWord);
    const header = readHeader(this.view(), closure, `${kind} callback`);
    requireCondition(header.kind === KIND.closure,
      `${kind} callback is not a Lean closure`);
    const root = { kind, closure, live: true, leases: 0 };
    this.callbackRoots.add(root);
    return this.callbackLease(root);
  }

  callbackLease(root) {
    requireCondition(root.live && !this.disposed,
      `${root.kind} callback has been released`);
    root.leases++;
    let released = false;
    const callback = (...args) => {
      requireCondition(!released && root.live && !this.disposed,
        `${root.kind} callback has been released`);
      return this.callCallback(root, args);
    };
    callback.retain = () => this.callbackLease(root);
    callback.release = () => {
      if (released || !root.live) return false;
      released = true;
      root.leases--;
      if (root.leases === 0) {
        root.live = false;
        this.callbackRoots.delete(root);
        this.requiredFunction(VBP_VERSO_VIEWER_RELEASE_OWNED_ENTRY)(
          root.closure, 1);
      }
      return true;
    };
    Object.defineProperty(callback, "released", {
      get: () => released || !root.live || this.disposed,
    });
    return callback;
  }

  callCallback(root, args) {
    const before = this.synchronizeFrontier();
    let result;
    switch (root.kind) {
      case "component":
        result = this.unwrapRuntimeResult(
          this.requiredFunction(BRIDGE.component)(root.closure, 0),
          "component callback");
        result = this.resolveResource(result, "component callback result", { take: true });
        break;
      case "event": {
        requireCondition(args.length === 1, "event callback expects one argument");
        const event = this.allocateResource(args[0], "event callback argument");
        result = this.unwrapRuntimeResult(
          this.requiredFunction(BRIDGE.event)(root.closure, event, 0),
          "event callback");
        this.requireUnit(result, "event callback");
        result = undefined;
        break;
      }
      case "state": {
        requireCondition(args.length === 1, "state callback expects one argument");
        const value = this.allocateResource(args[0], "state callback argument");
        const word = this.unwrapRuntimeResult(
          this.requiredFunction(BRIDGE.state)(root.closure, value, 0),
          "state callback");
        result = this.resolveResource(word, "state callback result", { take: true });
        break;
      }
      case "effectSetup": {
        requireCondition(args.length === 0, "effect setup callback expects no arguments");
        const word = this.unwrapRuntimeResult(
          this.requiredFunction(BRIDGE.effectSetup)(root.closure, 0),
          "effect setup callback");
        if (classify(word) === "immediate") {
          requireCondition((u32(word) >>> 1) === 0,
            "effect setup returned an invalid Option tag");
          result = null;
        } else {
          const { fields } = readConstructor(this.view(), word, 1, 1, 0,
            "effect setup result");
          result = this.createCallback("effectCleanup", fields[0]);
        }
        break;
      }
      case "effectCleanup":
        requireCondition(args.length === 0, "effect cleanup callback expects no arguments");
        result = this.unwrapRuntimeResult(
          this.requiredFunction(BRIDGE.effectCleanup)(root.closure, 0),
          "effect cleanup callback");
        this.requireUnit(result, "effect cleanup callback");
        result = undefined;
        break;
      default:
        fail(`unknown callback kind ${root.kind}`);
    }
    this.lastFrontier = this.synchronizeFrontier();
    requireCondition(this.lastFrontier >= before,
      "callback unexpectedly rewound the resident frontier");
    return result;
  }

  requireUnit(word, label) {
    requireCondition(classify(word) === "immediate" && (u32(word) >>> 1) === 0,
      `${label} did not return Unit`);
  }

  invoke(entry, args) {
    this.requireLive();
    requireCondition(Array.isArray(args), "invoke args must be an Array");
    const totalStarted = this.now();
    const encodeStarted = this.now();
    const frontierBefore = this.synchronizeFrontier();
    const writer = new LeanWriter(this, { maximumNodes: this.maximumNodes });
    let physicalArgs;
    if (entry === VBP_VERSO_VIEWER_MOUNT_ENTRY) {
      requireCondition(args.length === 2, "mount expects selector and RpcJson");
      physicalArgs = [
        writer.string(args[0], "mount selector"),
        writer.rpcJson(args[1]),
        0,
      ];
    } else if (entry === VBP_VERSO_VIEWER_UNMOUNT_ENTRY) {
      requireCondition(args.length === 1, "unmount expects one selector");
      physicalArgs = [writer.string(args[0], "unmount selector"), 0];
    } else {
      fail(`unknown logical entry ${entry}`);
    }
    const encodeMs = elapsed(this.now, encodeStarted);
    const frontierAfterEncode = this.synchronizeFrontier();
    const executeStarted = this.now();
    const word = this.unwrapRuntimeResult(
      this.requiredFunction(entry)(...physicalArgs), entry);
    const executeMs = elapsed(this.now, executeStarted);
    const decodeStarted = this.now();
    requireCondition(classify(word) === "immediate" &&
      ((u32(word) >>> 1) === 0 || (u32(word) >>> 1) === 1),
    `${entry} did not return Bool`);
    const result = (u32(word) >>> 1) === 1;
    const decodeMs = elapsed(this.now, decodeStarted);
    const frontierAfter = this.synchronizeFrontier();
    const totalMs = elapsed(this.now, totalStarted);
    const selector = args[0];
    if (result && entry === VBP_VERSO_VIEWER_MOUNT_ENTRY) {
      this.mountedSelectors.add(selector);
    } else if (entry === VBP_VERSO_VIEWER_UNMOUNT_ENTRY) {
      this.mountedSelectors.delete(selector);
    }
    this.lastCall = Object.freeze({
      entry,
      result,
      timings: Object.freeze({ encodeMs, executeMs, decodeMs, totalMs,
        overheadMs: Math.max(0, totalMs - encodeMs - executeMs - decodeMs) }),
      memory: Object.freeze({
        frontierBefore,
        frontierAfterEncode,
        frontierAfter,
        growth: frontierAfter - frontierBefore,
        pages: this.memory.buffer.byteLength / PAGE_BYTES,
        encodedBytes: writer.bytes,
        encodedObjects: writer.allocations,
        hostResourceHandles: this.resources.size,
        liveCallbackRoots: this.callbackRoots.size,
      }),
    });
    return result;
  }

  describeEntry(entry) {
    if (entry === VBP_VERSO_VIEWER_MOUNT_ENTRY) {
      return { entry, params: ["String", "Lean.Vir.Infoview.RpcJson"],
        result: "Bool", effect: "DomM" };
    }
    if (entry === VBP_VERSO_VIEWER_UNMOUNT_ENTRY) {
      return { entry, params: ["String"], result: "Bool", effect: "DomM" };
    }
    return null;
  }

  dispose() {
    if (this.disposed) return false;
    for (const selector of Array.from(this.mountedSelectors)) {
      try {
        this.invoke(VBP_VERSO_VIEWER_UNMOUNT_ENTRY, [selector]);
      } catch {
        // Continue invalidation: dropping the instance is the terminal owner.
      }
    }
    this.disposed = true;
    for (const root of this.callbackRoots) root.live = false;
    this.callbackRoots.clear();
    const uniqueResources = new Set(this.resources.values());
    this.resources.clear();
    for (const resource of uniqueResources) {
      try {
        resource?.release?.();
      } catch {
        // Best-effort cleanup; host resource owners also invalidate on dispose.
      }
    }
    this.mountedSelectors.clear();
    this.instance = null;
    this.exports = null;
    this.memory = null;
    return true;
  }
}

function validateManifest(manifest, module) {
  requireObject(manifest, "module descriptor");
  const imports = WebAssembly.Module.imports(module);
  requireCondition(imports.length === Object.keys(HOST_IMPORTS).length,
    `expected ${Object.keys(HOST_IMPORTS).length} function imports`);
  requireCondition(imports.every(({ module: namespace, name, kind }) =>
    namespace === "lean.extern" && kind === "function" &&
      Object.hasOwn(HOST_IMPORTS, name)),
  "module import frontier differs from the reviewed VIR host contract");
  requireCondition(Array.isArray(manifest.imports) &&
    manifest.imports.length === imports.length,
  "module descriptor import inventory is inconsistent");
  const exports = new Set(WebAssembly.Module.exports(module).map(({ name }) => name));
  for (const name of [VBP_VERSO_VIEWER_MOUNT_ENTRY,
    VBP_VERSO_VIEWER_UNMOUNT_ENTRY, ...Object.values(BRIDGE),
    VBP_VERSO_VIEWER_RELEASE_OWNED_ENTRY,
    "fir_heap_frontier", "fir_heap_set_frontier", "fir_heap_rewind",
    "fir_heap_alloc", "memory"]) {
    requireCondition(exports.has(name), `module is missing export ${name}`);
  }
}

async function resolveModule({ bytes, module }) {
  if (module instanceof WebAssembly.Module) return module;
  requireCondition(bytes instanceof ArrayBuffer || ArrayBuffer.isView(bytes),
    "bytes must be an ArrayBuffer or typed-array view");
  return WebAssembly.compile(bytes);
}

export async function createVbpVersoViewerAdapter({
  bytes,
  module,
  manifest,
  build = null,
  hostBindings,
  now = defaultNow,
  maximumNodes = 100000,
  fetchMs = 0,
} = {}) {
  requireCondition(typeof now === "function", "now must be a function");
  requireCondition(Number.isSafeInteger(maximumNodes) && maximumNodes > 0,
    "maximumNodes must be a positive safe integer");
  requireCondition(Number.isFinite(fetchMs) && fetchMs >= 0,
    "fetchMs must be a finite nonnegative number");
  const totalStarted = now();
  const compileStarted = now();
  const compiled = await resolveModule({ bytes, module });
  const compileMs = elapsed(now, compileStarted);
  validateManifest(manifest, compiled);
  const runtime = new FirVbpRuntime({ module: compiled, manifest, build,
    hostBindings, now, maximumNodes });
  const instantiateStarted = now();
  const instance = await WebAssembly.instantiate(compiled, runtime.importObject());
  runtime.attach(instance);
  const instantiateMs = elapsed(now, instantiateStarted);
  const totalMs = elapsed(now, totalStarted) + fetchMs;
  const initialization = Object.freeze({
    fetchMs,
    compileMs,
    instantiateMs,
    totalMs,
    overheadMs: Math.max(0, totalMs - fetchMs - compileMs - instantiateMs),
  });
  return Object.freeze({
    adapterApiVersion: VBP_VERSO_VIEWER_ADAPTER_API_VERSION,
    inputLayoutVersion: VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION,
    ownershipVersion: VBP_VERSO_VIEWER_OWNERSHIP_VERSION,
    revision: build?.package?.revision ?? build?.wasm?.sha256 ?? "",
    initialization,
    invoke: (entry, args) => runtime.invoke(entry, args),
    describeEntry: (entry) => runtime.describeEntry(entry),
    dispose: () => runtime.dispose(),
    get lastCall() { return runtime.lastCall; },
    get disposed() { return runtime.disposed; },
  });
}

export function createVbpVersoViewerComponentRuntimeProvider({
  id = "fir-vbp-verso-viewer",
  bytes,
  module,
  manifest,
  build = null,
  now = defaultNow,
  maximumNodes = 100000,
  fetchMs = 0,
} = {}) {
  requireCondition(typeof id === "string" && id.length > 0,
    "provider id must be a nonempty string");
  return Object.freeze({
    apiVersion: LEAN_COMPONENT_RUNTIME_PROVIDER_API,
    id,
    async open({ hostBindings } = {}) {
      const adapter = await createVbpVersoViewerAdapter({ bytes, module,
        manifest, build, hostBindings, now, maximumNodes, fetchMs });
      return {
        revision: adapter.revision,
        initialization: adapter.initialization,
        describeEntry: (entry) => adapter.describeEntry(entry),
        invoke: (entry, args) => adapter.invoke(entry, args),
        dispose: () => adapter.dispose(),
        get lastCall() { return adapter.lastCall; },
      };
    },
  });
}

export async function fetchVbpVersoViewerComponentRuntimeProvider({
  wasmUrl,
  manifestUrl,
  buildUrl,
  fetch: fetchImpl = globalThis.fetch,
  ...options
} = {}) {
  requireCondition(typeof fetchImpl === "function", "fetch must be available");
  const clock = typeof options.now === "function" ? options.now : defaultNow;
  const fetchStarted = clock();
  const [wasmResponse, manifestResponse, buildResponse] = await Promise.all([
    fetchImpl(wasmUrl), fetchImpl(manifestUrl), fetchImpl(buildUrl),
  ]);
  for (const [label, response] of [["Wasm", wasmResponse],
    ["manifest", manifestResponse], ["BUILD", buildResponse]]) {
    requireCondition(response?.ok === true,
      `${label} fetch failed with status ${response?.status}`);
  }
  const [bytes, manifest, build] = await Promise.all([
    wasmResponse.arrayBuffer(), manifestResponse.json(), buildResponse.json(),
  ]);
  const fetchMs = elapsed(clock, fetchStarted);
  return createVbpVersoViewerComponentRuntimeProvider({
    ...options, bytes, manifest, build, fetchMs,
  });
}
