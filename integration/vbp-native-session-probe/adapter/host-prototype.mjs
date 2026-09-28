import {createFirConstructionRuntime} from './direct-sink-runtime.mjs';
import {createFirDirectPreviewDecoder} from './fir-direct-typed-decoder.mjs';
import { leanBoolPayload } from './host-bool-abi.mjs';
import { OPTIONS_HOST_IMPORTS, OPTIONS_BORROWED, OPTIONS_CALLBACK_ABI,
  CONFIGURED_ENTRY, CONFIGURED_HOST_IMPORTS, CONFIGURED_BORROWED,
  CONFIGURED_CALLBACK_ABI } from './options-sdk-profile.mjs';
import { FLOAT_FORMAT_VERSION, FLOAT_FORMAT_RESERVED_BYTES, FLOAT_FORMAT_STRING_LAYOUT }
  from './float-format-contract.mjs';

/** Deliberately session-retained FIR/VIR bridge, not a permanent host ABI.
 * The caller supplies the pinned VIR host implementations (including React).
 * Wasm pointers never leave this module. No automatic rewind or finalization.
 */
export const HOST_IMPORTS = Object.freeze({
  "Lean.Vir.Js.Array.empty": ["js.array.empty", "__"],
  "Lean.Vir.React.Node.fragment": ["react.node.fragment", "jj_"],
  "Lean.Vir.JsValue.ofString": ["js.string", "s_"],
  "Lean.Vir.React.Node.text": ["react.node.text", "j_"],
  "Lean.Vir.Js.Object.empty": ["js.object.empty", "_"],
  "Lean.Vir.Js.Object.set": ["js.object.set", "_jjj_"],
  "Lean.Vir.JsValue.ofBool": ["js.bool", "b_"],
  "Lean.Vir.JsValue.ofFloat": ["js.float", "f_"],
  "Lean.Vir.React.Callback.ofUnary": ["js.value.react.callback", "_c_"],
  "Lean.Vir.React.ElementType.tag": ["react.elementType.tag", "j_"],
  "Lean.Vir.React.Node.createElement": ["react.node.createElement", "jjj_"],
  "Lean.Vir.Js.Array.push": ["js.array.push", "_jj_"],
});

// Exact current VBP 92db6325 / VIR 36d26bc2 inventory. This is not a caller-
// supplied registry; the accepted legacy factory keeps its original profile.
export const CURRENT_HOST_IMPORTS = Object.freeze({
  "Lean.Vir.Js.Array.empty": HOST_IMPORTS["Lean.Vir.Js.Array.empty"],
  "Lean.Vir.React.Node.fragment": HOST_IMPORTS["Lean.Vir.React.Node.fragment"],
  "Lean.Vir.JsValue.ofString": HOST_IMPORTS["Lean.Vir.JsValue.ofString"],
  "Lean.Vir.Js.Object.empty": HOST_IMPORTS["Lean.Vir.Js.Object.empty"],
  "Lean.Vir.Js.Object.set": HOST_IMPORTS["Lean.Vir.Js.Object.set"],
  "Lean.Vir.JsValue.ofBool": HOST_IMPORTS["Lean.Vir.JsValue.ofBool"],
  "Lean.Vir.JsValue.ofFloat": HOST_IMPORTS["Lean.Vir.JsValue.ofFloat"],
  "Lean.Vir.React.Callback.ofUnary": HOST_IMPORTS["Lean.Vir.React.Callback.ofUnary"],
  "Lean.Vir.React.Node.createElement": HOST_IMPORTS["Lean.Vir.React.Node.createElement"],
  "Lean.Vir.Js.Array.push": HOST_IMPORTS["Lean.Vir.Js.Array.push"],
  "Lean.Vir.Js.Object.get": ["js.object.get", "_jj_"],
  "Lean.Vir.Js.UndefinedOr.isUndefined": ["js.undefinedOr.isUndefined", "_j_"],
  "Lean.Vir.JsValue.toBool": ["js.bool.value", "j_"],
});

const PREFIX = "FirVbpHostPrototype.";
const UNIT = 1;
const leanObjectTokens = new WeakSet();
export const isFirLeanObjectHandle = value => leanObjectTokens.has(value);
const HEADER = 32;
const RESOURCE = 0x4a534852;
const align = n => Math.ceil(n / 8) * 8;
const check = (ok, message) => { if (!ok) throw new Error(`FIR host prototype: ${message}`); };

export const createRendererHostPrototype = options => createHost(options, false);
export const createCurrentRendererHostPrototype = options => createHost(options, true);
export const createOptionsComponentHostPrototype = options => createHost(options, 'options');
export const createConfiguredComponentHostPrototype = options => createHost(options, 'configured');
export const createCodecComponentHostPrototype = options => createHost(options, 'codec');

async function createHost({ module, manifest, bindings, hostBoundary, callbackBoundary, entryBoundary, constructorLayouts }, current) {
  const codec = current === 'codec';
  const { CODEC_HOST_IMPORTS, CODEC_BORROWED, CODEC_CALLBACK_ABI,
    CODEC_CONSTRUCTOR_ABI, CODEC_PREFIX, CODEC_ENTRY_ABI } = codec ? await import('./codec-sdk-profile.mjs') : {};
  const configured = current === 'configured' || codec;
  const options = current === 'options' || configured;
  const prefix = options ? 'FirVbpOptionsSdk.' : PREFIX;
  const inventory = codec ? CODEC_HOST_IMPORTS : configured ? CONFIGURED_HOST_IMPORTS : options ? OPTIONS_HOST_IMPORTS : current ? CURRENT_HOST_IMPORTS : HOST_IMPORTS;
  const borrowed = codec ? CODEC_BORROWED : configured ? CONFIGURED_BORROWED : OPTIONS_BORROWED;
  const callbackAbi = codec ? CODEC_CALLBACK_ABI : configured ? CONFIGURED_CALLBACK_ABI : OPTIONS_CALLBACK_ABI;
  const count = Object.keys(inventory).length;
  check(module instanceof WebAssembly.Module, "expected compiled WebAssembly.Module");
  const imports = WebAssembly.Module.imports(module);
  check(imports.length === count && new Set(imports.map(i => i.name)).size === count &&
    imports.every(i => i.kind === "function" && i.module === "lean.extern" &&
      Object.hasOwn(inventory, i.name)), options ? 'expected exactly thirty-one reviewed function imports' : current ? "expected exactly thirteen reviewed function imports" : "expected exactly twelve reviewed function imports");
  const providers = Object.create(null);
  if (options) {
    check(manifest?.nativeFloatRuntime?.version === FLOAT_FORMAT_VERSION &&
      manifest.nativeFloatRuntime.reservedMemoryBytes === FLOAT_FORMAT_RESERVED_BYTES &&
      JSON.stringify(manifest.nativeFloatRuntime.stringLayout) === JSON.stringify(FLOAT_FORMAT_STRING_LAYOUT) &&
      /^[a-f0-9]{64}$/.test(manifest.nativeFloatRuntime.providerBuildSha256),
    'missing reviewed native Float/String bridge capability');
    check(Array.isArray(callbackBoundary) && callbackBoundary.length === Object.keys(callbackAbi).length + (codec ? Object.keys(CODEC_CONSTRUCTOR_ABI).length : 0),
      'missing exact compiled callback ABI audit');
    for (const [name, [params, borrowed]] of Object.entries(callbackAbi)) {
      const rows = callbackBoundary.filter(row => row.name === prefix + name);
      check(rows.length === 1 && JSON.stringify(rows[0].params) === JSON.stringify(params) &&
        JSON.stringify(rows[0].borrowed) === JSON.stringify(borrowed) &&
        JSON.stringify(rows[0].result) === '["object"]', `wrong callback ABI/borrow contract for ${name}`);
    }
    if (codec) for (const [name, [params, borrow]] of Object.entries(CODEC_CONSTRUCTOR_ABI)) {
      const rows = callbackBoundary.filter(row => row.name === 'FirVbpCodecSdk.' + name);
      check(rows.length === 1 && JSON.stringify(rows[0].params) === JSON.stringify([...params, 'erased']) &&
        JSON.stringify(rows[0].borrowed) === JSON.stringify([...borrow, false]) &&
        JSON.stringify(rows[0].result) === '["object"]', `wrong compiled codec constructor ABI for ${name}`);
    }
    if (codec) {
      check(Array.isArray(entryBoundary) && entryBoundary.length === Object.keys(CODEC_ENTRY_ABI).length,
        'missing compiled source entry ABI audit');
      for (const [name, [params, borrow]] of Object.entries(CODEC_ENTRY_ABI)) {
        const rows = entryBoundary.filter(row => row.name === name);
        check(rows.length === 1 && JSON.stringify(rows[0].params) === JSON.stringify(params) &&
          JSON.stringify(rows[0].borrowed) === JSON.stringify(borrow) &&
          JSON.stringify(rows[0].result) === '["object"]', `wrong compiled source entry ABI for ${name}`);
      }
    }
  }
  for (const [target] of Object.values(inventory)) {
    if (options && (target === 'js.leanRef' || target === 'js.leanRef.value')) continue;
    const provider = bindings?.[target];
    check(typeof provider === "function", `missing host binding ${target}`);
    providers[target] = provider;
  }
  const kinds = { _: "erased", j: "tobject", s: "object", c: "object", b: "uint8", f: "float",
    r: 'tobject', u: 'object', m: 'object', e: 'object', n: 'object' };
  check(Array.isArray(manifest?.imports) && manifest.imports.length === count,
    "expected exact generated import manifest");
  for (const [name, [, shape]] of Object.entries(inventory)) {
    const rows = manifest.imports.filter(i => i.name === name);
    check(rows.length === 1 && rows[0].module === "lean.extern", `missing manifest import ${name}`);
    const op = rows[0].operation;
    check(op?.kind === "external" && op.declaration === name &&
      JSON.stringify(op.params) === JSON.stringify([...shape].map(c => kinds[c])) &&
      JSON.stringify(op.results) === '["object"]', `wrong typed signature for ${name}`);
    if (options) {
      const source = hostBoundary?.imports?.filter(row => row.declaration === name);
      check(source?.length === 1 && source[0].target === inventory[name][0] &&
        JSON.stringify(source[0].borrowedParameters) === JSON.stringify(borrowed[name]) &&
        source[0].physicalImport?.operation?.kind === op.kind &&
        source[0].physicalImport.operation.declaration === op.declaration &&
        JSON.stringify(source[0].physicalImport.operation.params) === JSON.stringify(op.params) &&
        JSON.stringify(source[0].physicalImport.operation.results) === JSON.stringify(op.results),
      `wrong source signature/borrow contract for ${name}`);
    }
  }

  let instance, memory, exports, disposed = false, reason = null, calls = 0;
  const resources = new Map();
  const callbackRoots = new Set();
  const leanRefs = new WeakMap();
  const retainedWords = new Set();
  const frames = [];
  const encoder = new TextEncoder();
  // Keep one reusable JavaScript-owned UTF-8 buffer per active conversion
  // depth. A slot stays leased while allocation runs because allocation may
  // reenter a host conversion; nested conversions must not overwrite it.
  const stringScratch = [];
  let stringScratchDepth = 0;
  const decoder = new TextDecoder("utf-8", { fatal: true });
  const live = () => check(!disposed && instance, reason ?? "session disposed");
  let cachedView;
  const view = () => {
    const buffer = memory.buffer;
    if (cachedView?.buffer !== buffer) cachedView = new DataView(buffer);
    return cachedView;
  };
  const header = word => {
    const p = word >>> 0, v = view();
    check(p >= 1024 && p % 8 === 0 && p + HEADER <= v.byteLength, "invalid heap object");
    // Fresh scalar snapshot: never share scratch or carry a view into a caller
    // that may invoke Wasm/providers/reentrant callbacks.
    const kind = v.getUint32(p, true), flags = v.getUint32(p + 4, true);
    const rc = v.getUint32(p + 8, true), extent = v.getUint32(p + 12, true);
    const aux0 = v.getUint32(p + 16, true), aux1 = v.getUint32(p + 20, true);
    const aux2 = v.getUint32(p + 24, true), aux3 = v.getUint32(p + 28, true);
    check((flags & 2) !== 0 && extent >= HEADER && extent % 8 === 0 &&
      p + extent <= v.byteLength, "invalid live extent");
    return { p, kind, flags, rc, extent, aux0, aux1, aux2, aux3 };
  };
  const allocate = bytes => {
    live();
    const size = align(bytes), p = exports.fir_heap_alloc(size) >>> 0;
    check(p >= 1024 && p % 8 === 0 && p + size <= memory.buffer.byteLength,
      "invalid allocation");
    new Uint8Array(memory.buffer, p, size).fill(0);
    return p;
  };
  const writeHeader = (p, kind, bytes, aux0 = 0, aux1 = 0, aux2 = 0, aux3 = 0, persistent = false) => {
    const v = view();
    v.setUint32(p, kind, true);
    v.setUint32(p + 4, persistent ? 3 : 2, true);
    v.setUint32(p + 8, persistent ? 0 : 1, true);
    v.setUint32(p + 12, bytes, true);
    v.setUint32(p + 16, aux0, true);
    v.setUint32(p + 20, aux1, true);
    v.setUint32(p + 24, aux2, true);
    v.setUint32(p + 28, aux3, true);
  };
  const ctor = (tag, fields) => {
    const size = HEADER + fields.length * 8, p = allocate(size);
    writeHeader(p, 1, size, tag, fields.length);
    const v = view();
    for (let i = 0; i < fields.length; i++) v.setUint32(p + HEADER + i * 8, fields[i], true);
    return p;
  };
  const resource = value => {
    // Persistent *opaque wrappers* have no Lean children. Keeping them and the
    // JS table until disposal prevents address-reuse/identity collisions.
    const p = allocate(HEADER);
    writeHeader(p, 8, HEADER, RESOURCE, resources.size + 1, 0, 0, true);
    resources.set(p, value);
    return p;
  };
  const resolve = word => {
    const { p, kind, aux0 } = header(word);
    check(kind === 8 && aux0 === RESOURCE && resources.has(p), "unknown JS resource");
    return resources.get(p);
  };
  const retainWord = (word, borrowed) => {
    const p = word >>> 0;
    if ((p & 1) === 0) {
      const { flags, rc } = header(p);
      if (borrowed && !(flags & 1)) {
        check(rc > 0 && rc < 0xffffffff, 'invalid retained reference count');
        view().setUint32(p + 8, rc + 1, true);
      }
    }
    retainedWords.add(p);
    return p;
  };
  const leanRef = word => {
    // The token exposes no address and is valid only in this session. Retain
    // one actual borrowed Lean reference; its children remain transitively live.
    const token = Object.freeze({});
    leanRefs.set(token, retainWord(word, true));
    leanObjectTokens.add(token);
    return token;
  };
  const readString = word => {
    const { p, kind, aux0, aux1: length, extent } = header(word);
    check(kind === 4 && aux0 === 1 && HEADER + length <= extent, "expected UTF-8 String");
    return decoder.decode(new Uint8Array(memory.buffer, p + HEADER, length));
  };
  const string = value => {
    check(typeof value === "string", "expected JS string");
    const scratchIndex = stringScratchDepth++;
    try {
      // Three bytes per UTF-16 code unit is sufficient even for unmatched
      // surrogates; a surrogate pair consumes four bytes for two code units.
      const capacity = Math.max(256, value.length * 3);
      let scratch = stringScratch[scratchIndex];
      if (scratch === undefined || scratch.length < capacity)
        scratch = stringScratch[scratchIndex] = new Uint8Array(capacity);
      const encoded = encoder.encodeInto(value, scratch);
      check(encoded.read === value.length, "incomplete UTF-8 encoding");
      const length = encoded.written;
      const size = align(HEADER + length), p = allocate(size);
      // Allocation may grow memory or reenter JavaScript. Acquire every Wasm
      // view and write the complete header only after it returns.
      writeHeader(p, 4, size, 1, length);
      new Uint8Array(memory.buffer, p + HEADER, length)
        .set(scratch.subarray(0, length));
      return p;
    } finally {
      stringScratchDepth = scratchIndex;
    }
  };
  const result = word => {
    const { p, kind, aux0: tag, aux1, aux2, aux3 } = header(word);
    check(kind === 1 && aux1 === 1 && aux2 === 0 && aux3 === 0,
      "malformed IO result");
    check(tag === 0 || tag === 1, "invalid IO result tag");
    return { failed: tag === 1, word: view().getUint32(p + HEADER, true) };
  };
  const dispose = () => {
    if (disposed) return false;
    disposed = true;
    resources.clear(); callbackRoots.clear(); retainedWords.clear();
    stringScratch.length = 0;
    instance = null; exports = null; memory = null; cachedView = null;
    return true;
  };
  const guarded = action => {
    live();
    try { return action(); }
    catch (error) {
      reason = "session invalidated by ABI or Wasm failure";
      dispose();
      throw error;
    }
  };
  const call = (entry, args, logical = false) => {
    const kind = logical === true ? 'unit' : logical === false ? 'js' : logical;
    const outcome = guarded(() => {
      const frame = { failed: false, error: undefined };
      frames.push(frame);
      try {
        check(typeof exports[entry] === "function", `missing export ${entry}`);
        const frontier = exports.fir_heap_frontier() >>> 0;
        exports.fir_heap_set_frontier(frontier);
        const { failed, word } = result(exports[entry](...args, 0));
        calls++;
        if (failed) {
          return { failed: true, error: frame.failed ? frame.error : new Error("Lean action returned an error") };
        }
        check(!frame.failed, "host error was converted to IO success");
        if (kind === 'unit') check(word === UNIT, "callback did not return Unit");
        if (kind === 'bool') check(word === 1 || word === 3, 'malformed compiled Bool result');
        return { failed: false, value: kind === 'unit' ? undefined :
          kind === 'bool' ? word === 3 : kind === 'string' ? readString(word) :
          kind === 'codec-word' ? word : resolve(word) };
      } finally {
        check(frames.pop() === frame, "corrupt JS entry frame");
      }
    });
    // Rethrow outside the structural guard, including `throw undefined`.
    // Reentrant callbacks have already popped their own frame at this point.
    if (outcome.failed) throw outcome.error;
    return outcome.value;
  };
  const callback = word => {
    const { p, kind } = header(word);
    check(kind === 2, "expected transferred Lean closure");
    // ofUnary transfers an owned reference. We retain it without a decrement;
    // invokeUnary borrows it, so nested captures remain valid between calls.
    callbackRoots.add(p);
    return argument => call(prefix + (options ? 'invokeVoid' : 'invokeUnary'), [0, p, guarded(() => resource(argument))], true);
  };
  const functionCallback = word => {
    const { p, kind } = header(word);
    check(kind === 2, 'expected transferred unary function closure');
    retainWord(p, false); callbackRoots.add(p);
    return argument => call(prefix + 'invokeFunction', [0, 0, p, guarded(() => resource(argument))]);
  };
  const memoCallback = word => {
    const { p, kind } = header(word);
    check(kind === 2, 'expected transferred memo action closure');
    retainWord(p, false); callbackRoots.add(p);
    return () => call(prefix + 'invokeMemo', [0, p]);
  };
  const nullaryCallback = word => {
    const { p, kind } = header(word);
    check(kind === 2, 'expected transferred nullary function closure');
    retainWord(p, false); callbackRoots.add(p);
    return () => call(prefix + 'invokeNullary', [0, p]);
  };
  const codecCall = (name, args = []) => call('FirVbpCodecSdk.' + name, args, 'codec-word');
  const codecPayload = (target, value) => {
    check(value !== null && typeof value === 'object', 'malformed codec provider result');
    if (target === 'jsonValue.check') {
      if (value.kind === 'ok') { check(value.value === null, 'malformed codec check Unit'); return codecCall('checkOk'); }
      check(value.kind === 'error' && typeof value.value === 'string', 'malformed codec check Except');
      return codecCall('checkError', [string(value.value)]);
    }
    switch (value.kind) {
      case 'null': return codecCall('viewNull');
      case 'bool': check(typeof value.value === 'boolean', 'malformed codec Bool');
        return codecCall('viewBool', [value.value ? 1 : 0]);
      case 'string': check(typeof value.value === 'string', 'malformed codec String');
        return codecCall('viewString', [string(value.value)]);
      case 'integer': {
        const n = value.value;
        check(typeof n === 'bigint' && n >= -9007199254740991n && n <= 9007199254740991n, 'malformed codec integer');
        return codecCall('viewInteger', [n < 0n ? -n : n, n < 0n ? 1 : 0]);
      }
      case 'array': {
        check(Array.isArray(value.value), 'malformed codec array');
        let array = codecCall('arrayEmpty');
        for (const child of value.value) array = codecCall('arrayPush', [array, resource(child)]);
        return codecCall('viewArray', [array]);
      }
      case 'object': {
        check(Array.isArray(value.value), 'malformed codec fields');
        let fields = codecCall('fieldsEmpty');
        for (const field of value.value) {
          check(field !== null && typeof field === 'object' && typeof field.fst === 'string' &&
            Object.hasOwn(field, 'snd'), 'malformed codec field');
          fields = codecCall('fieldsPush', [fields, string(field.fst), resource(field.snd)]);
        }
        return codecCall('viewObject', [fields]);
      }
      default: throw new Error('unreviewed codec View constructor');
    }
  };
  const effectCallbacks = word => {
    const { p, kind } = header(word);
    check(kind === 1, 'expected transferred LeanEffect value');
    retainWord(p, false); callbackRoots.add(p);
    // No field-offset decoding: the compiled source selects setup/cleanup.
    return Object.freeze({
      setup: () => call(prefix + 'invokeEffectSetup', [0, p]),
      cleanup: value => call(prefix + 'invokeEffectCleanup', [0, p, guarded(() => resource(value))], true),
    });
  };
  const importObject = {};
  for (const [name, [target, shape]] of Object.entries(inventory)) {
    importObject[name] = (...args) => guarded(() => {
      check(args.length === shape.length, `wrong arity for ${name}`);
      const values = [];
      for (let i = 0; i < shape.length; i++) {
        const x = args[i];
        switch (shape[i]) {
          case "_": break;
          case "j": values.push(resolve(x)); break;
          case "s": values.push(readString(x)); break;
          case "b": check(x === 0 || x === 1, "invalid Bool"); values.push(x !== 0); break;
          case "f": values.push(x); break;
          case "c": values.push(callback(x)); break;
          case 'u': values.push(functionCallback(x)); break;
          case 'm': values.push(memoCallback(x)); break;
          case 'e': values.push(effectCallbacks(x)); break;
          case 'r': values.push(leanRef(x)); break;
          case 'n': values.push(nullaryCallback(x)); break;
          default: throw new Error("unreviewed import shape");
        }
      }
      let value;
      try {
        if (options && target === 'js.leanRef') value = values[0];
        else if (options && target === 'js.leanRef.value') {
          check(leanRefs.has(values[0]), 'invalid or foreign LeanRef token');
          value = retainWord(leanRefs.get(values[0]), true);
        } else value = providers[target](...values);
      } catch (error) {
        // Only the provider invocation is recoverable. A nested ABI/Wasm
        // failure already disposed the session and must not be laundered.
        if (disposed) throw error;
        const frame = frames.at(-1);
        check(frame && !frame.failed, "provider failure outside a fresh effectful entry");
        frame.failed = true;
        frame.error = error;
        return exports[prefix + "providerError"](string("JavaScript provider exception"), 0);
      }
      if (target === "js.string") check(typeof value === "string", "malformed String host result");
      if (target === "js.bool") check(typeof value === "boolean", "malformed Bool host result");
      if (target === "js.undefinedOr.isUndefined" || target === 'js.nullable.isNull')
        check(typeof value === "boolean", "malformed JS Bool host result");
      if (target === "js.float" || target === "js.array.push")
        check(typeof value === "number", "malformed numeric host result");
      if (target === "js.array.empty") check(Array.isArray(value), "malformed Array host result");
      if (target === "js.object.empty")
        check(value !== null && typeof value === "object" && !Array.isArray(value), "malformed Object host result");
      if (['js.value.react.callback', 'js.value.function.unary', 'js.value.function.nullary',
        'js.value.function.unaryVoid', 'js.value.react.memoCalculation', 'js.value.react.effectCallback'].includes(target))
        check(typeof value === "function", "malformed callback host result");
      if (['js.object.set', 'js.construction.field', 'js.construction.element', 'js.function.callVoid', 'react.useEffect', 'react.state.modify'].includes(target))
        check(value === undefined, "malformed Unit host result");
      if (configured && target === 'js.float.value') {
        check(typeof value === 'number', 'malformed Float host result');
        // Lean itself constructs IO.Result and the resident Float box. No JS
        // guessed scalar layout, integer conversion, or decimal round trip.
        return exports[prefix + 'providerFloat'](value, 0);
      }
      // Object.set returns Lean Unit; Array.push instead returns Js Float,
      // including the actual JS array length. Do not erase that distinction.
      // Object.get always roots its raw value, including undefined and null.
      // isUndefined returns Js Bool; only toBool produces a Lean Bool payload.
      const payload = codec && ['jsonValue.check', 'jsonValue.inspect'].includes(target) ? codecPayload(target, value) :
        ['js.object.set', 'js.construction.field', 'js.construction.element', 'js.function.callVoid', 'react.useEffect', 'react.state.modify'].includes(target) ? UNIT :
        name === "Lean.Vir.JsValue.toBool" ? leanBoolPayload(value) :
        options && target === 'js.string.value' ? string(value) :
        options && target === 'js.leanRef.value' ? value : resource(value);
      return ctor(0, [payload]);
    });
  }
  instance = await WebAssembly.instantiate(module, { "lean.extern": importObject });
  exports = instance.exports; memory = exports.memory;
  check(memory instanceof WebAssembly.Memory, "expected module-owned memory");
  for (const name of ["fir_heap_alloc", "fir_heap_frontier", "fir_heap_set_frontier",
    prefix + (options ? 'invokeFunction' : 'invokeUnary'), prefix + "providerError"])
    check(typeof exports[name] === "function", `missing export ${name}`);


  let directParsed, directEquivalent;
  if (codec && constructorLayouts) {
    const validateWord = word => {
      check(Number.isInteger(word) && word >= 0 && word <= 0xffffffff, 'invalid construction word');
      if (!(word & 1)) header(word);
      return word;
    };
    const raw = (name,args) => guarded(() => {
      check(typeof exports[name] === 'function', 'missing construction export '+name);
      return exports[name](...args);
    });
    const validateToken = token => {
      live();
      if (!leanRefs.has(token)) throw new TypeError('invalid or foreign construction token');
      validateWord(leanRefs.get(token));
      return token;
    };
    const ownedIo = (name,args) => guarded(() => {
      const signature = {
        'FirVbpDirectSinkSdk.natural': 1, 'FirVbpDirectSinkSdk.integer': 2,
        'FirVbpDirectSinkArraySdk.empty': 1, 'FirVbpDirectSinkArraySdk.push': 3
      };
      check(Object.hasOwn(signature,name) && args.length === signature[name] &&
        exports[name]?.length === args.length+1, 'wrong compiled construction ABI '+name);
      const wrapper = exports[name](...args,0);
      const decoded = result(wrapper); // View acquired only after Wasm returned.
      check(!decoded.failed, 'unexpected pure construction IO failure');
      validateWord(decoded.word);
      exports.fir_sink_retain(decoded.word);
      exports.fir_sink_release(wrapper);
      return decoded.word;
    });
    const sink = createFirConstructionRuntime({
      isLive: () => !disposed && instance !== null,
      raw, ownedIo, validateWord,
      string: value => guarded(() => string(value)),
      retain: word => guarded(() => { validateWord(word); raw('fir_sink_retain',[word]); }),
      release: word => guarded(() => { validateWord(word); raw('fir_sink_release',[word]); }),
      token: word => guarded(() => { validateWord(word); return leanRef(word); }),
      validateToken,
      tokenWord: token => leanRefs.get(validateToken(token)),
      hook: (name,value) => call(name,[guarded(() => resource(value))])
    },constructorLayouts);
    directParsed = createFirDirectPreviewDecoder(sink,constructorLayouts,providers);
    directEquivalent = (left,right) => {
      validateToken(left); validateToken(right);
      return call(CODEC_PREFIX+'equivalent',[resource(left),resource(right)],'bool');
    };
  }
  if (options) {
    check(memory.buffer.byteLength >= FLOAT_FORMAT_RESERVED_BYTES,
      'native scratch/stack reservation exceeds initial memory');
    check(exports.fir_heap_frontier() === 1024, 'unexpected pre-reservation FIR allocation');
    exports.fir_heap_set_frontier(FLOAT_FORMAT_RESERVED_BYTES);
    check(exports.fir_heap_frontier() === FLOAT_FORMAT_RESERVED_BYTES,
      'native low-memory reservation was not installed');
    for (const [name, [params]] of Object.entries(callbackAbi))
      check(exports[prefix + name]?.length === params.length, `wrong physical callback arity for ${name}`);
    if (codec) {
      for (const [name, [params]] of Object.entries(CODEC_ENTRY_ABI))
        check(exports[name]?.length === params.length, `wrong source entry arity for ${name}`);
      for (const [name, [params]] of Object.entries(CODEC_CONSTRUCTOR_ABI))
        check(exports['FirVbpCodecSdk.' + name]?.length === params.length + 1, `wrong codec constructor arity for ${name}`);
    }
    for (const name of ['invokeMemo', ...(codec ? ['invokeNullary'] : ['invokeEffectSetup', 'invokeEffectCleanup']), 'invokeVoid',
      'retainedFunction', 'readBoolean', 'readString', 'produceUnit'])
      check(typeof exports[prefix + name] === 'function', `missing SDK export ${name}`);
    return Object.freeze({
      ...(codec ? {
        ...(directParsed ? { directParsed, equivalent: directEquivalent } : {}),
        browserParsed: input => call(CODEC_PREFIX + 'browserParsed', [guarded(() => resource(input))]),
        createTimedView: () => call(CODEC_PREFIX + 'createTimedView', []),
        renderTimedDecoded: (component, decoded, requested, received, notified, decodedAt) =>
          call(CODEC_PREFIX + 'renderTimedDecoded', guarded(() => {
            check([requested,received,notified].every(value => value === undefined || typeof value === 'number') &&
              typeof decodedAt === 'number', 'expected native Number|undefined timing and required decodedAt Number');
            return [component,decoded,requested,received,notified,decodedAt].map(value => resource(value));
          })),
        isLeanObjectHandle: isFirLeanObjectHandle,
      } : {}),
      retainedFunction: message => call(prefix + 'retainedFunction', [guarded(() => string(message))]),
      readBoolean: value => call(prefix + 'readBoolean', [guarded(() => resource(value))], 'bool'),
      readString: value => call(prefix + 'readString', [guarded(() => resource(value))], 'string'),
      unitProbe: () => call(prefix + 'produceUnit', [], true),
      stats: () => ({ disposed, reason, calls, resources: resources.size,
        callbacks: callbackRoots.size, retainedWords: retainedWords.size,
        nativeReservedMemoryBytes: FLOAT_FORMAT_RESERVED_BYTES,
        frontier: memory ? exports.fir_heap_frontier() >>> 0 : null }),
      dispose,
    });
  }

  // First executable host acceptance surface. A full consumer Document encoder
  // is intentionally separate; no second VBP schema is invented here.
  return Object.freeze({
    renderDocumentJson: source => call(PREFIX + "renderDocumentJson", [guarded(() => string(source))]),
    renderDocument: title => call(PREFIX + "renderDocument", [guarded(() => string(title))]),
    retainedCallback: message => call(PREFIX + "retainedCallback", [guarded(() => string(message))]),
    bindingFixture: (message, flag, number) => {
      const args = guarded(() => {
        check(typeof flag === "boolean" && typeof number === "number", "invalid scalar inputs");
        return [string(message), flag ? 1 : 0, number];
      });
      return call(PREFIX + "bindingFixture", args);
    },
    stats: () => ({ disposed, reason, calls, resources: resources.size,
      callbacks: callbackRoots.size, frontier: memory ? exports.fir_heap_frontier() >>> 0 : null }),
    dispose,
  });
}
