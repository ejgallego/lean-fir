import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";

import {
  LEAN_COMPONENT_RUNTIME_PROVIDER_API,
  VBP_VERSO_VIEWER_ADAPTER_API_VERSION,
  VBP_VERSO_VIEWER_HOST_IMPORTS,
  VBP_VERSO_VIEWER_MOUNT_ENTRY,
  VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
  createVbpVersoViewerComponentRuntimeProvider,
} from "./vbp-verso-viewer-browser-adapter.mjs";

const bytes = readFileSync(new URL("./vbp-verso-viewer.wasm", import.meta.url));
const manifest = JSON.parse(readFileSync(
  new URL("./vbp-verso-viewer.wasm.json", import.meta.url), "utf8"));
const build = JSON.parse(readFileSync(
  new URL("./BUILD.json", import.meta.url), "utf8"));
const inventoryBytes = readFileSync(
  new URL("./runtime-inventory.json", import.meta.url));
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

function rpcJsonFromValue(value, depth = 0) {
  assert.ok(depth <= 64, "smoke RpcJson nesting is bounded");
  if (value === null) return { kind: "null" };
  if (typeof value === "boolean") return { kind: "bool", value };
  if (typeof value === "string") return { kind: "string", value };
  if (Array.isArray(value)) {
    return { kind: "array",
      value: value.map((item) => rpcJsonFromValue(item, depth + 1)) };
  }
  assert.equal(typeof value, "object", "smoke payload must be JSON-like");
  return { kind: "object", value: Object.entries(value).map(([fst, snd]) =>
    ({ fst, snd: rpcJsonFromValue(snd, depth + 1) })) };
}

function createFakeHost() {
  const roots = new Map();
  const effects = [];
  const events = [];
  const resources = [];

  function resource(kind, value) {
    const result = {
      kind,
      value,
      released: false,
      release() {
        if (this.released) return false;
        this.released = true;
        return true;
      },
    };
    resources.push(result);
    return result;
  }

  function valueOf(item) {
    assert.equal(typeof item, "object");
    assert.notEqual(item, null);
    return item.value;
  }

  const hostBindings = {
    "js.string": (value) => resource("string", value),
    "js.bool.value": (value) => Boolean(valueOf(value)),
    "js.float.value": (value) => Number(valueOf(value)),
    "js.string.value": (value) => String(valueOf(value)),
    "js.nat.value": (value) => BigInt(valueOf(value)),
    "js.value.react.property": (value) => resource("property", value),
    "js.value.react.eventHandler": (value) => resource("eventHandler", value),
    "js.array.empty": () => resource("array", []),
    "js.array.push": (array, item) => {
      valueOf(array).push(item);
      return array;
    },
    "react.props.empty": () => resource("props", {
      key: null, ref: null, properties: [], handlers: [],
    }),
    "react.props.setKey": (props, key) => {
      valueOf(props).key = key;
      return undefined;
    },
    "react.props.setRef": (props, ref) => {
      valueOf(props).ref = ref;
      return undefined;
    },
    "react.props.setProperty": (props, property) => {
      valueOf(props).properties.push(valueOf(property));
      return undefined;
    },
    "react.props.setEventHandler": (props, handler) => {
      valueOf(props).handlers.push(valueOf(handler));
      events.push(valueOf(handler));
      return undefined;
    },
    "react.elementType.tag": (tag) => resource("elementType", valueOf(tag)),
    "react.node.text": (text) => resource("node", {
      type: "text", text: valueOf(text),
    }),
    "react.node.createElement": (type, props, children) => resource("node", {
      type: valueOf(type), props: valueOf(props), children: valueOf(children),
    }),
    "react.node.fragment": (props, children) => resource("node", {
      type: "fragment", props: valueOf(props), children: valueOf(children),
    }),
    "react.node.component": (type, component) => resource("node", {
      type: valueOf(type), component, rendered: component(),
    }),
    "browser.performance.now": () => resource("float", 1.25),
    "browser.performance.usedHeapBytes": () => resource("nullable", null),
    "browser.performance.heapLimitBytes": () => resource("nullable", null),
    "react.useRef": (initial) => resource("ref", { current: initial }),
    "react.ref.get": (ref) => valueOf(ref).current,
    "react.ref.set": (ref, value) => {
      valueOf(ref).current = value;
      return undefined;
    },
    "react.deps.empty": () => resource("deps", []),
    "react.deps.push": (deps, value) => {
      valueOf(deps).push(value);
      return undefined;
    },
    "react.useLeanEffect": (setup) => {
      effects.push(setup());
      return undefined;
    },
    "react.useLeanEffectWithDeps": (_deps, setup) => {
      effects.push(setup());
      return undefined;
    },
    "react.useState": (initial) => {
      const state = { value: initial };
      state.setter = resource("stateSetter", state);
      return resource("stateTuple", state);
    },
    "react.stateTuple.value": (tuple) => valueOf(tuple).value,
    "react.stateTuple.setter": (tuple) => valueOf(tuple).setter,
    "react.state.modify": (setter, update) => {
      valueOf(setter).value = update(valueOf(setter).value);
      return undefined;
    },
    "browser.event.currentTarget": (event) => valueOf(event).currentTarget,
    "browser.event.target": (event) => valueOf(event).target,
    "js.nullable.isNull": (value) =>
      resource("bool", valueOf(value) === null),
    "js.nullable.value": (value) => {
      assert.notEqual(valueOf(value), null);
      return resource("nullableValue", valueOf(value));
    },
    "browser.htmlInputElement.fromElement": (element) =>
      resource("nullable", valueOf(element)),
    "browser.htmlInputElement.getChecked": (input) =>
      resource("bool", Boolean(valueOf(input).checked)),
    "react.root.renderComponentIntoSelector":
      (selector, componentType, component) => {
        const key = valueOf(selector);
        const previous = roots.get(key);
        previous?.component?.release?.();
        roots.set(key, {
          componentType: valueOf(componentType),
          component,
          rendered: component(),
        });
        return resource("bool", true);
      },
    "react.root.unmountSelector": (selector) => {
      const key = valueOf(selector);
      const root = roots.get(key);
      root?.component?.release?.();
      return resource("bool", roots.delete(key));
    },
  };

  return { hostBindings, roots, effects, events, resources };
}

assert.equal(VBP_VERSO_VIEWER_ADAPTER_API_VERSION,
  "fir.vbp-verso-viewer.browser/v1");
assert.equal(build.wasm.sha256, sha256(bytes));
assert.equal(build.residentRuntime.inventory.sha256, sha256(inventoryBytes));
const module = await WebAssembly.compile(bytes);
const imports = WebAssembly.Module.imports(module);
assert.equal(imports.length, VBP_VERSO_VIEWER_HOST_IMPORTS.length);
assert.deepEqual(imports.map(({ module: namespace, name, kind }) =>
  ({ module: namespace, name, kind })), build.wasm.imports);
assert.deepEqual(WebAssembly.Module.exports(module), build.wasm.exports);

const fake = createFakeHost();
const provider = createVbpVersoViewerComponentRuntimeProvider({
  module, manifest, build,
});
assert.equal(provider.apiVersion, LEAN_COMPONENT_RUNTIME_PROVIDER_API);
const runtime = await provider.open({ hostBindings: fake.hostBindings });
assert.deepEqual(runtime.describeEntry(VBP_VERSO_VIEWER_MOUNT_ENTRY), {
  entry: VBP_VERSO_VIEWER_MOUNT_ENTRY,
  params: ["String", "Lean.Vir.Infoview.RpcJson"],
  result: "Bool",
  effect: "DomM",
});

const first = rpcJsonFromValue({
  loading: { message: "FIR smoke payload λ 日本語" },
});
const second = rpcJsonFromValue({
  loading: { message: "FIR smoke update two" },
});
assert.equal(runtime.invoke(VBP_VERSO_VIEWER_MOUNT_ENTRY,
  ["#preview", first]), true);
assert.equal(fake.roots.has("#preview"), true);
const firstCall = runtime.lastCall;
assert.ok(firstCall.memory.frontierAfter >= firstCall.memory.frontierBefore);
assert.equal(runtime.invoke(VBP_VERSO_VIEWER_MOUNT_ENTRY,
  ["#preview", second]), true);
assert.equal(fake.roots.size, 1);
assert.equal(runtime.invoke(VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
  ["#preview"]), true);
assert.equal(fake.roots.size, 0);
for (const cleanup of fake.effects) cleanup?.();
const lastCall = runtime.lastCall;
assert.equal(runtime.dispose(), true);
assert.equal(runtime.dispose(), false);
assert.throws(() => runtime.invoke(VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
  ["#preview"]), /disposed or invalid/);

for (const field of ["fetchMs", "compileMs", "instantiateMs", "totalMs",
  "overheadMs"]) {
  assert.ok(Number.isFinite(runtime.initialization[field]), field);
}
for (const field of ["encodeMs", "executeMs", "decodeMs", "totalMs",
  "overheadMs"]) {
  assert.ok(Number.isFinite(lastCall.timings[field]), field);
}

console.log(JSON.stringify({
  ok: true,
  mounts: 2,
  unmounts: 1,
  effects: fake.effects.length,
  eventHandlers: fake.events.length,
  hostResources: fake.resources.length,
  imports: imports.length,
  exports: WebAssembly.Module.exports(module),
  initialization: runtime.initialization,
  firstCall,
  lastCall,
}, null, 2));
