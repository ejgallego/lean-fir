import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { basename, dirname, join } from "node:path";

const MAX_TAGGED_PAYLOAD = 9223372036854775807n;
const OBJECT_KINDS = new Set(["object", "tagged", "tobject"]);

class SemanticHost {
  constructor() {
    this.nextHandle = 1;
    this.handles = new Map();
    this.valueHandles = new Map();
    this.nextLocation = 0;
    this.heap = [];
    this.world = 0;
    this.trace = [];
  }

  valueKey(value) {
    switch (value.kind) {
      case "tagged":
        return `tagged:${value.payload}`;
      case "heap":
        return `heap:${value.location}`;
      case "erased":
        return "erased";
      case "reuseToken":
        return `reuseToken:${value.location ?? "none"}`;
      default:
        throw new Error(`value has no handle representation: ${value.kind}`);
    }
  }

  accepts(kind, value) {
    switch (kind) {
      case "object":
        return value.kind === "heap";
      case "tagged":
        return value.kind === "tagged";
      case "tobject":
        return value.kind === "tagged" || value.kind === "heap";
      case "erased":
        return value.kind === "erased";
      case "reuseToken":
        return value.kind === "reuseToken";
      default:
        return false;
    }
  }

  encode(kind, value) {
    if (kind === "erased") {
      assert.equal(value.kind, "erased", "erased result has the wrong semantic kind");
      return 0;
    }
    assert.ok(OBJECT_KINDS.has(kind) || kind === "reuseToken", `unsupported handle kind: ${kind}`);
    assert.ok(this.accepts(kind, value), `${value.kind} does not refine ${kind}`);
    const key = this.valueKey(value);
    const existing = this.valueHandles.get(key);
    if (existing !== undefined) {
      return existing;
    }
    assert.ok(this.nextHandle <= 0xffffffff, "FIR handle space exhausted");
    const handle = this.nextHandle++;
    this.handles.set(handle, value);
    this.valueHandles.set(key, handle);
    return handle;
  }

  decode(kind, physical) {
    const handle = Number(physical) >>> 0;
    if (kind === "erased") {
      assert.equal(handle, 0, "erased sentinel must use handle zero");
      return { kind: "erased" };
    }
    assert.notEqual(handle, 0, `${kind} cannot use the reserved handle`);
    const value = this.handles.get(handle);
    assert.ok(value, `unknown FIR handle ${handle}`);
    assert.ok(this.accepts(kind, value), `handle ${handle} does not refine ${kind}`);
    return value;
  }

  alloc(object, persistent = false) {
    const location = this.nextLocation++;
    const cell = {
      location,
      rc: persistent ? 0 : 1,
      persistent,
      live: true,
      object,
    };
    this.heap.unshift(cell);
    return { kind: "heap", location };
  }

  literal(operation) {
    if (operation.kind === "naturalLiteral") {
      const payload = BigInt(operation.value);
      const value = payload <= MAX_TAGGED_PAYLOAD
        ? { kind: "tagged", payload }
        : this.alloc({ kind: "natural", value: payload });
      return this.encode(operation.result, value);
    }
    if (operation.kind === "stringLiteral") {
      const value = this.alloc({ kind: "string", value: operation.value });
      return this.encode(operation.result, value);
    }
    throw new Error(`unsupported literal operation: ${operation.kind}`);
  }

  allocCtor(operation, physicalArgs) {
    assert.equal(physicalArgs.length, operation.fields.length, "constructor host arity mismatch");
    assert.equal(operation.size, operation.fields.length, "constructor manifest size mismatch");
    const fields = operation.fields.map((kind, index) => this.decode(kind, physicalArgs[index]));
    const tag = BigInt(operation.tag);
    const value = operation.size === 0 && operation.usize === 0 && operation.ssize === 0
      ? { kind: "tagged", payload: tag }
      : this.alloc({
          kind: "ctor",
          tag,
          objectFields: fields,
          usizeFields: Array.from({ length: operation.usize }, () => 0n),
          scalarFields: [],
        });
    return this.encode(operation.result, value);
  }

  objectProj(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "object projection host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    assert.equal(source.kind, "heap", "object projection expected a heap constructor");
    const cell = this.liveCell(source.location);
    assert.equal(cell.object.kind, "ctor", "object projection expected a constructor");
    const value = cell.object.objectFields[operation.index];
    assert.ok(value, `object field ${operation.index} is out of bounds`);
    return this.encode(operation.result, value);
  }

  getTag(physicalArgs) {
    assert.equal(physicalArgs.length, 1, "getTag host arity mismatch");
    const value = this.decode("tobject", physicalArgs[0]);
    let tag;
    if (value.kind === "tagged") {
      tag = value.payload;
    } else {
      const cell = this.liveCell(value.location);
      assert.equal(cell.object.kind, "ctor", "getTag expected a constructor");
      tag = cell.object.tag;
    }
    return Number(BigInt.asUintN(32, tag));
  }

  liveCell(location) {
    const cell = this.heap.find((candidate) => candidate.location === location);
    assert.ok(cell?.live, `dead or unknown FIR heap location ${location}`);
    return cell;
  }

  importFunction(operation) {
    switch (operation.kind) {
      case "naturalLiteral":
      case "stringLiteral":
        return (...args) => {
          assert.equal(args.length, 0, "literal host arity mismatch");
          return this.literal(operation);
        };
      case "allocCtor":
        return (...args) => this.allocCtor(operation, args);
      case "objectProj":
        return (...args) => this.objectProj(operation, args);
      case "getTag":
        return (...args) => this.getTag(args);
      default:
        throw new Error(`unsupported A0 host operation: ${operation.kind}`);
    }
  }

  imports(manifestImports) {
    const imports = {};
    for (const descriptor of manifestImports) {
      imports[descriptor.module] ??= {};
      assert.equal(imports[descriptor.module][descriptor.name], undefined,
        `duplicate import ${descriptor.module}.${descriptor.name}`);
      imports[descriptor.module][descriptor.name] = this.importFunction(descriptor.operation);
    }
    return imports;
  }

  valueJson(value) {
    switch (value.kind) {
      case "tagged":
        return {
          kind: "object",
          reference: { kind: "tagged", payload: value.payload.toString() },
        };
      case "heap":
        return {
          kind: "object",
          reference: { kind: "heap", location: value.location },
        };
      case "usize":
        return { kind: "usize", value: value.value.toString() };
      case "scalar":
        return {
          kind: "scalar",
          scalar: { kind: value.scalarKind, value: value.value.toString() },
        };
      case "erased":
        return { kind: "erased" };
      case "reuseToken":
        return { kind: "reuseToken", location: value.location ?? null };
      default:
        throw new Error(`cannot observe semantic value kind ${value.kind}`);
    }
  }

  objectJson(object) {
    switch (object.kind) {
      case "ctor":
        return {
          kind: "ctor",
          tag: object.tag.toString(),
          objectFields: object.objectFields.map((value) => this.valueJson(value)),
          usizeFields: object.usizeFields.map((value) => value.toString()),
          scalarFields: object.scalarFields,
        };
      case "string":
        return { kind: "string", value: object.value };
      case "natural":
        return { kind: "natural", value: object.value.toString() };
      default:
        throw new Error(`cannot observe heap object kind ${object.kind}`);
    }
  }

  reachableLocations(root) {
    const pending = root.kind === "heap" ? [root.location] : [];
    const seen = new Set();
    while (pending.length > 0) {
      const location = pending.shift();
      if (seen.has(location)) {
        continue;
      }
      seen.add(location);
      const cell = this.liveCell(location);
      if (cell.object.kind === "ctor") {
        for (const value of cell.object.objectFields) {
          if (value.kind === "heap") {
            pending.unshift(value.location);
          }
        }
      }
    }
    return seen;
  }

  observation(resultKind, physicalResult) {
    const value = this.decode(resultKind, physicalResult);
    const reachable = this.reachableLocations(value);
    return {
      outcome: { kind: "returned", value: this.valueJson(value) },
      reachableHeap: this.heap
        .filter((cell) => reachable.has(cell.location))
        .map((cell) => ({
          location: cell.location,
          rc: cell.rc,
          persistent: cell.persistent,
          live: cell.live,
          object: this.objectJson(cell.object),
        })),
      world: this.world,
      trace: this.trace,
    };
  }
}

async function runArtifact(manifestPath) {
  const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
  const expectedPath = join(dirname(manifestPath), `${manifest.fixture}.expected.json`);
  const expected = JSON.parse(await readFile(expectedPath, "utf8"));
  const wasmPath = manifestPath.slice(0, -".json".length);
  const bytes = await readFile(wasmPath);
  assert.ok(WebAssembly.validate(bytes), `${basename(wasmPath)} failed standard WebAssembly validation`);

  const host = new SemanticHost();
  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const entry = instance.exports[manifest.entry];
  assert.equal(typeof entry, "function", `missing exported entry ${manifest.entry}`);
  const physicalResult = entry();
  const actual = host.observation(manifest.result, physicalResult);
  assert.deepStrictEqual(actual, expected, `${manifest.fixture} observation mismatch`);
  console.log(`PASS ${manifest.fixture}`);
}

const artifactDirectory = process.argv[2];
if (!artifactDirectory) {
  console.error("usage: node run-artifacts.mjs <artifact-directory>");
  process.exit(2);
}

const manifests = (await readdir(artifactDirectory))
  .filter((name) => name.endsWith(".wasm.json"))
  .sort();
assert.ok(manifests.length > 0, `no .wasm.json manifests found in ${artifactDirectory}`);
for (const manifest of manifests) {
  await runArtifact(join(artifactDirectory, manifest));
}
