import assert from "node:assert/strict";

const MAX_TAGGED_PAYLOAD = 9223372036854775807n;
const OBJECT_KINDS = new Set(["object", "tagged", "tobject"]);
const SCALAR_KINDS = new Set(["uint8", "uint16", "uint32", "uint64"]);

function scalarTypeRepr(kind) {
  const typeName = kind === "usize"
    ? "USize"
    : kind === "uint8"
      ? "UInt8"
      : kind === "uint16"
        ? "UInt16"
        : kind === "uint32"
          ? "UInt32"
          : kind === "uint64"
            ? "UInt64"
            : undefined;
  assert.ok(typeName, `unsupported boxed scalar kind: ${kind}`);
  return `Lean.Expr.const \`${typeName} []`;
}

export class SemanticFault extends Error {
  constructor(fault) {
    super(`FIR semantic fault: ${fault.kind}`);
    this.fault = fault;
  }
}

export function manifestValue(argument) {
  assert.ok(argument && typeof argument === "object", "manifest argument must be an object");
  switch (argument.kind) {
    case "tagged":
      return { kind: "tagged", payload: BigInt(argument.payload) };
    case "usize":
      return { kind: "usize", value: BigInt(argument.value) };
    case "scalar":
      assert.ok(SCALAR_KINDS.has(argument.scalarKind),
        `unsupported manifest scalar kind: ${argument.scalarKind}`);
      return {
        kind: "scalar",
        scalarKind: argument.scalarKind,
        value: BigInt(argument.value),
      };
    case "erased":
      return { kind: "erased" };
    case "heap":
      assert.ok(Number.isSafeInteger(argument.location) && argument.location >= 0,
        "heap argument location must be a nonnegative safe integer");
      return { kind: "heap", location: argument.location };
    case "reuseToken":
      assert.ok(argument.location === null ||
        (Number.isSafeInteger(argument.location) && argument.location >= 0),
        "reuse-token location must be null or a nonnegative safe integer");
      return { kind: "reuseToken", location: argument.location };
    default:
      throw new Error(`unsupported manifest argument kind: ${argument.kind}`);
  }
}

function runtimeScalarValue(value) {
  assert.ok(value && typeof value === "object", "runtime scalar value must be an object");
  assert.ok(SCALAR_KINDS.has(value.kind), `unsupported runtime scalar kind: ${value.kind}`);
  return { scalarKind: value.kind, value: BigInt(value.value) };
}

function runtimeValue(value) {
  assert.ok(value && typeof value === "object", "runtime value must be an object");
  switch (value.kind) {
    case "object":
      assert.ok(value.reference && typeof value.reference === "object",
        "runtime object reference must be an object");
      if (value.reference.kind === "tagged") {
        return { kind: "tagged", payload: BigInt(value.reference.payload) };
      }
      if (value.reference.kind === "heap") {
        assert.ok(Number.isSafeInteger(value.reference.location) && value.reference.location >= 0,
          "runtime heap location must be a nonnegative safe integer");
        return { kind: "heap", location: value.reference.location };
      }
      throw new Error(`unsupported runtime object reference: ${value.reference.kind}`);
    case "usize":
      return { kind: "usize", value: BigInt(value.value) };
    case "scalar": {
      const scalar = runtimeScalarValue(value.scalar);
      return { kind: "scalar", ...scalar };
    }
    case "erased":
      return { kind: "erased" };
    case "reuseToken":
      return { kind: "reuseToken", location: value.location };
    default:
      throw new Error(`unsupported initial-runtime value: ${value.kind}`);
  }
}

function runtimeHeapObject(object) {
  assert.ok(object && typeof object === "object", "runtime heap object must be an object");
  switch (object.kind) {
    case "ctor":
      assert.ok(Array.isArray(object.objectFields), "constructor objectFields must be an array");
      assert.ok(Array.isArray(object.usizeFields), "constructor usizeFields must be an array");
      assert.ok(Array.isArray(object.scalarFields), "constructor scalarFields must be an array");
      return {
        kind: "ctor",
        tag: BigInt(object.tag),
        objectFields: object.objectFields.map(runtimeValue),
        usizeFields: object.usizeFields.map(BigInt),
        scalarFields: object.scalarFields.map((field) => ({
          width: field.width,
          offset: field.offset,
          value: { kind: "scalar", ...runtimeScalarValue(field.value) },
        })),
      };
    case "string":
      assert.equal(typeof object.value, "string", "runtime string value must be a string");
      return { kind: "string", value: object.value };
    case "natural":
      return { kind: "natural", value: BigInt(object.value) };
    default:
      throw new Error(`unsupported initial-runtime heap object: ${object.kind}`);
  }
}

export class SemanticHost {
  constructor(initialRuntime = undefined, externalRegistry = undefined) {
    this.nextHandle = 1;
    this.handles = new Map();
    this.valueHandles = new Map();
    this.nextLocation = 0;
    this.heap = [];
    this.globals = new Map();
    this.world = 0;
    this.trace = [];
    this.externalRegistry = externalRegistry instanceof Map
      ? new Map(externalRegistry)
      : new Map(Object.entries(externalRegistry ?? {}));
    if (initialRuntime !== undefined) {
      this.loadInitialRuntime(initialRuntime);
    }
  }

  loadInitialRuntime(runtime) {
    assert.ok(runtime && typeof runtime === "object", "initialRuntime must be an object");
    assert.ok(Number.isSafeInteger(runtime.nextLocation) && runtime.nextLocation >= 0,
      "initialRuntime.nextLocation must be a nonnegative safe integer");
    assert.ok(Array.isArray(runtime.heap), "initialRuntime.heap must be an array");
    const locations = new Set();
    this.heap = runtime.heap.map((cell) => {
      assert.ok(cell && typeof cell === "object", "runtime heap cell must be an object");
      assert.ok(Number.isSafeInteger(cell.location) && cell.location >= 0,
        "runtime heap location must be a nonnegative safe integer");
      assert.ok(cell.location < runtime.nextLocation,
        `runtime heap location ${cell.location} is not below nextLocation`);
      assert.ok(!locations.has(cell.location), `duplicate runtime heap location ${cell.location}`);
      locations.add(cell.location);
      assert.ok(Number.isSafeInteger(cell.rc) && cell.rc >= 0,
        "runtime reference count must be a nonnegative safe integer");
      assert.equal(typeof cell.persistent, "boolean", "runtime persistent flag must be boolean");
      assert.equal(typeof cell.live, "boolean", "runtime live flag must be boolean");
      return {
        location: cell.location,
        rc: cell.rc,
        persistent: cell.persistent,
        live: cell.live,
        object: runtimeHeapObject(cell.object),
      };
    });
    this.nextLocation = runtime.nextLocation;
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
    switch (kind) {
      case "uint8":
      case "uint16":
      case "uint32": {
        assert.equal(value.kind, "scalar", `${kind} requires a scalar value`);
        assert.equal(value.scalarKind, kind, `${value.scalarKind} does not refine ${kind}`);
        const maximum = kind === "uint8" ? 0xffn : kind === "uint16" ? 0xffffn : 0xffffffffn;
        assert.ok(value.value >= 0n && value.value <= maximum,
          `${kind} argument is out of range: ${value.value}`);
        return Number(BigInt.asIntN(32, value.value));
      }
      case "uint64":
        assert.equal(value.kind, "scalar", "uint64 requires a scalar value");
        assert.equal(value.scalarKind, "uint64", `${value.scalarKind} does not refine uint64`);
        assert.ok(value.value >= 0n && value.value <= 0xffffffffffffffffn,
          `uint64 argument is out of range: ${value.value}`);
        return BigInt.asIntN(64, value.value);
      case "usize":
        assert.equal(value.kind, "usize", "usize requires a usize value");
        assert.ok(value.value >= 0n && value.value <= 0xffffffffffffffffn,
          `usize argument is out of range: ${value.value}`);
        return BigInt.asIntN(64, value.value);
      case "erased":
        assert.equal(value.kind, "erased", "erased has the wrong semantic kind");
        return 0;
      default:
        break;
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
    switch (kind) {
      case "uint8":
      case "uint16":
      case "uint32": {
        assert.equal(typeof physical, "number", `${kind} must use the WebAssembly i32 lane`);
        const value = Number(physical) >>> 0;
        if (kind === "uint8") {
          assert.ok(value <= 0xff, `uint8 result is out of range: ${value}`);
        } else if (kind === "uint16") {
          assert.ok(value <= 0xffff, `uint16 result is out of range: ${value}`);
        }
        return { kind: "scalar", scalarKind: kind, value: BigInt(value) };
      }
      case "uint64":
        assert.equal(typeof physical, "bigint", "uint64 must use the WebAssembly i64 lane");
        return {
          kind: "scalar",
          scalarKind: "uint64",
          value: BigInt.asUintN(64, physical),
        };
      case "usize":
        assert.equal(typeof physical, "bigint", "usize must use the WebAssembly i64 lane");
        return { kind: "usize", value: BigInt.asUintN(64, physical) };
      case "erased": {
        assert.equal(typeof physical, "number", "erased must use the WebAssembly i32 lane");
        const handle = Number(physical) >>> 0;
        assert.equal(handle, 0, "erased sentinel must use handle zero");
        return { kind: "erased" };
      }
      case "object":
      case "tagged":
      case "tobject":
      case "reuseToken": {
        assert.equal(typeof physical, "number", `${kind} must use the WebAssembly i32 lane`);
        const handle = Number(physical) >>> 0;
        assert.notEqual(handle, 0, `${kind} cannot use the reserved handle`);
        const value = this.handles.get(handle);
        assert.ok(value, `unknown FIR handle ${handle}`);
        assert.ok(this.accepts(kind, value), `handle ${handle} does not refine ${kind}`);
        return value;
      }
      default:
        throw new Error(`unsupported result ABI kind: ${kind}`);
    }
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

  natural(value) {
    const payload = BigInt(value);
    return payload <= MAX_TAGGED_PAYLOAD
      ? { kind: "tagged", payload }
      : this.alloc({ kind: "natural", value: payload });
  }

  literal(operation) {
    if (operation.kind === "naturalLiteral") {
      const value = this.natural(operation.value);
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
    const object = this.constructorObject(source);
    const value = object.objectFields[operation.index];
    if (value === undefined) {
      throw new SemanticFault({
        kind: "objectFieldOutOfBounds",
        index: operation.index,
        size: object.objectFields.length,
      });
    }
    return this.encode(operation.result, value);
  }

  usizeProj(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "usize projection host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    const object = this.constructorObject(source);
    const value = object.usizeFields[operation.index];
    if (value === undefined) {
      throw new SemanticFault({
        kind: "usizeFieldOutOfBounds",
        index: operation.index,
        size: object.usizeFields.length,
      });
    }
    return this.encode("usize", { kind: "usize", value });
  }

  scalarProj(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "scalar projection host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    const object = this.constructorObject(source);
    const field = object.scalarFields.find((candidate) =>
      candidate.width === operation.width && candidate.offset === operation.offset);
    if (field === undefined) {
      throw new SemanticFault({
        kind: "scalarFieldMissing",
        width: operation.width,
        offset: operation.offset,
      });
    }
    return this.encode(operation.result, field.value);
  }

  cacheSet(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "cacheSet host arity mismatch");
    const value = this.decode(operation.value, physicalArgs[0]);
    this.globals.set(operation.declaration, value);
    return this.encode(operation.value, value);
  }

  partialApply(operation, physicalArgs) {
    assert.equal(physicalArgs.length, operation.fields.length,
      "partial application host arity mismatch");
    assert.equal(operation.fixed, operation.fields.length,
      "partial application manifest fixed-count mismatch");
    assert.ok(operation.fixed < operation.arity,
      "partial application must leave at least one argument");
    const fixed = operation.fields.map((kind, index) =>
      this.decode(kind, physicalArgs[index]));
    const value = this.alloc({
      kind: "closure",
      function: operation.function,
      arity: operation.arity,
      fixed,
    });
    return this.encode(operation.result, value);
  }

  closureData(source) {
    if (source.kind !== "heap") {
      throw new SemanticFault({ kind: "expectedClosure" });
    }
    const object = this.liveCell(source.location).object;
    if (object.kind !== "closure") {
      throw new SemanticFault({ kind: "expectedClosure" });
    }
    return object;
  }

  closureMatches(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "closure match host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    const closure = this.closureData(source);
    return closure.function === operation.function &&
      closure.arity === operation.arity && closure.fixed.length === operation.fixed
      ? 1
      : 0;
  }

  closureProj(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "closure projection host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    const closure = this.closureData(source);
    if (closure.function !== operation.function || closure.arity !== operation.arity ||
        closure.fixed.length !== operation.fixed) {
      throw new Error("FIR target failure: closure metadata mismatch");
    }
    const value = closure.fixed[operation.index];
    assert.notEqual(value, undefined, "closure projection index is out of bounds");
    return this.encode(operation.result, value);
  }

  external(operation, physicalArgs) {
    assert.equal(physicalArgs.length, operation.params.length,
      "external host arity mismatch");
    const args = operation.params.map((kind, index) =>
      this.decode(kind, physicalArgs[index]));
    const implementation = this.externalRegistry.get(operation.declaration);
    if (implementation === undefined) {
      throw new SemanticFault({
        kind: "externalFailure",
        name: operation.declaration,
        message: "no external implementation installed",
      });
    }
    const response = implementation({
      declaration: operation.declaration,
      args,
      host: this,
      world: this.world,
    });
    assert.ok(response && typeof response === "object",
      `external ${operation.declaration} returned no response`);
    assert.ok(response.value && typeof response.value === "object",
      `external ${operation.declaration} returned no semantic value`);
    assert.ok(response.world === undefined ||
      (Number.isSafeInteger(response.world) && response.world >= 0),
    `external ${operation.declaration} returned an invalid world`);
    if (response.world !== undefined) {
      this.world = response.world;
    }
    this.trace.push({
      name: operation.declaration,
      args: args.map((value) => this.valueJson(value)),
      result: this.valueJson(response.value),
    });
    assert.ok(operation.results.length <= 1,
      "external semantic host supports at most one result");
    return operation.results.length === 0
      ? undefined
      : this.encode(operation.results[0], response.value);
  }

  box(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "box host arity mismatch");
    const scalar = this.decode(operation.scalar, physicalArgs[0]);
    assert.ok(scalar.kind === "scalar" || scalar.kind === "usize",
      "box expected a scalar value");
    const payload = scalar.value;
    const value = payload <= MAX_TAGGED_PAYLOAD
      ? { kind: "tagged", payload }
      : this.alloc({ kind: "boxed", scalarKind: operation.scalar, value: scalar });
    return this.encode(operation.result, value);
  }

  unbox(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "unbox host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    let value;
    if (source.kind === "tagged") {
      value = operation.scalar === "usize"
        ? { kind: "usize", value: source.payload }
        : { kind: "scalar", scalarKind: operation.scalar, value: source.payload };
    } else {
      const object = this.liveCell(source.location).object;
      if (object.kind !== "boxed") {
        throw new SemanticFault({ kind: "expectedScalar" });
      }
      value = object.value;
    }
    return this.encode(operation.scalar, value);
  }

  isShared(physicalArgs) {
    assert.equal(physicalArgs.length, 1, "isShared host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    const shared = source.kind === "tagged" || (() => {
      const cell = this.liveCell(source.location);
      return cell.persistent || cell.rc !== 1;
    })();
    return this.encode("uint8", {
      kind: "scalar",
      scalarKind: "uint8",
      value: shared ? 1n : 0n,
    });
  }

  objectSet(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 2, "object mutation host arity mismatch");
    const source = this.decode("object", physicalArgs[0]);
    const field = this.decode(operation.field, physicalArgs[1]);
    const object = this.constructorObject(source);
    if (operation.index >= object.objectFields.length) {
      throw new SemanticFault({
        kind: "objectFieldOutOfBounds",
        index: operation.index,
        size: object.objectFields.length,
      });
    }
    object.objectFields[operation.index] = field;
  }

  usizeSet(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 2, "usize mutation host arity mismatch");
    const source = this.decode("object", physicalArgs[0]);
    const field = this.decode("usize", physicalArgs[1]);
    const object = this.constructorObject(source);
    if (operation.index >= object.usizeFields.length) {
      throw new SemanticFault({
        kind: "usizeFieldOutOfBounds",
        index: operation.index,
        size: object.usizeFields.length,
      });
    }
    object.usizeFields[operation.index] = field.value;
  }

  scalarSet(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 2, "scalar mutation host arity mismatch");
    const source = this.decode("object", physicalArgs[0]);
    const field = this.decode(operation.field, physicalArgs[1]);
    if (field.kind !== "scalar") {
      throw new SemanticFault({ kind: "expectedScalar" });
    }
    const object = this.constructorObject(source);
    object.scalarFields = [
      { width: operation.width, offset: operation.offset, value: field },
      ...object.scalarFields.filter((old) =>
        old.width !== operation.width || old.offset !== operation.offset),
    ];
  }

  setTag(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "setTag host arity mismatch");
    const source = this.decode("object", physicalArgs[0]);
    this.constructorObject(source).tag = BigInt(operation.tag);
  }

  ownedValues(object) {
    switch (object.kind) {
      case "ctor":
        return object.objectFields;
      case "boxed":
        return [object.value];
      case "closure":
        return object.fixed;
      default:
        return [];
    }
  }

  incLocation(location, amount) {
    const cell = this.liveCell(location);
    if (!cell.persistent) {
      cell.rc += amount;
    }
  }

  decLocation(location) {
    const cell = this.liveCell(location);
    if (cell.persistent) {
      return;
    }
    if (cell.rc === 0) {
      throw new SemanticFault({ kind: "referenceCountUnderflow", location });
    }
    if (cell.rc > 1) {
      cell.rc -= 1;
      return;
    }
    cell.rc = 0;
    cell.live = false;
    for (const value of this.ownedValues(cell.object)) {
      if (value.kind === "heap") {
        this.decLocation(value.location);
      }
    }
  }

  inc(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "inc host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    if (source.kind === "heap") {
      this.incLocation(source.location, operation.amount);
    } else if (!operation.check) {
      throw new SemanticFault({ kind: "expectedHeapReference" });
    }
  }

  decValueOnce(source, check) {
    if (source.kind === "heap") {
      this.decLocation(source.location);
    } else if (source.kind === "tagged") {
      if (!check) {
        throw new SemanticFault({ kind: "expectedHeapReference" });
      }
    } else {
      throw new SemanticFault({ kind: "expectedObject" });
    }
  }

  dec(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "dec host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    for (let index = 0; index < operation.amount; ++index) {
      this.decValueOnce(source, operation.check);
    }
  }

  delete(physicalArgs) {
    assert.equal(physicalArgs.length, 1, "delete host arity mismatch");
    const source = this.decode("object", physicalArgs[0]);
    const cell = this.liveCell(source.location);
    cell.rc = 0;
    cell.live = false;
  }

  reset(operation, physicalArgs) {
    assert.equal(physicalArgs.length, 1, "reset host arity mismatch");
    const source = this.decode("tobject", physicalArgs[0]);
    let token;
    if (source.kind === "tagged") {
      token = { kind: "reuseToken", location: null };
    } else {
      const cell = this.liveCell(source.location);
      if (cell.persistent || cell.rc !== 1) {
        this.decLocation(source.location);
        token = { kind: "reuseToken", location: null };
      } else {
        if (cell.object.kind !== "ctor") {
          throw new SemanticFault({ kind: "expectedConstructor" });
        }
        if (operation.objectFields > cell.object.objectFields.length) {
          throw new SemanticFault({
            kind: "objectFieldOutOfBounds",
            index: operation.objectFields,
            size: cell.object.objectFields.length,
          });
        }
        const released = cell.object.objectFields.slice(0, operation.objectFields);
        for (let index = 0; index < operation.objectFields; ++index) {
          cell.object.objectFields[index] = { kind: "tagged", payload: 0n };
        }
        for (const field of released) {
          this.decValueOnce(field, true);
        }
        token = { kind: "reuseToken", location: source.location };
      }
    }
    return this.encode("reuseToken", token);
  }

  reuse(operation, physicalArgs) {
    assert.equal(physicalArgs.length, operation.fields.length + 1,
      "reuse host arity mismatch");
    const token = this.decode("reuseToken", physicalArgs[0]);
    const fields = operation.fields.map((kind, index) =>
      this.decode(kind, physicalArgs[index + 1]));
    assert.equal(operation.size, fields.length, "reuse manifest size mismatch");
    let value;
    if (token.location === null) {
      const tag = BigInt(operation.tag);
      value = operation.size === 0 && operation.usize === 0 && operation.ssize === 0
        ? { kind: "tagged", payload: tag }
        : this.alloc({
            kind: "ctor",
            tag,
            objectFields: fields,
            usizeFields: Array.from({ length: operation.usize }, () => 0n),
            scalarFields: [],
          });
    } else {
      const cell = this.liveCell(token.location);
      if (cell.object.kind !== "ctor") {
        throw new SemanticFault({ kind: "expectedConstructor" });
      }
      cell.object = {
        kind: "ctor",
        tag: operation.updateHeader ? BigInt(operation.tag) : cell.object.tag,
        objectFields: fields,
        usizeFields: Array.from({ length: operation.usize }, () => 0n),
        scalarFields: [],
      };
      value = { kind: "heap", location: token.location };
    }
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
    if (!cell?.live) {
      throw new SemanticFault({ kind: "deadObject", location });
    }
    return cell;
  }

  constructorObject(value) {
    if (value.kind !== "heap") {
      throw new SemanticFault({ kind: "expectedConstructor" });
    }
    const cell = this.liveCell(value.location);
    if (cell.object.kind !== "ctor") {
      throw new SemanticFault({ kind: "expectedConstructor" });
    }
    return cell.object;
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
      case "usizeProj":
        return (...args) => this.usizeProj(operation, args);
      case "scalarProj":
        return (...args) => this.scalarProj(operation, args);
      case "cacheSet":
        return (...args) => this.cacheSet(operation, args);
      case "partialApply":
        return (...args) => this.partialApply(operation, args);
      case "closureMatches":
        return (...args) => this.closureMatches(operation, args);
      case "closureProj":
        return (...args) => this.closureProj(operation, args);
      case "box":
        return (...args) => this.box(operation, args);
      case "unbox":
        return (...args) => this.unbox(operation, args);
      case "isShared":
        return (...args) => this.isShared(args);
      case "objectSet":
        return (...args) => this.objectSet(operation, args);
      case "usizeSet":
        return (...args) => this.usizeSet(operation, args);
      case "scalarSet":
        return (...args) => this.scalarSet(operation, args);
      case "setTag":
        return (...args) => this.setTag(operation, args);
      case "inc":
        return (...args) => this.inc(operation, args);
      case "dec":
        return (...args) => this.dec(operation, args);
      case "delete":
        return (...args) => this.delete(args);
      case "reset":
        return (...args) => this.reset(operation, args);
      case "reuse":
        return (...args) => this.reuse(operation, args);
      case "external":
        return (...args) => this.external(operation, args);
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
          scalarFields: object.scalarFields.map((field) => ({
            width: field.width,
            offset: field.offset,
            value: {
              kind: field.value.scalarKind,
              value: field.value.value.toString(),
            },
          })),
        };
      case "boxed":
        return {
          kind: "boxed",
          type: scalarTypeRepr(object.scalarKind),
          value: this.valueJson(object.value),
        };
      case "closure":
        return {
          kind: "closure",
          function: object.function,
          arity: object.arity,
          fixed: object.fixed.map((value) => this.valueJson(value)),
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
      for (const value of this.ownedValues(cell.object)) {
        if (value.kind === "heap") {
          pending.unshift(value.location);
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

  faultObservation(fault) {
    return {
      outcome: { kind: "fault", fault },
      reachableHeap: [],
      world: this.world,
      trace: this.trace,
    };
  }
}
