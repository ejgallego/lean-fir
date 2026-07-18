import assert from "node:assert/strict";

import {
  SemanticFault,
  SemanticHost,
} from "../../../scripts/wasm_semantic_host.mjs";
import {
  validationExternalRegistry,
} from "../../../scripts/wasm_validation_externals.mjs";

function scalar(kind, value) {
  return { kind: "scalar", scalarKind: kind, value: BigInt(value) };
}

function tagged(payload) {
  return { kind: "tagged", payload: BigInt(payload) };
}

function ctorRuntime() {
  return {
    nextLocation: 2,
    heap: [
      {
        location: 0,
        rc: 1,
        persistent: false,
        live: true,
        object: {
          kind: "ctor",
          tag: "4",
          objectFields: [
            { kind: "object", reference: { kind: "heap", location: 1 } },
            { kind: "object", reference: { kind: "tagged", payload: "7" } },
          ],
          usizeFields: ["3"],
          scalarFields: [
            { width: 4, offset: 0, value: { kind: "uint32", value: "9" } },
          ],
        },
      },
      {
        location: 1,
        rc: 1,
        persistent: false,
        live: true,
        object: { kind: "natural", value: "9223372036854775808" },
      },
    ],
  };
}

{
  const host = new SemanticHost(ctorRuntime());
  const root = host.encode("object", { kind: "heap", location: 0 });
  const projected = host.importFunction({ kind: "objectProj", index: 1, result: "tobject" })(root);
  assert.deepStrictEqual(host.decode("tobject", projected), tagged(7));
  assert.equal(host.importFunction({ kind: "usizeProj", index: 0 })(root), 3n);
  assert.equal(host.importFunction({
    kind: "scalarProj", width: 4, offset: 0, result: "uint32",
  })(root), 9);

  host.importFunction({ kind: "objectSet", index: 1, field: "tobject" })(
    root, host.encode("tobject", tagged(11)));
  host.importFunction({ kind: "usizeSet", index: 0 })(
    root, host.encode("usize", { kind: "usize", value: 12n }));
  host.importFunction({ kind: "scalarSet", width: 4, offset: 0, field: "uint32" })(
    root, host.encode("uint32", scalar("uint32", 13)));
  host.importFunction({ kind: "setTag", tag: "14" })(root);
  assert.deepStrictEqual(
    host.decode("tobject", host.importFunction({
      kind: "objectProj", index: 1, result: "tobject",
    })(root)),
    tagged(11),
  );
  assert.equal(host.importFunction({ kind: "usizeProj", index: 0 })(root), 12n);
  assert.equal(host.importFunction({
    kind: "scalarProj", width: 4, offset: 0, result: "uint32",
  })(root), 13);
  assert.equal(host.importFunction({ kind: "getTag" })(root), 14);
}

{
  const host = new SemanticHost({
    nextLocation: 1,
    heap: [{
      location: 0,
      rc: 1,
      persistent: false,
      live: true,
      object: { kind: "integer", value: "-2147483649" },
    }],
  });
  assert.deepStrictEqual(host.liveCell(0).object, {
    kind: "integer",
    value: -2147483649n,
  });
}

{
  const host = new SemanticHost({
    nextLocation: 1,
    heap: [{
      location: 0,
      rc: 1,
      persistent: false,
      live: true,
      object: { kind: "byteArray", value: [0, 127, 128, 255] },
    }],
  });
  assert.deepStrictEqual(host.liveCell(0).object, {
    kind: "byteArray",
    value: [0, 127, 128, 255],
  });
}

{
  const host = new SemanticHost();
  const maximum = scalar("uint64", 0xffffffffffffffffn);
  const boxed = host.importFunction({ kind: "box", scalar: "uint64", result: "tobject" })(
    host.encode("uint64", maximum));
  const boxedValue = host.decode("tobject", boxed);
  assert.equal(boxedValue.kind, "heap");
  assert.deepStrictEqual(host.objectJson(host.liveCell(boxedValue.location).object), {
    kind: "boxed",
    type: "Lean.Expr.const `UInt64 []",
    value: {
      kind: "scalar",
      scalar: { kind: "uint64", value: "18446744073709551615" },
    },
  });
  const unboxed = host.importFunction({ kind: "unbox", scalar: "uint64" })(boxed);
  assert.deepStrictEqual(host.decode("uint64", unboxed), maximum);
  assert.equal(host.importFunction({ kind: "isShared" })(boxed), 0);
  host.importFunction({ kind: "inc", amount: 1, check: false })(boxed);
  assert.equal(host.importFunction({ kind: "isShared" })(boxed), 1);
  host.importFunction({ kind: "dec", amount: 1, check: false, objectFields: null })(boxed);
  assert.equal(host.importFunction({ kind: "isShared" })(boxed), 0);

  const immediate = host.importFunction({ kind: "box", scalar: "uint32", result: "tobject" })(
    host.encode("uint32", scalar("uint32", 0xffffffffn)));
  assert.equal(host.decode("tobject", immediate).kind, "tagged");
  assert.equal(host.importFunction({ kind: "isShared" })(immediate), 1);
}

{
  const host = new SemanticHost();
  assert.deepStrictEqual(host.integer(2147483647n), tagged(2147483647n));
  assert.deepStrictEqual(host.integer(-2147483648n), tagged(2147483648n));
  const positive = host.integer(2147483648n);
  const negative = host.integer(-2147483649n);
  assert.deepStrictEqual(host.liveCell(positive.location).object, {
    kind: "integer",
    value: 2147483648n,
  });
  assert.deepStrictEqual(host.liveCell(negative.location).object, {
    kind: "integer",
    value: -2147483649n,
  });
}

{
  const host = new SemanticHost(undefined, validationExternalRegistry);
  const decLt = host.importFunction({
    kind: "external",
    declaration: "Int.decLt",
    params: ["tobject", "tobject"],
    results: ["uint8"],
  });
  const compare = (left, right) => {
    const result = decLt(
      host.encode("tobject", host.integer(left)),
      host.encode("tobject", host.integer(right)),
    );
    return host.decode("uint8", result).value;
  };
  assert.equal(compare(-2147483648n, 0n), 1n);
  assert.equal(compare(2147483647n, 0n), 0n);
  assert.equal(compare(-2147483649n, 0n), 1n);
  assert.equal(compare(2147483648n, 0n), 0n);
  assert.equal(host.world, 0);
  assert.deepStrictEqual(host.trace.map((event) => event.name),
    ["Int.decLt", "Int.decLt", "Int.decLt", "Int.decLt"]);
}

{
  const host = new SemanticHost(ctorRuntime());
  const root = host.encode("object", { kind: "heap", location: 0 });
  const tokenPhysical = host.importFunction({ kind: "reset", objectFields: 1 })(root);
  const token = host.decode("reuseToken", tokenPhysical);
  assert.deepStrictEqual(token, { kind: "reuseToken", location: 0 });
  assert.throws(
    () => host.liveCell(1),
    (error) => error instanceof SemanticFault && error.fault.kind === "deadObject",
  );
  const reused = host.importFunction({
    kind: "reuse",
    name: "Replacement.mk",
    tag: "9",
    size: 1,
    usize: 0,
    ssize: 0,
    updateHeader: true,
    fields: ["tobject"],
    result: "object",
  })(tokenPhysical, host.encode("tobject", tagged(13)));
  assert.deepStrictEqual(host.decode("object", reused), { kind: "heap", location: 0 });
  assert.equal(host.importFunction({ kind: "getTag" })(reused), 9);
  assert.deepStrictEqual(
    host.decode("tobject", host.importFunction({
      kind: "objectProj", index: 0, result: "tobject",
    })(reused)),
    tagged(13),
  );
}

{
  const host = new SemanticHost(ctorRuntime());
  const root = host.encode("object", { kind: "heap", location: 0 });
  host.importFunction({ kind: "dec", amount: 1, check: false, objectFields: 2 })(root);
  for (const location of [0, 1]) {
    assert.throws(
      () => host.liveCell(location),
      (error) => error instanceof SemanticFault && error.fault.kind === "deadObject",
    );
  }
}

{
  const host = new SemanticHost(ctorRuntime());
  const root = host.encode("object", { kind: "heap", location: 0 });
  host.importFunction({ kind: "delete" })(root);
  assert.throws(
    () => host.liveCell(0),
    (error) => error instanceof SemanticFault && error.fault.kind === "deadObject",
  );
  assert.equal(host.liveCell(1).live, true);
}

{
  const host = new SemanticHost(ctorRuntime());
  host.importFunction({ kind: "delete" })(0);
  assert.equal(host.liveCell(0).rc, 1);
  assert.equal(host.liveCell(1).rc, 1);
}

{
  const host = new SemanticHost();
  const captured = host.encode("tobject", tagged(21));
  const closurePhysical = host.importFunction({
    kind: "partialApply",
    function: "callee",
    arity: 2,
    fixed: 1,
    fields: ["tobject"],
    result: "tobject",
  })(captured);
  assert.equal(host.importFunction({
    kind: "closureMatches", function: "callee", arity: 2, fixed: 1,
  })(closurePhysical), 1);
  assert.equal(host.importFunction({
    kind: "closureMatches", function: "other", arity: 2, fixed: 1,
  })(closurePhysical), 0);
  const projected = host.importFunction({
    kind: "closureProj",
    function: "callee",
    arity: 2,
    fixed: 1,
    index: 0,
    result: "tobject",
  })(closurePhysical);
  assert.deepStrictEqual(host.decode("tobject", projected), tagged(21));
  const closure = host.decode("tobject", closurePhysical);
  assert.deepStrictEqual(host.objectJson(host.liveCell(closure.location).object), {
    kind: "closure",
    function: "callee",
    arity: 2,
    fixed: [{
      kind: "object",
      reference: { kind: "tagged", payload: "21" },
    }],
  });
}

{
  const host = new SemanticHost(undefined, {
    echo: ({ args, world }) => ({ value: args[0], world: world + 1 }),
  });
  const maximum = scalar("uint64", 0xffffffffffffffffn);
  const physical = host.encode("uint64", maximum);
  const cached = host.importFunction({
    kind: "cacheSet", declaration: "echo", value: "uint64",
  })(physical);
  assert.deepStrictEqual(host.decode("uint64", cached), maximum);
  assert.deepStrictEqual(host.globals.get("echo"), maximum);
  const result = host.importFunction({
    kind: "external",
    declaration: "echo",
    params: ["uint64"],
    results: ["uint64"],
  })(physical);
  assert.deepStrictEqual(host.decode("uint64", result), maximum);
  assert.equal(host.world, 1);
  assert.deepStrictEqual(host.trace, [{
    name: "echo",
    args: [{
      kind: "scalar",
      scalar: { kind: "uint64", value: "18446744073709551615" },
    }],
    result: {
      kind: "scalar",
      scalar: { kind: "uint64", value: "18446744073709551615" },
    },
  }]);
}

{
  const host = new SemanticHost();
  assert.throws(
    () => host.importFunction({
      kind: "external",
      declaration: "missing",
      params: [],
      results: ["uint64"],
    })(),
    (error) => error instanceof SemanticFault && error.fault.kind === "externalFailure",
  );
}

console.log("PASS W5 semantic host runtime/external/cache/closure operations");
