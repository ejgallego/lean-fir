# Current `Std.Format.prettyM` Wasm package

This folder is a reproducible handoff of the current, tested FIR artifact. It
is intentionally the pre-W7 runtime boundary: the compiler-produced Wasm
module uses the concrete `wasm32-lean64` representation, while JavaScript
implements its runtime imports over a byte-level heap.

The exported raw ABI is:

```text
Format(tobject) × Nat(tobject) × Nat(tobject) × Nat(tobject) → String(object)
```

The JavaScript smoke client constructs ordinary Lean 4.32 `Format` heap
objects directly. It does not introduce another format AST or a high-level
adapter.

## Build the package

From the repository root:

```sh
integration/talos/artifact/package-pretty-format.sh
```

The prepared package is written to:

```text
integration/talos/artifact/_build/prettyM-current/
```

An alternate output directory can be passed as the first argument.
If the source artifact has already been generated, `--no-build` re-packages
and tests it without rerunning Lean:

```sh
integration/talos/artifact/package-pretty-format.sh --no-build
```

## Test the prepared package

```sh
cd integration/talos/artifact/_build/prettyM-current
node smoke.mjs
```

The expected result is:

```text
PASS concrete raw-layout prettyM client (Fir.Wasm.Emit.SourceFixture.prettyFormatRaw)
```

`SHA256SUMS` authenticates the Wasm module, descriptor, final LCNF capture,
smoke client, and copied runtime sources. `BUILD.json` records the source
commit, raw ABI, artifact size and digest, import count, and exact test command.

## Runtime boundary

`prettyM.wasm` is a real standards-conforming Wasm module, but it is not the
future W7 self-contained artifact. The accompanying `runtime/` tree supplies
the current concrete JavaScript host. The module has 351 function imports and
does not own a `WebAssembly.Memory`; the host owns the concrete byte buffer.

W7 will replace this boundary with module-owned memory and Wasm-resident
runtime helpers. Keeping this package separate provides a stable baseline for
agents and differential testing while that work proceeds.
