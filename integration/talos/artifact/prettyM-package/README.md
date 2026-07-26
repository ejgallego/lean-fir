# Current `Std.Format.prettyM` Wasm package

This folder is a reproducible handoff of the current, tested FIR artifact. The
compiler-produced Wasm module uses the concrete `wasm32-lean64`
representation, owns and exports its linear memory, and carries the first W7
resident heap boundary. JavaScript still implements the remaining semantic
runtime imports over that byte-level memory.

The exported raw boundary is:

```text
Format(tobject) × Nat(tobject) × Nat(tobject) × Nat(tobject)
  → PrettyTrace(object)

PrettyTrace := { text : String, eventsRev : List PrettyEvent }
PrettyEvent := { kind : Nat, text : String, value : Nat }
```

The JavaScript smoke client constructs ordinary Lean 4.32 `Format` heap
objects directly. It does not introduce another format AST or a high-level
adapter. This is intentional for the current compiler/runtime work: consumers
use the same low-level representation that the generated entry point sees.
`eventsRev` preserves the complete reverse-chronological
`MonadPrettyFormat` protocol: text output, newlines, tag starts, and tag ends.
The `text` field is the plain `String` projection for consumers that
intentionally do not observe styling.

This boundary is experimental and unversioned. `BUILD.json` sets its ABI
version to `null` and records capabilities rather than promising compatibility:
the measured import count, memory owner, current frontier operations, and both
the semantic and physical output types.

## Build the package

From the repository root:

```sh
integration/talos/artifact/package-pretty-format.sh
```

The canonical package path is:

```text
integration/talos/artifact/_build/prettyM-current/
```

Each invocation first builds and tests a complete immutable release, then
atomically moves the `prettyM-current` symlink to it. Readers therefore see
either the previous complete package or the new complete package, never a
mixture of their files. The sibling `prettyM-current-releases/` directory
contains the symlink targets.

An alternate canonical output path can be passed as the first argument.
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
PASS concrete styled prettyM trace (Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw)
```

`SHA256SUMS` authenticates the capability metadata, README, Wasm module,
descriptor, final LCNF capture, smoke client, and copied runtime sources.
`BUILD.json` records the source commit and dirty state, raw boundary, artifact
size and digest, measured capabilities, and exact test command.

## Runtime boundary

`prettyM.wasm` is a real standards-conforming Wasm module, but it is not yet
the final zero-function-import W7 artifact. It owns a `WebAssembly.Memory`,
starts its private frontier at byte 1024, and exports low-level
`fir_heap_frontier`, `fir_heap_set_frontier`, `fir_heap_alloc`, and typed raw
store operations. The accompanying `runtime/` tree supplies the current
concrete JavaScript implementations of the remaining 157 function imports.
All 27 constructor-allocation operations in the styled artifact are resident
in Wasm. While other allocating families remain imported, the temporary
mixed-runtime client synchronizes the shared monotone frontier at each import
boundary.

The smoke client prepares ordinary Lean values directly in the exported
memory, advances the monotone resident frontier before each call, decodes the
raw trace graph, and checks both its rendered text and exact tag boundaries
against an event oracle also guarded by native Lean 4.32. Keeping this package
separate provides a coherent integration snapshot while allocation families
move behind the resident boundary; it does not freeze that boundary as a
supported ABI.
