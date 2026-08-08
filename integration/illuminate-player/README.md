# FIR-native Illuminate player package

This integration project compiles the real Lean 4.32
`Illuminate.Animation.Native.replayTraceNative` façade into a self-contained
WebAssembly module. The façade calls Illuminate's `initialTransition` and
`transition`; JSON, DOM code, and a copied state machine are not part of the
artifact.

## Build the immutable package

Point `ILLUMINATE_ROOT` at an Illuminate checkout whose player sources compile
under Lean 4.32, then run:

```sh
cd integration/illuminate-player
ILLUMINATE_ROOT=/path/to/illuminate node package.mjs
```

The command rebuilds the focused Lean dependency cone, emits Wasm, verifies
the zero-import complete-runtime contract, and atomically publishes an
immutable directory under `_build/illuminate-player-packages/`.
`_build/illuminate-player-current` points to the complete tested package:

```text
illuminate-player.wasm
illuminate-player.wasm.json
illuminate-player-browser-adapter.mjs
BUILD.json
SHA256SUMS
smoke.mjs
```

Run the complete focused gate with:

```sh
ILLUMINATE_ROOT=/path/to/illuminate ./check.sh
```

The gate runs the native Lean guards, source-tree adapter smoke, 105
legacy-JavaScript/FIR-native differential traces, two deterministic package
publications, checksum verification, and the packaged smoke test.

## Consume from browser or Node

The adapter exports `createIlluminatePlayerAdapter` for bytes already in hand
and `fetchIlluminatePlayerAdapter` for browser loading. Its public phases are
`prepare`, `execute`, and `decode`; `replayTrace` performs all three.

```js
const adapter = await fetchIlluminatePlayerAdapter(
  new URL("./illuminate-player.wasm", import.meta.url));
const result = adapter.replayTrace(animation, events);
```

The adapter accepts Illuminate's compact animation/event objects, writes a
fresh Lean graph into module-owned memory, preserves timestamp `Float` values
as binary64, and returns copied normalized actions. No raw Wasm address escapes
the adapter. Allocations use an instance-lifetime monotonic arena, so discard
the adapter instance to reclaim a completed differential-testing batch.

The production module exports only the structured trace entry plus
`fir_heap_frontier`, `fir_heap_set_frontier`, and `fir_heap_alloc`. Resident
runtime helpers remain internal Wasm functions and are retained only when
reachable from that four-function public surface. `BUILD.json` records the
exact public, source, and resident-helper inventories plus the internal
function count.
