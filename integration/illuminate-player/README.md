# FIR-native Illuminate player package

This integration project compiles the real Lean 4.32 entry
`Illuminate.AnimationPlayer.replayTrace` into a self-contained WebAssembly
module. Its structured input is the SVG-free `Illuminate.PlayerAnimation`;
JSON, DOM code, synchronization SVG, and a copied façade or state machine are
not part of the artifact. The integration reads Illuminate source through the
FIR toolchain and never consumes Illuminate's `.lake` products.

The source compiler clears Lean's imported specialization-name cache inside
an isolated environment and records the exact declaration groups at the end
of the real final-impure LCNF pipeline. Consequently, private loop and matcher
specializations are retained as ordinary source functions; the package does
not replace them with Illuminate-specific resident Wasm implementations.

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

The gate runs the native Lean guards, source-tree adapter smoke, 105 focused
legacy-JavaScript/FIR-native differential traces, two deterministic package
publications, checksum verification, and the packaged smoke test. The
authoritative Illuminate repository adds the full 106-trace comparison across
legacy JavaScript, VIR-JSON, VIR-typed, and FIR-native:

```sh
cd /path/to/illuminate
ILLUMINATE_NATIVE_PLAYER_DIR=/absolute/path/to/illuminate-player-current \
  npm run stage:players
npm run test:player-traces
```

The staging script must accept the direct
`Illuminate.AnimationPlayer.replayTrace` entry and browser-adapter API v2; an
older staging script that pins `replayTraceNative`/v1 is incompatible with this
package even though the trace runner itself can consume it.

## Consume from browser or Node

The adapter exports `createIlluminatePlayerAdapter` for bytes already in hand
and `fetchIlluminatePlayerAdapter` for browser loading. Its public phases are
`prepare`, `execute`, and `decode`; `replayTrace` performs all three.

```js
const adapter = await fetchIlluminatePlayerAdapter(
  new URL("./illuminate-player.wasm", import.meta.url));
const result = adapter.replayTrace(animation, events);
```

The adapter projects Illuminate's compact animation object exactly once,
discarding each segment's `sync` field and mapping patch targets to the Lean
inductive. It then writes a fresh Lean graph into module-owned memory, retains
the validated integers as Lean `Nat`, preserves timestamp `Float` values as
binary64, and returns copied normalized actions. Phase handles hide raw Wasm
object words. Allocations use an instance-lifetime monotonic arena, so discard
the adapter instance to reclaim a completed differential-testing batch.

`replayTrace` reports `projectMs`, `encodeMs`, `prepareMs`, `executeMs`,
`decodeMs`, independently measured `totalMs`, and residual `overheadMs`.
`prepareMs` encloses frontier synchronization, projection, encoding, and
argument preparation; `executeMs` covers only the exported Wasm call. Memory
diagnostics report each frontier and prepare/execute/total growth.

The production module exports only the structured trace entry plus
`fir_heap_frontier`, `fir_heap_set_frontier`, and `fir_heap_alloc`. Resident
runtime helpers remain internal Wasm functions and are retained only when
reachable from that four-function public surface. `BUILD.json` records the
exact public, source, and resident-helper inventories plus the internal
function count, including the captured generated-specialization inventory.

## Compare the previous and regenerated packages

`benchmark.mjs` uses every example embedded in Illuminate's comparison
dashboard. It runs one warmup and eight measured order-balanced old/new rounds
by default, creates a fresh Wasm instance for every sample, checks decoded
action equality, and writes raw samples plus median/MAD summaries:

```sh
ILLUMINATE_ROOT=/path/to/illuminate \
ILLUMINATE_OLD_PLAYER_DIR=/path/to/old/package \
ILLUMINATE_NEW_PLAYER_DIR=$(realpath _build/illuminate-player-current) \
  node benchmark.mjs
```

The report is `_build/illuminate-player-benchmark.json`. The previous v1
adapter's `encodeMs` includes direct encoding of its SVG-bearing input and has
no separate projection interval; its `totalMs` is the sum of its three phase
durations. The v2 adapter reports projection separately and measures total wall
time independently. Neither number should be compared directly with the
current Verso-style VIR `runtime.call` timing; a typed VIR benchmark boundary
is required for that performance comparison.
