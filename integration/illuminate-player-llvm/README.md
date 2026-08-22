# LLVM/Emscripten Illuminate selection player

This package compiles Illuminate's real `initialSelectionLive` and
`transitionSelectionLive` entries through Lean final LCNF, generated C, LLVM,
and Emscripten Wasm. It implements the same selection-only browser API as the
FIR-native v4 player while retaining the full Lean animation and player state
inside the module.

The JavaScript boundary projects `fps`, `totalFrames`, segment bounds, and
steps once during `createPlayer`. Segment SVG, patch maps, and parameter rows
never cross the compiler boundary. `dispatchTick` transports its timestamp as
a direct Wasm `f64`; the generic event wire carries the same little-endian
IEEE-754 binary64 bits.

## Build

The generic Emscripten setup must contain the unthreaded Lean runtime profile.
After running its setup command, build and test an immutable package with:

```sh
integration/illuminate-player-llvm/check.sh
```

`package.sh` prints the immutable directory and records that path in the
ignored `_build/illuminate-selection-player-current.txt` convenience file.
Pass the immutable directory itself to consumers; do not pass the pointer file
or introduce a moving package symlink.

## Browser API

```js
import { loadEmscriptenIlluminateSelectionPlayerAdapter } from
  "./illuminate-selection-player-emscripten-adapter.mjs";

const adapter = await loadEmscriptenIlluminateSelectionPlayerAdapter(
  new URL("./illuminate-selection-player.manifest.json", import.meta.url),
);
const created = adapter.createPlayer(animation);
const next = adapter.dispatch(created.player, { kind: "advance" });
const tick = adapter.dispatchTick(created.player, performance.now());
adapter.disposePlayer(created.player);
```

The five public methods are `createPlayer`, `dispatch`, `dispatchTick`,
`disposePlayer`, and `replayTrace`. Player objects are adapter-owned opaque
capabilities; no Lean or Wasm address reaches application JavaScript.
Disposal decrements the retained Lean player graph and is idempotent.

Each successful create/dispatch result contains a copied `action`, Lean's
`scheduleNextFrame` decision, non-overlapping phase timings, and current/peak
module-memory diagnostics. `projectMs` is present on creation. `totalMs` is an
independent wall interval rather than the sum of phases.

## Illuminate acceptance

From the Illuminate checkout named in the handoff:

```sh
ILLUMINATE_LLVM_PLAYER_DIR=/absolute/immutable/package \
  npm run accept:llvm-player

ILLUMINATE_LLVM_PLAYER_DIR=/absolute/immutable/package \
  npm run stage:players

npm run test:player-traces
```

The module is intentionally unthreaded and does not require COOP/COEP or
`crossOriginIsolated`. The manifest and `SHA256SUMS` authenticate the exact
loader, adapter, module, Wasm, smoke test, and source identities.

## Benchmark

Run the package-local fixed-event experiment without a profiler:

```sh
node integration/illuminate-player-llvm/benchmark.mjs \
  --manifest=/absolute/package/illuminate-selection-player.manifest.json \
  --out=integration/illuminate-player-llvm/_build/benchmark.json
```

The default design excludes two warmup rounds and alternates generic/scalar
order across nine measured rounds of 1,000 identical non-integer ticks. It
checks every resulting selection for equality and retains raw callback
samples plus median, p95, and median-absolute-deviation summaries for encode,
execute, decode, combined marshal, adapter overhead, and outer overhead. Run
the cross-engine dashboard separately; this script compares only the two
transport paths inside the same LLVM artifact.
