# FIR-native Illuminate player packages

This integration publishes the accepted full-action v3 live player and a
separately versioned selection-only v4 player. The v3 API remains unchanged;
v4 retains only timing and selection state in Wasm while JavaScript owns SVG,
parameter bindings, and per-frame parameter strings. Both package fingerprints
are tied to the source revision in `illuminate-source.json`.

This integration compiles the real Lean 4.32 entries from
`Illuminate.Animation.FirLive`:

```text
initialLive : PlayerAnimation → Except String LiveTransition
transitionLive : PlayerAnimation → PlayerState → PlayerEvent → LiveTransition
```

The structured input is the SVG-free `PlayerAnimation`. JSON, DOM code,
synchronization SVG, and a copied state machine are not part of the artifact.
The integration consumes Illuminate source through a read-only FIR-toolchain
view and never consumes Illuminate's `.lake` products.

FIR clears Lean's imported specialization-name cache in an isolated
environment and records the exact declarations at the end of the real final
impure LCNF pipeline. Private matcher specializations therefore remain source
functions; no Illuminate transition is replaced by a handwritten resident
implementation.

## Build and verify

The required Illuminate source is pinned to repository
`https://github.com/ejgallego/illuminate.git` at revision
`6f16cdc3d4320c093b53a9d381b92bfbb689b2ce`. To prepare the default local
checkout:

```sh
cd integration/illuminate-player
git clone https://github.com/ejgallego/illuminate.git .illuminate
git -C .illuminate checkout --detach 6f16cdc3d4320c093b53a9d381b92bfbb689b2ce
./check.sh
```

Alternatively, point the gate at an existing clean checkout of that exact
revision:

```sh
cd integration/illuminate-player
ILLUMINATE_ROOT=/path/to/illuminate ./check.sh
```

`check.sh`, `package.mjs`, and `selection-package.mjs` reject a dirty checkout
or any revision other than the pinned contract before publishing a package.

The gate builds both focused Lean dependency cones, publishes both packages
twice, checks deterministic bytes and checksums, runs the source-tree and
packaged smokes, and compares 107 legacy-JavaScript/FIR-v3/FIR-v4 traces event
by event. The
smoke includes every event and patch target, non-integral timestamps, two
independent players, failure poisoning, repeated disposal, repeated
create/dispose cycles, and 10,000 ticks at a flat post-dispatch frontier.

`package.mjs` atomically publishes an immutable directory under
`_build/illuminate-player-packages/`; the canonical
`_build/illuminate-player-current` symlink points to:

```text
illuminate-player.wasm
illuminate-player.wasm.json
illuminate-player-browser-adapter.mjs
BUILD.json
SHA256SUMS
smoke.mjs
```

### External artifact producer

`export-v3-package.sh` exposes the accepted v3 package through the common
caller-owned output-directory contract. The caller must supply a fresh output
path and the exact clean Illuminate checkout explicitly:

```sh
ILLUMINATE_ROOT=/path/to/illuminate \
  ./export-v3-package.sh /path/to/fresh-output
```

The FIR checkout must also be clean. The producer runs the complete existing
gate, including deterministic double publication, checksums, packaged smokes,
and the 107-trace v3/v4 comparison. It then installs regular copies of the six
v3 package files into the requested directory and independently checks that
directory's `SHA256SUMS` and package-local smoke before returning success. It
does not copy the `_build/illuminate-player-current` symlink, publish the
export, or collect performance timings.

## Browser and Node contract

The asynchronous loader compiles one shared `WebAssembly.Module`. Each opaque
player receives its own synchronous `WebAssembly.Instance`:

```js
const adapter = await fetchIlluminatePlayerAdapter(
  new URL("./illuminate-player.wasm", import.meta.url));

const created = adapter.createPlayer(animation);
if (!created.ok) throw new Error(created.error);

const next = adapter.dispatch(created.player,
  { kind: "tick", timestamp: performance.now() });
adapter.disposePlayer(created.player);
```

`createPlayer` returns the initial copied action and Lean-computed
`scheduleNextFrame`. `dispatch` returns the next copied action and scheduling
decision. `disposePlayer` is idempotent, invalidates the handle, and drops the
instance. No Wasm address is an application-visible property. `replayTrace`
is retained as a compatibility/differential helper implemented by these three
live operations.

Creation reports `instantiateMs`, `projectMs`, `animationEncodeMs`,
`stateSlotMs`, `executeMs`, `decodeMs`, `rewindMs`, independently measured
`totalMs`, and residual `overheadMs`. Dispatch reports non-overlapping
`encodeMs`, `executeMs`, `decodeMs`, and `rewindMs` intervals plus total and
overhead. Memory diagnostics include the persistent checkpoint, scratch peak,
bytes cleared, exact post-rewind frontier, logical animation-object count, and
physical resident allocator-call count.

## Ownership and bounded reclamation

Animation projection and encoding happen once per player. The adapter first
measures the exact graph, obtains one contiguous resident allocation, and
suballocates its Lean objects locally while encoding. The recursively
persistent animation graph and a fixed 448-byte `PlayerState` slot live below
the checkpoint. This removes one JavaScript-to-Wasm allocator call per graph
object without changing the Lean layout or public adapter contract. State
stays in Wasm: the adapter copies each Lean-produced
state into that fixed slot before discarding the transition graph, including
bit-exact boxed binary64 timestamp bits. It is neither exposed nor rebuilt
from an application JavaScript object.

Each dispatch allocates only its `PlayerEvent` and Lean result in scratch
memory. Before restoring the frontier, the adapter copies all result strings,
updates the fixed state slot, clears the discarded byte interval, calls the
checked `fir_heap_rewind`, and verifies the exact checkpoint. Execution,
decoding, or rewind failure poisons and drops the instance.

The live lowering replaces private lazy-cache-global sequences with direct
zero-argument calls. Those declarations are pure; this keeps their values in
scratch and makes the allocator frontier the module's sole mutable heap root.
`Emit.lean` fails unless the linked module has zero cache initializers, exactly
one resident global, zero unresolved operations, and zero imports.

The public function surface is exactly:

```text
Illuminate.AnimationPlayer.initialLive
Illuminate.AnimationPlayer.transitionLive
fir_heap_frontier
fir_heap_set_frontier
fir_heap_rewind
fir_heap_alloc
```

Memory is module-owned. `fir_heap_set_frontier` keeps its historical monotonic
synchronization contract; backward restoration is deliberately isolated in
`fir_heap_rewind`. Resident helpers remain internal unless listed above.
`BUILD.json` records both entry ABIs, source and helper inventories, the absent
cache roots, ownership versions, source hashes, artifact sizes, and checksums.

## Selection-only v4 package

`Illuminate.Animation.FirSelection` contributes the real entries:

```text
initialSelectionLive : SelectionAnimation → Except String LiveSelectionTransition
transitionSelectionLive : SelectionAnimation → PlayerState → PlayerEvent → LiveSelectionTransition
```

They reuse `initialPrepared` and `transitionPrepared`; there is no copied state
machine. Lean erases the single-field `SelectionAnimation` wrapper, so the
physical object parameter is its underlying `PlayerAnimation` timeline. The
adapter documents and encodes that representation directly.

`selection-package.mjs` atomically publishes a distinct immutable directory
under `_build/illuminate-selection-player-packages/`; the canonical
`_build/illuminate-selection-player-current` symlink points to:

```text
illuminate-selection-player.wasm
illuminate-selection-player.wasm.json
illuminate-selection-player-browser-adapter.mjs
BUILD.json
SHA256SUMS
smoke.mjs
```

The adapter API remains `createPlayer`, `dispatch`, `disposePlayer`, and
`replayTrace`, at capability `fir.illuminate-player.browser/v4`. Returned
actions contain frame, step, segment, local frame, segment-change, and playback
only. Consumers materialize patches from their original `pmap` and
`params[localFrame]`; the adapter neither reads nor transfers those values.

The v4 package preserves the v3 persistent-checkpoint ownership protocol:
one shared compiled module, one instance per opaque player, a retained compact
selection graph and fixed state slot below the checkpoint, and cleared/re-wound
event and result scratch after every call. Its source and package smokes enforce
the 16 KiB/400-allocation/one-page creation bounds and a flat frontier across
10,000 ticks.

Against an Illuminate checkout that has generated
`test_output/anim-comparison.html`, the package-level dashboard check and the
order-balanced phase benchmark are:

```sh
ILLUMINATE_ROOT=/path/to/illuminate node check-selection-dashboard.mjs
ILLUMINATE_ROOT=/path/to/illuminate node selection-benchmark.mjs
```

The dashboard check compares v4 after host-side patch-row materialization with
v3 at every segment boundary, step, and final frame of all 16 examples. The
benchmark excludes a warmup, alternates v3/v4 order for at least seven rounds,
records raw samples and median/p95/MAD summaries, and writes
`_build/illuminate-selection-benchmark.json`.

## Benchmarking

`benchmark.mjs` can compare a prior whole-trace package and the live package
over every dashboard example using order-balanced rounds. It checks action
equality and records the differing phase models explicitly, including live
persistent bytes, scratch peak, rewind time, and post-rewind frontier. Do not
compare raw FIR entry time with a VIR measurement that includes its complete
`runtime.call` boundary.
