# FIR-native Illuminate live-player package

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

```sh
cd integration/illuminate-player
ILLUMINATE_ROOT=/path/to/illuminate ./check.sh
```

The gate builds the focused Lean dependency cone, publishes the package twice,
checks deterministic bytes and checksums, runs the source-tree and packaged
smokes, and compares 105 legacy-JavaScript/FIR traces event by event. The
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
bytes cleared, and exact post-rewind frontier.

## Ownership and bounded reclamation

Animation projection and encoding happen once per player. The recursively
persistent animation graph and a fixed 448-byte `PlayerState` slot live below
the checkpoint. State stays in Wasm: the adapter copies each Lean-produced
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

## Benchmarking

`benchmark.mjs` can compare a prior whole-trace package and the live package
over every dashboard example using order-balanced rounds. It checks action
equality and records the differing phase models explicitly, including live
persistent bytes, scratch peak, rewind time, and post-rewind frontier. Do not
compare raw FIR entry time with a VIR measurement that includes its complete
`runtime.call` boundary.
