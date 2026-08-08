---
id: FIR-BUG-wasm-none-live-scratch-rewind-padding
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-08
reproduction: integration/illuminate-player/smoke.mjs
regression: integration/illuminate-player/illuminate-player-browser-adapter.mjs
---

# Summary

The persistent Illuminate player could not restore a per-dispatch heap
checkpoint with the existing monotonic frontier setter. After adding a
separate backward restore, reused resident Array slots retained stale high-word
padding unless the discarded scratch interval was cleared.

## Minimal reproduction

Encode a persistent `PlayerAnimation`, run `initialLive`, observe the frontier,
then attempt to restore the pre-call frontier with `fir_heap_set_frontier`.
The helper traps because its shared contract accepts only monotonic frontier
synchronization. If the frontier is restored without clearing discarded bytes,
run `transitionLive` twice and strictly decode the second action's update
Array; a reused object slot may retain nonzero padding from the preceding
transition.

## Exact commands

From `integration/illuminate-player`:

```sh
ILLUMINATE_ROOT=/home/egallego/lean/illuminate-vir-performance ./check.sh
```

## Expected semantics

Each live dispatch should allocate above one persistent checkpoint, copy all
host-visible results and the next native state, discard every scratch object,
and begin the next dispatch at the exact same canonical zero-filled frontier.
The historical monotonic setter must keep its existing contract.

## Actual behavior

`fir_heap_set_frontier(checkpoint)` traps whenever `checkpoint` is below the
current frontier. A first direct rewind then exposed stale slot padding:
`transitionLive result.action.updates[0]` contained the correct low object word
but retained a nonzero high padding word from the previous scratch graph.

## Proof or differential evidence

The live adapter's strict raw-layout decoder rejected the stale padding before
the action escaped to JavaScript. The same transition succeeds when the
discarded interval is zeroed before restoring the frontier. All 105 local
legacy/FIR traces remain action-equal with the fix.

## Semantic impact

Without a distinct rewind operation, the live package grows monotonically or
weakens an accepted allocator contract. Without clearing, repeated dispatches
can expose noncanonical raw object padding to strict consumers even though the
semantic low words are correct.

## Classification and triage

This is a Wasm adapter/runtime-boundary issue, not an Illuminate state-machine
discrepancy. Fresh monotonic allocation historically obtained zero padding
from new linear-memory pages; a resettable arena adds an explicit
canonicalization obligation.

## Workaround

None. The live package uses the resolved contract below.

## Upstream tracking

none

## Resolution and regression

W7 adds `fir_heap_rewind` as a separate aligned, bounded backward-frontier
helper, leaving `fir_heap_set_frontier` monotonic. Before invoking it, the
adapter clears the complete discarded interval and then verifies the exact
checkpoint. The live lowering also eliminates lazy-cache globals, and emission
fails unless the allocator frontier is the module's only mutable heap root.

The source and immutable-package smokes each run 10,000 ticks with a constant
704-byte scratch peak and the same post-dispatch checkpoint. They also cover
encode failures that remain recoverable and decode failures that rewind and
poison the player.
