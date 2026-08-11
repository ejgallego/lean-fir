---
id: FIR-BUG-wasm-none-external-runtime-arena-overlap
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-11
reproduction: integration/illuminate-player/check-player-traces.mjs
regression: integration/illuminate-player/check-player-traces.mjs
---

# Summary

A closed application linked with the standard C math runtime can allocate its
FIR input graph inside the runtime's low-memory stack/data reservation, causing
later external calls to corrupt otherwise valid Lean objects.

## Minimal reproduction

Link the full Illuminate player frontier against the shared standard math
runtime, leave its fresh FIR heap frontier at 1024, and replay the existing
duplicate-frame-zero initialization trace. Initial graph encoding succeeds,
but `Float.ofScientific` execution overlaps the encoded graph and the result
decoder observes nonzero constructor-slot padding.

## Exact commands

```sh
cd integration/illuminate-player
ILLUMINATE_ROOT=/home/egallego/lean/vir/.worktrees/illuminate-fir-source-6f16 \
  node package.mjs
ILLUMINATE_ROOT=/home/egallego/lean/vir/.worktrees/illuminate-fir-source-6f16 \
  node check-player-traces.mjs
```

## Expected semantics

The external runtime and FIR arena must occupy disjoint memory regions. Every
decoded `FrameAction` should equal the native source result, independently of
whether standard Float externals execute during initialization.

## Actual behavior

The linked module is import-free and its small smoke passes, but the complete
trace suite rejects `initialLive transition.action.updates[0]` because slot
padding contains a value written by the overlapping runtime region.

## Proof or differential evidence

The same generated source module passes before the standard runtime is merged,
and the HitScene adapter already avoids this failure by moving the FIR frontier
to 65536. The player adapters retain their historical 1024 frontier, isolating
the discrepancy to the unshared memory-reservation contract.

## Semantic impact

Any complete package that merges the C runtime without reserving its low-memory
prefix can silently corrupt persistent inputs, scratch values, or decoded
results. Zero imports alone is therefore insufficient to establish a valid
module-owned-memory contract.

## Classification and triage

This is a package/adapter ownership-contract omission. The runtime linker must
publish one application-independent reserved-prefix capability, and all
adapters must advance the fresh FIR frontier to that boundary before encoding.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The shared `fir.standard-math/v1` capability now declares its 65536-byte
low-memory reservation. Complete module descriptors and `BUILD.json` carry the
same record; each adapter rejects disagreement and advances a fresh FIR heap
frontier to the declared boundary before allocating any Lean value. HitScene,
the full player, and the selection player consume the same contract.

The full 107-trace player comparison now passes, including the
duplicate-frame-zero reproducer. Package smokes also assert the initial arena
frontier, reject mismatched metadata, and retain flat post-dispatch frontiers
over 10,000 calls.
