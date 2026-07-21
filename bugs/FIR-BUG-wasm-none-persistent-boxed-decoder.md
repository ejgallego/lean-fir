---
id: FIR-BUG-wasm-none-persistent-boxed-decoder
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-21
reproduction: Fir/Wasm/Concrete/Examples.lean
regression: none
---

# Summary

The concrete boxed-scalar decoder rejects a live boxed allocation after cache
publication marks its header persistent.

## Minimal reproduction

Allocate the heap-backed `UInt64.max` scalar with `boxScalar`, call
`markPersistent` on the returned object, and then decode it with
`readBoxedScalar`. The persistence transition succeeds and retains the boxed
layout and payload, but the decoder returns `malformedBoxedHeader` solely
because the header's persistent bit is now true.

## Exact commands

```sh
lake build Fir.Wasm.Examples
```

## Expected semantics

Cache publication changes ownership metadata to `persistent = true, rc = 0`.
It does not change an object's kind, allocation extent, auxiliary layout, or
payload, so a persistent boxed scalar must decode to the same semantic value.

## Actual behavior

`readHeapBoxedScalar` contains an `unless !header.persistent` guard. Therefore
every cache-persisted `.boxed` allocation is rejected before its otherwise
canonical metadata and payload are checked.

## Proof or differential evidence

`markPersistentFuel` writes `{ header with persistent := true, refCount := 0 }`
and leaves the boxed payload untouched. `BoxedObjectRel`, independently,
requires `header.persistent = false`; together these facts make both executable
decoding and `LiveHeapRel` reconstruction fail for the same valid post-state.

## Semantic impact

A zero-argument declaration returning a heap-backed scalar above FIR's tagged
range can be cached successfully but cannot subsequently be unboxed by the
concrete runtime. The same restriction blocks the constructive cache-
persistence refinement for boxed cells.

## Classification and triage

The shared FIR semantics intentionally permits persistent boxed objects and
the concrete persistence writer preserves their representation. The fault is
therefore in the concrete Wasm decoder/refinement boundary rather than in an
LCNF pass.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
