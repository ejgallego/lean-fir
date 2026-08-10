---
id: FIR-BUG-wasm-none-rewindable-lazy-initializer-persistence
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-10
reproduction: integration/illuminate-hit-scene/package-smoke.mjs
regression: Fir/Wasm/Emit/ResidentCache.lean
---

# Summary

`ResidentCache.eliminateLazyInitializers` replaces a lazy persistent singleton
read with a direct initializer call, but does not recursively mark the fresh
result persistent. Final LCNF has already erased persistent increments and
decrements, so the fresh ordinary graph can be under-retained and released
twice.

## Minimal reproduction

Use a closed initializer that allocates one child, performs
`inc[2][persistent][ref] child`, and stores the child in both fields of a pair.
After lazy-initializer elimination, the increment is absent from emitted Wasm
and the direct initializer returns an ordinary pair whose duplicated child has
reference count one. Releasing both fields frees the child on the first release
and faults on the second.

The real distinguishing instance is
`_private.Illuminate.Geometry.Trace.0.Illuminate.pathDataHits._closed_1` in the
HitScene closure.

## Exact commands

```sh
cd integration/illuminate-hit-scene
ILLUMINATE_ROOT=/tmp/illuminate-hit-scene-pinned \
  lake --keep-toolchain env lean -DmaxHeartbeats=0 Emit.lean
```

Then execute the fixture's `origin` query through the browser adapter.

## Expected semantics

Removing module cache roots for a rewindable consumer must preserve the
compiler's persistent-value contract. Each use may receive a fresh graph, but
that graph must be recursively persistent before code compiled under erased
persistent ownership operations observes it.

## Actual behavior

The transform emits only `call initializer`. The fresh result remains ordinary
and retains allocation-time reference counts that do not account for
persistent increments erased by final-LCNF lowering.

## Proof or differential evidence

Temporary external-engine instrumentation records two consecutive checked
releases of the same address. The first installs a canonical freed header; the
second faults in `fir_dec_once`. The object is the duplicated `Vec2` child of
the closed path-traversal accumulator.

## Semantic impact

Any rewindable resident package using a closed initializer with shared
substructure can fault or observe incorrect ownership after applying the
current transform. Persistent cached packages mask the issue because their
cache publication recursively marks the graph.

## Classification and triage

This is a shared executable transform bug against the existing persistence
contract. The fix should reuse the resident cache-publication/persistence API:
directly construct the fresh graph, recursively mark it persistent, and retain
no module cache root.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`eliminateLazyInitializers` now replaces a cache read with `call initializer`
followed by the existing `cacheSet` runtime operation. Resident cache linking
turns that operation into recursive persistence publication without retaining
the former global root. Its focused guard requires the shifted private global,
the fresh-publication operation, and the exact rewritten body.

The real duplicated-`Vec2` HitScene initializer no longer double-releases its
child. All 301 fixture queries, 10,000 same-instance queries, two independent
instances, repeated create/dispose, malformed input, and checksum/package
checks pass.
