---
id: FIR-BUG-wasm-none-self-tail-local-reinitialization
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-11
reproduction: integration/illuminate-hit-scene/package.mjs
regression: Fir/Wasm/Emit/TailCall.lean
---

# Summary

Generic direct self-tail-call elimination can change an Illuminate HitScene
query result because a loop iteration reuses Wasm locals that a real recursive
call would initialize afresh.

## Minimal reproduction

Compile `Illuminate.HitScene.query` with the generic closed-application policy,
including `directSelfTailCallsAvailable`, and run the accepted 301-query
HitScene fixture. Query `grid-8-5` is the first observed mismatch.

## Exact commands

```sh
cd integration/illuminate-hit-scene
FIR_ALLOW_DIRTY_PACKAGE=1 \
ILLUMINATE_ROOT=/tmp/illuminate-hit-scene-pinned \
ILLUMINATE_HIT_SCENE_FIXTURE=/path/to/hit-scene-benchmark.json \
  node package.mjs
```

## Expected semantics

`grid-8-5` returns the fixture's tagged result `{ kind: "tag", value: 1,
label: "back" }`, as it does before direct self-tail-call elimination.

## Actual behavior

The packaged smoke test receives `{ kind: "something" }`. The complete module
also changes from 45,595 to 45,621 bytes, confirming that the optional generic
tail transform rewrote this closure.

## Proof or differential evidence

The package smoke compares all decoded `HitSceneResult` values with the
runtime-neutral fixture and fails at `grid-8-5`. The same package and fixture
pass with the corrected transform, as they did before generic direct
self-tail-call elimination was enabled.

## Semantic impact

Any transformed self-recursive function that reads a local before assigning it
on every path can observe a value retained from the previous loop iteration.
A normal Wasm call creates fresh zero-initialized locals, so the current loop
rewrite does not preserve the function-call semantics in that case.

## Classification and triage

This is a W7 symbolic-Wasm transform defect, not an Illuminate state-machine or
adapter discrepancy. The missing invariant was reinitialization of every
non-parameter local before branching to the synthetic function-body loop.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The transform now assigns the evaluated recursive arguments to parameters,
then writes the appropriate Wasm zero value to every non-parameter local before
branching to the synthetic loop. Its structural guard covers i32, i64, f32,
and f64 zero construction and checks that the generated restart sequence resets
the example result local.

The complete HitScene package is the differential regression: all 301 fixture
queries, including `grid-8-5`, and 10,000 flat-frontier queries pass with the
generic tail transform enabled. The resulting 45,621-byte module has zero
imports and SHA-256
`2bfe26020afe22c0f965bf85dcfd1c9f7aea4deb55ce44815fb937eb696698aa`.
