---
id: FIR-BUG-wasm-none-hitscene-lazy-cache-rewind
status: fixed
classification: wasm-runtime
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-10
reproduction: integration/illuminate-hit-scene/package-smoke.mjs
regression: integration/illuminate-hit-scene/IlluminateFirHitScene/Compile.lean
---

# Summary

The HitScene resident module retains compiler-generated lazy singleton globals
while its adapter rewinds the scratch arena after every query. A singleton
first allocated during query one therefore points above the persistent
checkpoint after rewind, and query two reads invalidated storage.

## Minimal reproduction

Create one scene from the canonical 301-query fixture, run the `origin` query,
then run `front-center` through the same instance. The first query succeeds and
initializes cached direction vectors. The adapter rewinds to the scene
checkpoint. The second query faults while reading the stale cached value.

## Exact commands

```sh
cd integration/illuminate-hit-scene
FIR_HIT_SCENE_REUSE_FRONTIER=1 FIR_ALLOW_DIRTY_PACKAGE=1 node package.mjs
```

## Expected semantics

A rewindable resident consumer must not retain a root above its checkpoint.
Compiler-generated closed singletons must either be allocated below the
checkpoint or rebuilt in the current arena on every use.

## Actual behavior

The unconfigured source module publishes the first query's singleton address
in a module global. The arena rewind invalidates that address without clearing
the global.

## Proof or differential evidence

The first query agrees with the fixture. The second query traps in the cached
`Vec2.west` path. Running the same queries in fresh instances succeeds, which
distinguishes retained module state from input encoding and pure geometry.

## Semantic impact

Any scratch-rewinding package can retain dangling lazy-cache roots across
calls. This violates the package ownership contract even when each individual
query is otherwise correct.

## Classification and triage

This is a W7 package-configuration omission. FIR already provides the
fail-closed `ResidentCache.eliminateLazyInitializers` transform, used by the
Illuminate live-player packages for the same ownership model. HitScene must
apply that API before resident linking.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The HitScene base module now calls
`ResidentCache.eliminateLazyInitializers` before resident linking, exactly as
the accepted Illuminate live-player packages do. No lazy cache global survives;
fresh closed graphs are recursively published as persistent by the repaired
transform. The package smoke runs all 301 queries in one instance and then
10,000 additional queries with the post-rewind frontier equal to the persistent
scene checkpoint.
