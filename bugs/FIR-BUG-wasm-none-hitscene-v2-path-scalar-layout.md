---
id: FIR-BUG-wasm-none-hitscene-v2-path-scalar-layout
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-11
reproduction: integration/illuminate-hit-scene/package-smoke.mjs
regression: integration/illuminate-hit-scene/package-smoke.mjs
---

# Summary

The HitScene source-view publisher can link stale v1 final LCNF while claiming
the pinned v2 Illuminate source identity in package metadata.

## Minimal reproduction

Compile `Illuminate.HitScene.query` from Illuminate revision
`88dcfee895a55e804641bff485024cffec1b5419`, encode the v2 mixed-geometry
fixture with the retained path bounds, and run its first substantive query.
The entry traps with `unreachable` before returning a `HitSceneResult` because
the adapter supplies the valid v2 constructor layout to a stale v1 module.

## Exact commands

```sh
cd integration/illuminate-hit-scene
FIR_ALLOW_DIRTY_PACKAGE=1 \
FIR_HIT_SCENE_REUSE_FRONTIER=1 \
ILLUMINATE_ROOT=/tmp/illuminate-hit-scene-v2 \
ILLUMINATE_HIT_SCENE_FIXTURE=/absolute/path/to/hit-scene-benchmark.json \
  node package.mjs
```

## Expected semantics

The adapter should encode the raw Lean 4.32 `HitPrimitive.path` value with its
path object, `hasFill`, `strokeWidth`, and four retained binary64 bounds. Every
fixture query should agree with the Illuminate oracle.

## Actual behavior

Source capture and resident linking initially completed with the exact v1
inventory: 159 declarations, 34 reviewed externals, 439 frontier functions,
and 15 runtime imports. The final-LCNF dump projected only `strokeWidth` and
`hasFill`, despite the package metadata pinning v2. Lake's module trace showed
that its elaborated configuration still named the prior v1 source root.

## Proof or differential evidence

The v1 package passes the same real-engine smoke. A clean module rebuild still
reused the old source root until Lake was invoked with `--reconfigure`. With
reconfiguration, final LCNF projects the four bound fields at offsets 8, 16,
24, and 32, the Bool at offset 40, and all 301 v2 fixture queries pass.

## Semantic impact

Any external-source package can publish code from a prior configured root while
recording the newly validated Git revision and file hashes in `BUILD.json`.

## Classification and triage

This is a W7 package build-provenance bug. `-KilluminateRoot=...` changes a Lake
configuration option, but an existing elaborated lakefile can retain the old
value unless the command also passes `--reconfigure`.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The package publisher passes `--reconfigure` to both the source-view build and
the final-LCNF emission command. `package-smoke.mjs` is the regression: the v2
fixture requires the enlarged constructor, checks every query, and runs 10,000
additional queries with a flat frontier.
