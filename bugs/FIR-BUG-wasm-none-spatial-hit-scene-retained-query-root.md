---
id: FIR-BUG-wasm-none-spatial-hit-scene-retained-query-root
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-13
reproduction: integration/illuminate-spatial-hit-scene/package-smoke.mjs
regression: integration/illuminate-spatial-hit-scene/package-smoke.mjs
---

# Summary

The first spatial HitScene package exported
`Illuminate.SpatialHitScene.query` with its ordinary owned root parameter and
then attempted to reuse one retained `SpatialHitScene` address across browser
queries. The first query traps in the resident closure-application path.

## Minimal reproduction

Encode the `bounds-small` fixture as a persistent `HitScene`, execute the real
`Illuminate.SpatialHitScene.ofHitScene` once in Wasm, retain its returned
`SpatialHitScene`, and call the raw `Illuminate.SpatialHitScene.query` export
at coordinates `(0, 0)`. Preparation succeeds, but the query traps before
returning the expected tag `{ value := 10, label := "text" }`.

## Exact commands

From `integration/illuminate-spatial-hit-scene`:

```sh
ILLUMINATE_ROOT=/home/egallego/lean/illuminate/.worktrees/vir-hit-scene \
FIR_ALLOW_DIRTY_PACKAGE=1 node package.mjs
```

## Expected semantics

The persistent browser handle borrows the prepared spatial root for each
query. The real Illuminate query executes without consuming the retained root,
copies its `HitSceneResult` to JavaScript, and leaves the scene valid for the
next query.

## Actual behavior

The package exposes the source declaration's ordinary owned parameter as a
reusable host call. Wasm preparation succeeds, but the first query reaches an
`unreachable` in the resident closure-application path. The raw entry contract
does not express that the host intends to retain and repeatedly borrow the
root.

## Proof or differential evidence

The production closure captures 193 declarations and 41 reviewed externals,
links 777 resident functions, closes all runtime operations, and retains only
the accepted 15 Float/libm imports. The corresponding reference HitScene
package accepts the same encoded graph, and Illuminate's reference and spatial
VIR implementations agree on all 1,009 fixture queries. The failing query is
the first `bounds-small/text-center` oracle point.

## Semantic impact

Without an explicit borrowed application boundary, a persistent native scene
handle cannot safely call the real spatial query repeatedly. Treating an owned
entry as borrowed in JavaScript would silently disagree with Lean's ownership
semantics.

## Classification and triage

This is an adapter/application-boundary defect, not evidence that
`SpatialHitScene.query` computes the wrong geometric result. The browser API
needs a Lean-compiled borrowed facade so upstream ExplicitRC, rather than host
convention, establishes root lifetime.

## Workaround

None. Do not mark arbitrary Wasm-produced graphs persistent from JavaScript or
skip reference-count operations.

## Upstream tracking

none

## Resolution and regression

`IlluminateFirSpatialHitScene.queryBorrowed` is the thin persistent-host ABI:
its `SpatialHitScene` parameter is annotated borrowed and its body immediately
calls the real `Illuminate.SpatialHitScene.query`. FIR compiles the façade and
`ofHitScene` together through Lean's generic final-LCNF pipeline and exports
only the façade's bit-exact Float transport.

The package smoke passes all 1,009 shared-oracle queries, then 10,000 queries
on one retained scene with an unchanged post-rewind checkpoint. Two scenes,
repeated create/dispose, use-after-dispose rejection, malformed input, and
package checksums also pass. The complete 95,995-byte module has zero imports
and owns its memory.
