---
id: FIR-BUG-wasm-none-endpoint-partial-application-admission
status: candidate
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-10
reproduction: integration/illuminate-hit-scene/Probe.lean
regression: none
---

# Summary

FIR rejects the compiler-generated partial application retained by the real
`Illuminate.HitScene.query` final-LCNF closure.

## Minimal reproduction

Capture `Illuminate.HitScene.query` from clean Illuminate commit
`af088e313eaade90be100aeaf63ddac79a8c1710` through FIR's Lean 4.32 deferred
source view and lower the exact module-wise final-LCNF closure with
`Fir.Wasm.Emit.Source.compileModuleArtifact`.

## Exact commands

```sh
cd integration/illuminate-hit-scene
lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  build IlluminateFirHitScene.Compile
lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  env lean -DmaxHeartbeats=0 Probe.lean
```

## Expected semantics

`Illuminate.endpointToCenter._closed_1` should allocate the ordinary closure
created by partially applying `Illuminate.endpointToCenter._lam_0._boxed` to
its compiler-generated constant. The same declaration is accepted by Lean's
native compiler and is required by the arc hit-testing path.

## Actual behavior

Exact deferred capture succeeds and internalizes matching private lambda
names, yielding 159 reachable declarations and all eight expected geometry
math externals. FIR's supported-domain check then rejects
`Illuminate.endpointToCenter._closed_1`; direct lowering reports:

```text
partial-application argument does not refine its parameter ABI
```

`Illuminate.endpointToCenter` is rejected downstream because it loads the
unsupported closure.

The target's five effective parameters are all `.object`, while the fixed
argument is the `.tobject` result of
`Illuminate.endpointToCenter._closed_1._boxed_const_1`. That constant boxes a
`Float` and is therefore a heap object, but its declaration result remains the
coarse compiler `tobject` kind. Ordinary Lean calls and joins use the common
object-family calling representation; FIR's partial-application boundary
currently requires the directional `actual.refines expected` relation.

## Proof or differential evidence

The rejection occurs before resident-runtime linking or external-engine
execution. `Probe.lean` records the exact declaration, parameter, argument,
and external inventories without changing Illuminate's source.

## Semantic impact

This blocks the real prepared HitScene query before the 301-case geometry
fixture can exercise the resident `Float.abs`, `sqrt`, trigonometric, `cbrt`,
and `floor` implementations.

## Classification and triage

Compiler admission/ABI refinement. A generic repair must either propagate the
precise heap-object result through the boxed constant declaration or justify
the same object-family compatibility at closure capture/projection boundaries.
The latter also affects W6's concrete closure-projection refinement premise,
so it must not be weakened locally as an application workaround.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Candidate repair: lowering now derives an effective singleton result kind for
an internal declaration when a straight-line body proves a strict refinement
of its public `tobject` annotation. The analysis is deliberately conservative:
it follows parameter and let-value kinds to the return, and retains the public
kind at joins, branches, externals, or incompatible results.

Named-call locals, declaration results, partial-application checking, and lazy
cache slots use that effective kind. The focused source regressions distinguish
the boxed-Float case (refined to `object`) from a `tobject` declaration that
returns a tagged natural (not refined). The real HitScene probe now captures
159 declarations with 34 externals and zero unsupported declarations.

The candidate preserves FIR's directional semantic refinement rather than
making arbitrary `tobject` values acceptable as heap objects. Landing remains
pending the W6 adaptation of the concrete lazy-cache correctness theorem and
the complete integration gate.
