---
id: FIR-BUG-wasm-none-lazy-source-step-count
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 3407f806ee122cc550913ba60c12e0e4ddbbdc6f
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-30
reproduction: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
regression: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
---

# Summary

`SourceLazyLetResult` classifies a cache miss as exactly four interpreter
steps, but an internal nullary code declaration needs additional steps to
evaluate its body before the cache frame can publish and bind the result.

## Minimal reproduction

`cachedHeapProgram` calls the internal nullary declaration
`FirTalos.Concrete.cachedHeap`. Its body evaluates a natural literal, allocates
a constructor, and returns it. Starting at the caller's generated lazy `let`,
the first four source steps are:

1. stage the named invocation and push the caller binding frame;
2. enter the nullary declaration and push its cache frame;
3. evaluate the literal binding; and
4. evaluate the constructor binding.

The machine is still at the callee's `.return` with both cache and caller
frames pending. It has not reached the caller continuation required by
`SourceLazyLetResult .miss`.

## Exact commands

```text
lake -d integration/talos build FirTalos.ConcreteRuntimeExamples
make talos-check
```

The `cachedHeapFourStepsRemainInCallee` guard in the reproduction file checks
the four-step intermediate state.

## Expected semantics

The source lazy-miss relation should admit any successfully lowered internal
nullary declaration, independently of the number of finite steps required by
its body. It should distinguish the initial failed cache lookup, the callee
evaluation, the cache-frame publication, and the final caller bind
structurally.

## Actual behavior

`LazyCachePath.sourceSteps` assigns `.miss` the constant `4`, and
`SourceLazyLetResult` is only an `ExecSteps` relation indexed by that count.
Four steps are sufficient for a nullary external declaration because the
external response is resumed in the invocation step. They are not sufficient
for internal code declarations, even though lowering caches both families and
the W6 miss theorem is parameterized by a hereditary internal declaration
body.

## Proof or differential evidence

The intended W6 inversion cannot derive cache absence or the semantic
publication equation for an internal declaration: its
`SourceLazyLetResult .miss` premise is uninhabited for the canonical finite
prefix. In contrast, the concrete runtime regression executes
`cachedHeapProgram` successfully and its second call observes the published
value.

## Semantic impact

The current lazy-miss compiler theorem is useful for the fixed-step external
case but cannot establish partial correctness for generated internal
declaration caches such as `cachedHeapProgram`. It also makes hit/miss identity
an incidental step-count convention rather than a structural source
transition, preventing robust source-fact inversion.

## Classification and triage

The executable interpreter and generated concrete runtime agree. The defect is
in the proof-facing FIR semantic wrapper in
`FirTalos/Correctness/Semantics.lean`, so this is classified as
`fir-semantics`. Repair changes a shared evaluation contract and must be
coordinated through the integration owner.

## Workaround

none. W6 should not add a per-program execution certificate or duplicate the
source evaluator to mask the fixed-step relation.

## Upstream tracking

none

## Resolution and regression

Fixed. `SourceLazyMissResult` now records the staging step, cache-miss
declaration entry, arbitrary finite *isolated* callee execution, semantic
publication, and caller bind separately. `ExecSteps.withFrameSuffix` lifts the
callee execution under the protected cache and caller-bind frames, so a miss
witness cannot consume or reconstruct those frames. `SourceLazyLetResult.execSteps`
then composes either the exact three-step hit or that structured miss into an
ordinary finite interpreter prefix.

`SourceLazyLetResult.miss_cacheFacts_of_valueEq` derives both the initial
semantic cache absence and exact `RuntimeState.setGlobal` publication equation
from the structured execution. The generated miss theorem uses the absence
fact through `LazyCacheGlobalsRel.emptySlot`, so its zero Wasm flag is no
longer caller supplied.

`cachedHeapFourStepsRemainInCallee` retains the original negative regression.
`cachedHeapSevenStepsPublishAndResume` checks that the same nontrivial internal
declaration now completes its three-step body, publishes the cache entry, and
resumes the caller after seven total steps.
