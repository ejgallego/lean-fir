---
id: FIR-BUG-impure-simpCase-nested-phase-depth
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/LeanIR/Passes/SimpCaseExamples.lean#nestedPhaseDepthCode
regression: Fir/LeanIR/Passes/SimpCaseExamples.lean#nestedPhaseDepthTrace
---

# Summary

FIR's two/three-phase scoped result is closed under non-case syntax but has no
representation for the unbounded phase depth created by nested case kernels.

## Minimal reproduction

`nestedPhaseDepthCode` has an inner folded singleton in its false arm and
`alphaRight` in its true arm. Recursive traversal first turns the false arm
into `alphaLeft`. The parent table then alpha-folds `alphaLeft` with
`alphaRight` and eliminates its own singleton. The resulting schedule contains
more than the single alpha step admitted by `ScopedCodePhaseFactor`.

## Exact commands

```sh
lake build Fir.LeanIR.Passes.SimpCaseExamples
make check
```

## Expected semantics

The proof representation for the transparent recursive traversal should
retain every structural and alpha segment in execution order, admit identity
padding when sibling branches have different phase depths, and compose those
segments at whole-program scope.

## Actual behavior

`ScopedCodePhaseFactor` classifies only structural/alpha and
structural/alpha/structural witnesses. `ScopedCodePhaseResult` supplies the
final structural identity needed to align those two schedules through a
single non-case constructor, but it cannot append a second case-kernel phase
round without discarding an intermediate semantic edge.

## Proof or differential evidence

The attempted universal phase-aware case-kernel lift receives recursively
proved branch results before applying `shadowSimplifyCases`. A three-phase
branch result followed by a three-phase parent result requires sequential
composition; neither `ScopedCodeBifactor` nor `ScopedCodeTrifactor` has a
constructor for that trace. Collapsing adjacent structural legs would require
an unavailable general transitivity theorem for selector-indexed `CodeRel`.

## Semantic impact

The current folded-singleton proof is sound at one case node and through all
surrounding non-case syntax, but it cannot yet justify arbitrary nesting of
alpha-folding case nodes. This blocks the intended universal recursive
correctness theorem; it does not indicate a Lean compiler miscompilation.

## Classification and triage

The transparent shadow and actual Lean pass both reduce the pinned nested
fixture to `alphaLeft`. Lean's traversal order is intentional. The fixed-depth
representation is a FIR proof-architecture limitation, so the issue is
classified as `fir-semantics`.

## Workaround

None required. Each local case factor remains explicit in the phase trace;
no `CodeRel` transitivity or intermediate alpha-phase erasure is assumed.

## Upstream tracking

none

## Resolution and regression

Resolved. `ScopedCodePhaseResult` retains both structural and
alpha identity at its target. `ScopedCodePhaseTrace` records a nonempty
sequence of local rounds, supports sequential composition and explicit
identity padding, and has endpoint/round-count regressions.
`StructuralAlphaStructuralTrace` supplies the matching whole-program semantic
composition theorem for arbitrarily many rounds. `nestedPhaseDepthCode` is
checked against both the transparent shadow and actual Lean pass.

`ScopedCodePhaseTrace.lift` now maps every round through unary recursive
syntax. `ScopedCodePhaseTrace.zip` aligns two child traces and pads only the
shorter endpoint; `scopedCodePhaseTracedOnAlphaReflexive_traversalLaws`
instantiates this construction for every non-case constructor, with an
unequal-depth join-point regression in `mixedDepthJoinTraced`.

`ScopedAltsPhaseTrace` synchronizes recursively transformed alternatives,
including unequal depths, and lifts each synchronized round to its enclosing
case table. `scopedCaseTraceKernelLaws_of_localPhases` appends the exact local
`shadowSimplifyCases` round, while
`scopedCaseBoundarySoundTraceTree_of_localPhases` and
`shadowCode_scopedPhaseTracedTree` expose the reusable universal recursive
boundary under full-tree hygiene.

`nestedPhaseDepthTrace` is the original reproducer closed with two explicit
rounds under a non-vacuous Boolean-tag predicate. Its round-count guard and
the existing transparent/actual-pass result checks pin the regression.
