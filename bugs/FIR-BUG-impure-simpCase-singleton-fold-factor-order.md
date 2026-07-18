---
id: FIR-BUG-impure-simpCase-singleton-fold-factor-order
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/LeanIR/Passes/SimpCaseExamples.lean#alphaSingletonFoldCode
regression: Fir/LeanIR/Passes/SimpCaseExamples.lean#alphaSingletonFold_hasNoStructuralConvergence
---

# Summary

FIR's scoped `simpCase` factor currently assumes one structural rewrite
followed by one alpha-equivalence step. Lean 4.32 can instead fold two
alpha-equivalent alternatives to a singleton default and immediately eliminate
that default, requiring structural, alpha, and structural steps in that order.

## Minimal reproduction

`alphaSingletonFoldCases` contains two constructor alternatives. Their bodies
return the same value but bind distinct `FVarId`s, so Lean's `Code.alphaEqv`
accepts them while structural `CodeRel` cannot identify them. The transparent
compiler shadow evaluates this table directly to `alphaLeft`.

Both tags are phase-valid. Consequently
`ScopedSingletonSelectionConvergence` would need one structural middle related
from both `alphaLeft` and `alphaRight`. The theorem
`alphaSingletonFold_hasNoStructuralConvergence` proves that no such witness
exists: inversion of `CodeRel` preserves each leading let declaration, forcing
the distinct binder identifiers to be equal.

## Exact commands

```sh
lake build Fir.LeanIR.Passes.SimpCaseExamples
make check
```

## Expected semantics

The proof relation should represent the local compiler sequence explicitly:

1. recursively transform the alternative bodies structurally;
2. alpha-fold the transformed table to a singleton default;
3. structurally eliminate the singleton case.

Selection-local evidence may choose different structural branch intermediates
before the common alpha representative. It must not require the distinct
source branches to converge structurally before alpha renaming.

## Actual behavior

`ScopedCaseSelectionSurvivalLaws.singleton` returns
`ScopedSingletonSelectionConvergence`, whose single `middle` precedes the alpha
step. This shape can prove a pre-existing singleton but cannot prove the real
fold-and-eliminate path above.

## Proof or differential evidence

The executable `#guard` for `alphaSingletonFoldCases` confirms that
`shadowSimplifyCases` returns `alphaLeft`. The negative kernel theorem uses
only `CodeRel` inversion and the distinct binder names; it does not rely on an
unproved compiler-output equality.

## Semantic impact

This is a limitation of FIR's proof architecture, not evidence of a Lean
miscompilation. It blocks an honest construction of the remaining concrete
singleton phase law for compiler-generated alpha-folding cases.

## Classification and triage

The compiler behavior is intended. FIR compressed three semantic phases into
two, so the issue is classified as `fir-semantics`.

## Workaround

Do not postulate `ScopedSingletonSelectionConvergence` for folded singletons.
Use `ScopedSingletonPhaseEvidence.direct` for a pre-existing singleton and
`ScopedSingletonPhaseEvidence.folded` with `ScopedCodeTrifactor` for a
fold-created singleton. Recursive clients use
`ScopedCodePhaseResultOnAlphaReflexive`; its target structural identity pads a
two-phase child when a sibling needs the final structural phase.

## Upstream tracking

none

## Resolution and regression

Resolved on the proof track. `ScopedCodeTrifactor` explicitly records
structural, alpha, and final structural legs; `ScopedCodePhaseFactor`
classifies the old two-phase and corrected three-phase paths; and
`ScopedSingletonPhaseEvidence` exposes both direct and folded singletons.

`ScopedCodePhaseResult` adds the target structural identity needed to align
independently transformed children and now also retains target alpha identity
for later multi-round padding. The generic
`scopedCodePhaseResultOnAlphaReflexive_traversalLaws` now covers every
non-case constructor, including a `jp` whose body is three-phase and whose
continuation is two-phase. `scopedCodePhaseResult_caseBoundary_iff_kernel`
reduces recursive correctness to the local phase-aware case kernel, and
`shadowCode_scopedPhaseFactored_of_caseKernel` exposes the resulting phase
factor.

At whole-program scope, `StructuralAlphaStructuralPrograms` and
`structuralAlphaStructuralSamePhaseCorrectOn` consume both structural legs
with separate readiness obligations around the existing alpha theorem.
`alphaSingletonComposedCorrect` instantiates that composition for the exact
fold-created singleton fixture. The permanent regressions are
`alphaSingletonFold_hasNoStructuralConvergence`,
`nestedAlphaSingletonFoldPhaseFactored`, `mixedPhaseJoinFactored`, and the
corresponding actual-pass fixture checks.
