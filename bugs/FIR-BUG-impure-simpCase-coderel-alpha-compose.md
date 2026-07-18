---
id: FIR-BUG-impure-simpCase-coderel-alpha-compose
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/LeanIR/Passes/SimpCaseExamples.lean#alphaFoldCode
regression: Fir/LeanIR/Passes/SimpCaseCompilerBridge.lean#CaseBoundarySound
---

# Summary

FIR's structural recursive `CodeRel` cannot express a `simpCase` result that
replaces a selected branch by an alpha-renamed equivalent branch.

## Minimal reproduction

`alphaFoldCode` has two constructor arms whose bodies bind distinct
`FVarId`s, `alphaRightId` and `alphaLeftId`, but are accepted as
alpha-equivalent. Lean's pass folds those arms to a default containing
`alphaLeft`. At tag 1 the source selects `alphaRight` while the target selects
`alphaLeft`.

## Exact commands

From a clean checkout:

```sh
lake build Fir.LeanIR.Passes.SimpCaseExamples
lake build Fir.LeanIR.Passes.SimpCaseCompilerBridge
```

The executable fixture confirms the actual compiler result and the local
semantic theorem proves `alphaRight` equivalent to `alphaLeft`, but the
compiler bridge must retain `CaseBoundarySound` as a premise.

## Expected semantics

The whole-pass relation should compose recursive `simpCase` stuttering with
the bidirectional alpha-renaming relation already proved in
`AlphaEqvCode.lean`. The composed relation should relate the source branch to
the folded representative and preserve the appropriate renamed environments.

## Actual behavior

`CodeRel.aligned` requires identical binder metadata at every aligned head,
and `CodeRel.eliminate` requires the selected source branch to be recursively
`CodeRel`-related to the target. Neither constructor can relate `alphaRight`
to `alphaLeft`, even though `CodeRelated` and `CodeEquivalentAt` do.

## Proof or differential evidence

`alphaLocalCodeRelated` constructs the declarative alpha relation and
`alphaFoldTrueCodeEquivalent` closes the local observational proof. The actual
pass and the transparent shadow both produce `alphaFoldExpected`. In contrast,
the generic recursive traversal theorem can reduce all other syntax to the
single `CaseBoundarySound` premise but cannot instantiate that premise for
this fixture using `CodeRel` alone.

## Semantic impact

This is a limitation of FIR's proof relation, not evidence of a compiler
miscompilation. Whole-pass correctness is complete for programs whose case
results inhabit `CodeRel`; alpha-default folding remains outside that theorem
until the two existing simulations are composed.

## Classification and triage

The compiler behavior is intentional and separately checked. The missing
composition lives in FIR's semantic proof architecture, so this is classified
as `fir-semantics`.

## Workaround

Keep `CaseBoundarySound` explicit, prove local alpha-fold equivalence with the
bidirectional transparent checker, and differentially compare the actual pass
with the pinned transparent traversal shadow. Do not weaken `CodeRel` or add a
trusted alpha constructor.

## Upstream tracking

none

## Resolution and regression

Unresolved. Add a composed recursive/alpha machine relation, prove its
non-lockstep bisimulation, discharge `CaseBoundarySound` for default folding,
and turn `alphaFoldCode` into the permanent whole-pass regression.
