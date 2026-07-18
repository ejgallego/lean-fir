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
regression: Fir/LeanIR/Passes/SimpCaseExamples.lean#alphaFoldComposedCorrect
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
lake build Fir.LeanIR.Passes.SimpCaseAlphaBridge
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
pass and the transparent shadow both produce `alphaFoldExpected`.

`SimpCaseAlphaBridge.StructuralThenAlphaPrograms` now packages this factorization
at whole-program scope. `alphaFoldComposedCorrect` instantiates the reusable
theorem through `alphaFoldIntermediateProgram`: recursive `CodeRel` stuttering
replaces the selected source cases with a default holding `alphaRight`, then
the program-aware alpha bisimulation renames that default to `alphaLeft`.

`ShadowThenAlphaPrograms` additionally lifts any transparent traversal run to
the same theorem while retaining `CaseBoundarySound` as an explicit field.
The traversal theorem still cannot instantiate that premise directly for an
alpha-default fold: `CaseBoundarySound` has no declaration-local variable or
join scopes with which to state `AlphaEqv.CodeRelated`.

## Semantic impact

This is a limitation of FIR's generic compiler-bridge relation, not evidence
of a compiler miscompilation. The concrete alpha-default-folding fixture is
now covered by a composed whole-program theorem. Arbitrary shadow traversal
results remain outside the generic theorem when their case boundary needs an
alpha step.

## Classification and triage

The compiler behavior is intentional and separately checked. The missing
composition lives in FIR's semantic proof architecture, so this is classified
as `fir-semantics`.

## Workaround

Use `StructuralThenAlphaPrograms` for proof-produced structural intermediates,
and `ShadowThenAlphaPrograms` when the transparent shadow itself produces that
intermediate. Keep `CaseBoundarySound` explicit and continue to compare the
actual pass with the pinned traversal shadow. Do not weaken `CodeRel` or add a
trusted alpha constructor.

## Upstream tracking

none

## Resolution and regression

Partially resolved. `ProgramsRelated` relates named declarations across
distinct programs, including partial-application arities and external ABIs;
its bidirectional machine simulation proves whole-program observational
equivalence. `SimpCaseAlphaBridge` makes structural-then-alpha composition
generic, and `alphaFoldComposedCorrect` is now only a witness instantiation.

The card stays confirmed for direct compiler traversal. Closing it requires a
scope-indexed case-boundary interface (or an upstream transformation graph)
that can justify the alpha edge produced inside the private recursive pass;
the scope-free `CaseBoundarySound` statement cannot safely express that edge.
