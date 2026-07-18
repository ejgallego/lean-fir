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
lake build Fir.LeanIR.Passes.SimpCaseScopedBridge
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

`SimpCaseScopedBridge` now supplies the missing recursive interface. Its
`ScopeIndex` tracks forward and backward renamings plus variable and join
scopes; `shadowCode_scopedRelated` updates that index through ordinary,
parameter, and join binders and delegates only case nodes to
`ScopedCaseBoundarySound`. `ScopedCodeBifactor` states the semantic payload as
a structural intermediate followed by `CodeRelated` in both orientations.
`alphaFoldScopedCaseBoundary` proves that the alpha-folding fixture inhabits
this case contract directly, and the declaration-level alpha proof consumes
the factor's two scoped alpha fields.

`ScopedCodeFactoredOnAlphaReflexive` now makes declaration hygiene an explicit
premise instead of asserting that arbitrary indices are scoped. From that
evidence, `scopedCodeFactoredOnAlphaReflexive_traversalLaws` proves closure
through every non-case constructor, including ordinary binders, parameter
lists, join bodies and continuations, and all impure ownership instructions.
`nestedAlphaFoldScopedTraversal` is the regression that lifts the
alpha-changing case factor through a non-case parent using those generic laws.

Attempting to discharge `ScopedCaseBoundarySound` without another phase
premise exposed a smaller counterexample: take an empty case table and
`validCase := fun _ _ => True`. The transparent simplifier returns `unreach`,
but `CodeRel.eliminate` cannot justify any promised tag because the source has
no selected arm. Alpha reflexivity still holds for the empty table, so hygiene
alone cannot rule this case out. The universal theorem must therefore consume
an explicit case-admissibility/kernel law connecting `validCase` to the
source table and the simplifier result.

The recursive proof also exposed an independent syntactic requirement. The
alpha case relation is selector-based, so root reflexivity need not mention a
shadowed alternative, while `shadowCode?` still transforms every array entry.
`ScopedAlphaBireflexiveTree` now records hygiene for the complete syntax tree.
`ScopedCaseAdmissibilityLaws` isolates the remaining phase fact at the
nonrecursive simplifier boundary, and
`scopedCaseBoundarySoundTree_of_admissibility` lifts it to the universal
recursive boundary. `shadowCode_scopedFactoredTree` then factors any
successful recursive shadow run under those explicit premises.

`ScopedCaseShapeLaws` now decomposes the phase premise along the compiler's
empty, singleton, and retained outputs and assembles it back into
`ScopedCaseAdmissibilityLaws`. For retained tables,
`ScopedRetainedPhaseEvidence` reduces the proof to phase-valid structural
selection plus `ScopedAddDefaultSelectionEvidence`, the exact bidirectional
alpha relation between a structural middle and the prepared compiler table.
Unreachable filtering preserves both concrete reachable selections and
pointwise alpha relations. No-fold `addDefaultAlt` paths discharge the fold
witness automatically.

## Semantic impact

This was a limitation of FIR's generic compiler-bridge relation, not evidence
of a compiler miscompilation. The concrete alpha-default-folding fixture is
covered both by the composed whole-program theorem and by the new scoped
case-node contract. Closure through surrounding recursive syntax is now
generic under explicit full-tree alpha-reflexivity evidence. Arbitrary shadow
results are covered by the universal theorem once the phase supplies
`ScopedCaseAdmissibilityLaws`; the boundary remains intentionally invalid for
an unconstrained `validCase`.

## Classification and triage

The compiler behavior is intentional and separately checked. The missing
composition lives in FIR's semantic proof architecture, so this is classified
as `fir-semantics`.

## Workaround

Use `StructuralThenAlphaPrograms` for proof-produced program intermediates,
`ShadowThenAlphaPrograms` when the transparent shadow produces that
intermediate, and `ScopedCodeBifactor` at alpha-changing case nodes. Keep the
appropriate case boundary explicit and continue to compare the actual pass
with the pinned traversal shadow. Do not weaken `CodeRel` or add a trusted
alpha constructor.

## Upstream tracking

none

## Resolution and regression

Partially resolved. `ProgramsRelated` relates named declarations across
distinct programs, including partial-application arities and external ABIs;
its bidirectional machine simulation proves whole-program observational
equivalence. `SimpCaseAlphaBridge` makes structural-then-alpha composition
generic, and `alphaFoldComposedCorrect` is now only a witness instantiation.

The scope-indexed case-boundary interface and concrete alpha-fold regression
are now implemented. Full-tree hygiene supplies every recursive branch
certificate, `ScopedCaseShapeLaws` supplies the phase-local selection facts by
compiler output shape, and the generic theorem lifts them through arbitrary
recursive shadow traversal. `nestedEmptyCaseFactored_of_shapes` exercises the
complete assembly through a non-case parent. Concrete folded tables still
need the private `addDefaultAlt` output equation; connecting that fact and the
shadow theorem to the actual private pass remains the separate upstream
proof-interface issue.
