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

The follow-up `ScopedCasePhaseShapeLaws` contract now splits the remaining
local simplifier premise into empty, phase-classified singleton, and retained
output evidence. `scopedLocalCasePhaseLaws_of_shapes` derives the local law by
following `shadowSimplifyCases`' decision tree, and
`shadowCode_scopedPhaseTracedTree_of_phaseShapes` feeds those independent
shape proofs directly into arbitrary recursive traversal. Examples cover
empty, direct-singleton, fold-created-singleton, and retained-table result
packaging.

The bundled shape premise has since been decomposed one level further.
`ScopedCaseEmptySelectionLaws` states only empty-table selection survival;
`ScopedCaseSingletonPhaseLaws` preserves the direct/folded classification;
`ScopedCaseRetainedPhaseLaws` contains only retained-table folding evidence;
and `ScopedCasePhaseTargetIdentityLaws` isolates the endpoint identities used
for trace padding. `scopedCasePhaseShapeLaws_of_components` is the lossless
assembly theorem, while
`shadowCode_scopedPhaseTracedTree_of_phaseComponents` exposes those four
independent obligations at the universal recursive endpoint. The empty-table
and nested recursive examples exercise the unbundled path directly.

The empty-table component is now discharged from a lower semantic invariant.
`ReachableCaseTag` says that a phase-valid runtime tag selects an existing,
non-`unreach` source arm, and `ScopedCaseReachableSelectionLaws` lets custom
validity predicates refine that canonical predicate. The transparent
preparation lemmas prove that unreachable filtering preserves the selected
arm and that default folding never erases its final survivor. Consequently,
`scopedCaseEmptySelectionLaws_of_reachableSelection` derives the former empty
shape assumption, while
`shadowCode_scopedPhaseTracedTree_of_reachableSelection` reaches the universal
recursive theorem with only singleton, retained-table, and target-identity
components left. Regressions include a non-vacuous reachable default arm, an
empty table rejected by canonical validity, and the reduced recursive API.

The ordinary singleton path is now discharged as well. The recursive
alternative trace exposes a pointwise endpoint identity round, preserving
hygiene and structural reflexivity for every array entry rather than only the
entries observable through `chooseAlt`. This matters for shadowed alternatives
that root-level `CodeRelated.cases` intentionally hides. When unreachable
filtering has size one, `shadowAddDefaultAlt` is inert, reachable validity
forces every valid selection to that sole body, and the pointwise identity
supplies its two alpha directions. `ScopedCaseFoldedSingletonPhaseLaws`
therefore contains only prepared singletons created by genuine default
folding, and `shadowCode_scopedPhaseTracedTree_of_foldedSingletons` exposes
that reduced contract at the universal recursive endpoint. The remaining
proof frontier is fold-created singleton evidence, retained-table folding,
and the corresponding target identities.

Fold-created singleton evidence has now been reduced to its genuine alpha
boundary. Compiler-shape lemmas prove that a singleton created from a
non-singleton filtered table came from an input of size at least two, is
exactly one default arm, and selects that arm at every tag.
`ScopedFoldedAlphaEvidence` exposes only a selection-preserving proof
intermediate plus the bidirectional selected-branch alpha relation for
`shadowAddDefaultAlt`; reachable selection and the recursive pointwise
identity round derive the first structural leg, while the singleton shape and
target structural identity derive the final elimination leg.
`scopedCaseFoldedSingletonPhaseLaws_of_reachableSelectionAndAlpha` therefore
constructs the former broad trifactor contract, and
`shadowCode_scopedPhaseTracedTree_of_foldedAlpha` carries the smaller alpha
contract to the universal recursive endpoint. The alpha-singleton fixture
pins both the compiler shape and the selection-preserving intermediate. The
remaining frontier is construction of the general fold-alpha presentation,
retained-table folding, and the shared target identities; no folded
three-phase factor is assumed by the preferred recursive API.

The fold-alpha frontier is now split at the exact executable boundary. The
proof-only intermediate is the filtered table with the occurrence-count
representative appended as a default; generic lookup lemmas prove that this
append preserves every successful source selection and supplies the fallback
when selection previously failed. The transparent maximum loop now also
exposes that its representative is a real source-table member.

For a fold-created singleton, kernel theorems show that the actual shadow
output is exactly that representative as one default and that every removed
alternative passed Lean's upstream alpha check against it. Consequently
`chooseAlt_foldCreatedSingleton_alpha` classifies every tag: the intermediate
and folded tables select real endpoint bodies that are either identical or
the exact checked alpha pair. `scopedCaseAddDefaultAlphaLaws_of_transport`
uses the recursive pointwise endpoint identities to discharge all table and
selector bookkeeping. The remaining fold obligation is now the uniform
`ScopedFoldAlphaTransportLaws`: transport one successful upstream body check,
plus the endpoint hygiene/normalization evidence, to the two scoped
`CodeRelated` orientations. No additional axiom or compiler discrepancy was
introduced by this reduction.

The resolver-transport half of that obligation is now kernel-proved. A new
transparent parametricity layer shows that every primitive check, parameter
traversal, alternative traversal, and the complete fuel-indexed impure local
checker is invariant under extensionally equal totalized resolver lookups.
`ScopeIndex` now records as an intrinsic invariant that both outer maps behave
like the empty map; `empty`, `pushVar`, `pushJoin`, `pushParams`, and `reverse`
preserve the invariant. Consequently the single explicit `UpstreamBridge`
can replay an accepted body comparison under either recursive outer resolver.
The reverse code orientation is now kernel-derived rather than checked again:
`RenamingBijection` follows opposite binder insertions through ordinary and
join scopes, and `codeRelated_symm` reverses the entire declarative relation.
Thus `scopedFoldAlphaTransportLaws_of_upstreamBridge` needs only one audited
upstream check and one forward `CodeSideConditions` witness. The remaining
fold-transport work is precisely construction of those explicit cross-code
side conditions, including normalization for nested case tables; that fact is
not being inferred from endpoint identities alone.

The forward side obligation is now factored more precisely. Recursive
`CodeRuntimeTypesEq` carries only the exact declaration-result and boxed-scalar
types observed by FIR's current runtime relation; Lean's checker establishes
only type alpha-equivalence, so these cross-code equalities remain explicit.
All unary scope, freshness, and case-normalization premises instead come from
`ScopedCodeSideReflexive` endpoint certificates.
`CodeRuntimeTypesEq.sideConditions` kernel-combines the two sources, and
`scopedFoldAlphaSideLaws_of_endpoints` feeds the result into the existing
single-check transport theorem. The transparent ordered-alternative proof now
also exposes constructor/default body checks after sorting and transports them
back through deterministic table permutations. The next step is to thread the
endpoint certificates and exact runtime-type compatibility through the
recursive phase result, rather than reintroducing the original monolithic
side-condition assumption.

The stronger invariant now has a non-lossy trace carrier. A
`ScopedCodeTargetCertificate` packages structural identity, alpha identity,
and `ScopedCodeSideReflexive`; certified code and alternative phase results
retain it at every round. Certified traces implement append, padding, sibling
depth synchronization, pointwise target lookup (including shadowed entries),
and erasure back to the established phase traces. The full-tree alternative
kernel has a certified synchronization theorem, and
`ScopedFoldAlphaCertifiedTransportLaws` consumes the resulting per-body
certificates directly. Its only remaining cross-code input is
`ScopedFoldRuntimeTypeLaws`; the audited upstream bridge is still called once
and reverse alpha remains derived by `codeRelated_symm`. The certified
default-fold law now uses the two concrete body certificates selected from
that recursive result, so it no longer assumes a global recovery principle
from weaker endpoint identities. This certified result has been lifted to the
folded-alpha interface; the next step is to carry it through singleton and
retained-case reconstruction.
