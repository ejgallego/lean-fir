---
id: FIR-BUG-impure-simpCase-private-proof-interface
status: confirmed
classification: upstream-drift
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-17
reproduction: Fir/LeanIR/Passes/SimpCaseCompilerBridge.lean#CaseBoundarySound
regression: Fir/LeanIR/Passes/SimpCaseExamples.lean#checkFixtures
---

# Summary

Lean 4.32 keeps the impure `simpCase` transformation kernels module-private,
so a downstream kernel proof cannot state correspondence lemmas for the
compiler's `filterUnreachable`, `addDefaultAlt`, `simplifyCases`, or recursive
`Code.simpCase` definitions.

## Minimal reproduction

Import the public module containing `LCNF.simpCase` and try to state:

```lean
theorem filter_spec (alts : Array (LCNF.Alt .impure)) :
    (LCNF.filterUnreachable alts).toList =
      SimpCase.removeUnreachable alts.toList := by
  sorry
```

Lean reports `Unknown identifier LCNF.filterUnreachable`. The definition is
present in the upstream source, but it is not marked `public`. The same is true
of `addDefaultAlt`, `simplifyCases`, and `Code.simpCase`; only the final pass
value and `ensureHasDefault` are exported.

## Exact commands

From a clean checkout using the pinned toolchain:

```sh
rg -n "^(partial )?def (filterUnreachable|addDefaultAlt|simplifyCases)|public def simpCase" \
  ~/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Compiler/LCNF/SimpCase.lean
lake build Fir.LeanIR.Passes.SimpCaseCorrectness
```

The failed declaration above stops at name resolution, before the equality
proof can inspect the transparent filter implementation.

## Expected semantics

The pass should export its transformation kernels, or public graph/equation
theorems for them, so downstream proofs can connect each actual compiler
rewrite to a semantic specification and compose those results through
declarations.

## Actual behavior

`LCNF.simpCase` can be executed through the pass manager, but its intermediate
results cannot be related to the local rewrite specifications inside the
kernel. The recursive `Code.simpCase` is additionally an opaque `partial def`,
so merely exporting its name without safe equations would still leave the
whole-code induction blocked.

## Proof or differential evidence

FIR proves semantic correctness for selected-arm elimination, unreachable-arm
removal, singleton elimination, and bidirectional alpha-equivalent default
folding. `SimpCaseExamples.checkFixtures` also executes Lean's actual pass and
checks representative outputs. `SimpCaseCompilerBridge` now ships a total,
fuel-indexed shadow of the returned-syntax traversal and proves that every
non-case recursive edge, declaration, and declaration array lifts to
`ProgramRelated CodeRel`; the only remaining kernel premise is the named
`CaseBoundarySound` obligation. The executable regression compares the actual
pass with that shadow over the rewrite fixtures, a nested closed program, and
an array spanning every impure `Code` constructor. The missing public
transformation graph is the remaining link between those facts.

`SimpCaseAlphaBridge` now composes a proved structural intermediate with
whole-program bidirectional alpha equivalence, and offers the same corollary
for a transparent-shadow run. This closes the semantic composition layer
without pretending to prove that Lean's private traversal produced the
intermediate. The upstream correspondence boundary therefore remains explicit.

`SimpCaseScopedBridge` separately tracks the two alpha-renaming maps, variable
scopes, and join scopes through recursive traversal. The alpha-fold fixture's
case contract is now kernel-proved, while its concrete shadow output remains
an executable guard: Lean 4.32 exposes `LCNF.Code.beq` as opaque and provides
no `LawfulBEq` instance with which to turn that Boolean result into a kernel
syntax equality. This is additional evidence for retaining the explicit
compiler-correspondence boundary rather than adding an axiom.

The downstream non-case traversal gap is also closed:
`ScopedCodeFactoredOnAlphaReflexive` consumes explicit hygiene evidence and
lifts the structural/alpha factor through every recursive non-case
constructor. `ScopedCaseKernelLaws` now separates successful recursive branch
transformation from the nonrecursive `shadowSimplifyCases` step, and its
equivalence theorem lifts that local law to the old universal boundary.
`ScopedAlphaBireflexiveTree` supplies hygiene for every syntactic alternative,
including selector-shadowed entries. `ScopedCaseAdmissibilityLaws` packages
the admissible local case result, and the kernel now proves both the universal
`ScopedCaseBoundarySound` consequence and factoring of arbitrary successful
recursive shadow runs. The remaining phase obligation is to construct this
law from its concrete case-table invariant—not to assert an unconditional
theorem for arbitrary `validCase`.

The transparent bridge also names the unreachable filter and prepared
alternative array, proves the filter equal to FIR's list specification, and
exports equations for the empty, singleton, and retained-case output shapes.
These lemmas reduce the next phase proof to selection and default-fold facts;
they do not widen the trusted compiler-correspondence boundary.

The shape split is now formalized by `ScopedCaseShapeLaws`, which derives the
universal admissibility law and arbitrary recursive factoring theorem.
Filtering is kernel-proved to preserve reachable selections and alpha-related
alternative lists. `ScopedAddDefaultSelectionEvidence` names the exact
remaining fold relation; small tables and tables with an existing default are
proved unchanged and obtain this relation without trust. For the alpha-fold
fixture, `alphaFoldRetainedPhaseEvidence_of_output` closes every structural
and alpha obligation from one explicit equation identifying the private fold
output. The executable guard confirms that equation, but opacity prevents it
from becoming a kernel theorem.

## Semantic impact

This is a proof-interface gap, not evidence that the pass miscompiles a valid
program. Until the gap is closed, FIR can prove the rewrite specification and
differentially confirm compiler outputs, but cannot derive a kernel theorem
whose premise is an actual `LCNF.simpCase` execution.

## Classification and triage

This is `upstream-drift`: the visibility and opacity choices live in Lean
4.32's compiler module. A minimal upstream repair would export the three
nonrecursive kernels and a total relation or safe equation theorem describing
recursive code/declaration traversal.

## Workaround

Keep the semantic rewrite theorems in FIR, exercise the real pass with
compiler-generated fixtures, and make the unproved correspondence boundary
explicit. FIR's transparent shadow copies only the returned-syntax
calculation, omits the compiler-state `eraseCode` effects, reports fuel
exhaustion instead of using `partial`, and reduces the kernel boundary to
`CaseBoundarySound`. `scripts/validate_trusted_assumptions.py` pins the audited
Lean 4.32 `SimpCase.lean` source hash. Do not duplicate the effectful compiler
pass or add a trusted axiom.

## Upstream tracking

none

## Resolution and regression

Unresolved, but narrowed to compiler correspondence and the folded-table
output equation consumed by the phase-specific shape law. Downstream
structural-then-alpha composition, full-tree traversal, pointwise alternative
factoring, shape-law assembly, and the kernel-to-boundary lift are reusable.
The unreachable-filter and no-fold `addDefaultAlt` paths are kernel-proved.
Once the private kernels or graph theorems are public, prove the genuine fold
equation and replace executable actual-vs-shadow checks with a kernel
correspondence theorem.
