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
reproduction: Fir/LeanIR/Passes/SimpCaseCorrectness.lean
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
checks representative outputs. The missing public transformation graph is the
remaining link between those two facts.

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
explicit. Do not duplicate the effectful compiler pass or add a trusted axiom.

## Upstream tracking

none

## Resolution and regression

Unresolved. Once the kernels or graph theorems are public, prove
`filterUnreachable` equal to `removeUnreachable`, connect `addDefaultAlt` to
bidirectional alpha equivalence, and compose the public recursive traversal
with `SimpCaseCorrectness`.
