---
id: FIR-BUG-impure-case-table-selector-determinism
status: confirmed
classification: upstream-drift
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-16
reproduction: Fir/LeanIR/Passes/AlphaEqvCode.lean#CaseTableNormalizationInvariant
regression: none
---

# Summary

Lean 4.32 exports no impure LCNF case-table invariant strong enough to prove
that each constructor tag and the default selector determine at most one body.

## Minimal reproduction

Construct an impure `LCNF.Cases` value whose alternatives contain two
`.default` entries with different bodies, or two `.ctorAlt` entries with the
same `CtorInfo.cidx` and different bodies. The public inductive type accepts
both values, but either table violates FIR's `CaseTableDeterministic` property.

The pure LCNF checker rejects duplicate constructor *names*, but its local
`hasDefault` flag is assigned and never read. It does not export a theorem
connecting checked pure alternatives, constructor-name/index consistency,
`Alt.toImpure`, and the impure alternatives consumed by `simpCase`.

## Exact commands

From a clean checkout using the pinned toolchain:

```sh
rg -n "partial def checkCases|hasDefault|occurs more than once" \
  ~/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Compiler/LCNF/Check.lean
rg -n "inductive Alt|inductive Cases" \
  ~/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Compiler/LCNF/Basic.lean
lake build Fir.LeanIR.Passes.AlphaEqvCode
```

## Expected semantics

The impure phase boundary used by `simpCase` should expose or preserve a
kernel-facing invariant showing that every constructor tag and the default
selector have at most one associated body. That invariant is exactly what
makes reordering by `LCNF.AlphaEqv.sortAlts` observationally harmless.

## Actual behavior

`LCNF.Cases .impure` stores an unrestricted array. Lean's pure checker tracks
constructor names operationally, does not reject duplicate defaults, and
exports no proposition or preservation theorem usable after `Alt.toImpure`.
Consequently FIR cannot derive selector determinism from any public Lean 4.32
phase invariant.

## Proof or differential evidence

`chooseAlt_sortAlts_eq` is proved from the minimal
`CaseTableDeterministic` premise. Removing that premise admits tables where a
permutation changes which duplicate constructor/default body is selected.
The generic `sortAlts_perm` theorem therefore cannot close the proof alone.

## Semantic impact

This does not show that Lean emits a malformed table for a source program. It
prevents FIR from discharging the last case-normalization premise solely from
the public Lean 4.32 compiler interface. Whole-pass correctness must carry a
named phase bridge until construction and preservation are formalized.

## Classification and triage

This is classified as `upstream-drift`: the intended compiler discipline is
clear from the duplicate-constructor-name check and the transformations that
preserve alternative identities, but the proof-relevant invariant is absent.
The unused `hasDefault` flag is additional evidence of an incomplete checker
boundary, not by itself evidence of a miscompilation on compiler-generated
input.

## Workaround

FIR keeps `CaseTableNormalizationInvariant` as the explicit, minimal phase
bridge. Its only field is `CaseTableDeterministic`; quicksort's permutation
property is proved independently and is not assumed.

## Upstream tracking

none

## Resolution and regression

Unresolved. A complete resolution should define a checked case-table
proposition, reject duplicate defaults, prove constructor-name/index
consistency and preservation through `Alt.toImpure` and impure passes, then
derive FIR's `CaseTableDeterministic` theorem from that proposition.
