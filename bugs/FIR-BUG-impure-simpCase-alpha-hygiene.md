---
id: FIR-BUG-impure-simpCase-alpha-hygiene
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-16
reproduction: Fir/LeanIR/Passes/SimpCaseExamples.lean#nonHygienicAlphaLeft
regression: none
---

# Summary

FIR's current impure well-formedness predicate is too weak to state Lean's
`Code.alphaEqv` test as semantically sound without a binder-hygiene hypothesis.

## Minimal reproduction

The reproduction defines two code bodies containing two literal bindings and
a return. The left body reuses `x` for both bindings and returns `x`; the right
body binds `y`, then `z`, and returns `y`.

Lean 4.32 reports the bodies as alpha-equivalent. The FIR interpreter returns
the second literal, 6, on the left and the first literal, 5, on the right.

## Exact commands

From a clean checkout:

```sh
lake env lean Fir/LeanIR/Passes/SimpCaseExamples.lean
```

The three `#guard` commands under `nonHygienicAlphaLeft` establish that the
alpha-equivalence test succeeds and that the observations differ.

## Expected semantics

Any `Code.alphaEqv` result used to replace a selected `simpCase` branch must
imply semantic equivalence under the hypotheses of the pass theorem. Therefore
the theorem must either reject this input or carry the compiler's global
fresh-`FVarId` invariant.

## Actual behavior

`nonHygienicAlphaLeft.alphaEqv nonHygienicAlphaRight` is `true`, while executing
the bodies returns tagged natural values 6 and 5 respectively.

## Proof or differential evidence

The counterexample refutes an unconditional proof of `AlphaEqvSoundAt`. Lean's
pure LCNF checker rejects repeated free-variable identifiers, but its impure
checker is currently a no-op. FIR's `WellFormedAt .impure` records only unique
top-level declaration names and therefore also admits the witness.

## Semantic impact

The compiler-generated `simpCase` path is not known to produce this malformed
input; its preceding phases are intended to preserve globally fresh local
identifiers. The impact is on FIR's theorem boundary: a whole-pass correctness
claim must make that inherited invariant explicit and prove it is preserved.

## Classification and triage

This is classified as `fir-semantics`, not as a confirmed Lean compiler bug.
The minimized input violates Lean's intended LCNF binder discipline, but FIR's
current phase invariant does not express that discipline.

## Workaround

Keep `AlphaEqvSoundAt` as an explicit hypothesis until the impure checked-program
invariant includes global binder freshness and the alpha-equivalence proof uses
it.

## Upstream tracking

none

## Resolution and regression

unresolved
