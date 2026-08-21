---
id: FIR-BUG-impure-none-opaque-hygiene
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: proof
first-seen: 2026-07-17
reproduction: Fir/LeanIR/Hygiene.lean#codeScoped
regression: Fir/LeanIR/HygieneExamples.lean
---

# Summary

FIR defines its impure hygiene and binder traversals as opaque `partial def`s,
so a kernel proof cannot derive declaration-body scope and freshness facts from
`Program.ImpureHygienic`.

## Minimal reproduction

Assume that a return instruction is accepted by the hygiene checker:

```lean
h : ImpureHygiene.codeScoped scope (.return x) = true
```

The expected one-constructor proof is:

```lean
simpa [ImpureHygiene.codeScoped] using h
```

Lean leaves `codeScoped scope (.return x)` opaque, so it cannot derive
`scope.vars.contains x = true`. The same issue affects the mutually recursive
scope traversal and the binder traversal used to prove global freshness.

## Exact commands

From a clean checkout using the pinned toolchain:

```sh
rg -n "partial def (codeScoped|altScoped|funDeclScoped|codeBinders|altBinders)" \
  Fir/LeanIR/Hygiene.lean
lake build Fir.LeanIR.Passes.AlphaEqvCode
```

A Lean probe containing the minimal example above fails because simplification
does not unfold `ImpureHygiene.codeScoped`.

## Expected semantics

`Program.ImpureHygienic` should be usable as the public phase boundary for
proofs. Downstream proofs should be able to invert each accepted code
constructor, recover lexical scope, and use global binder uniqueness to prove
freshness of parameters, lets, and joins.

## Actual behavior

The executable checker computes successfully, but its recursive constants are
opaque to the kernel and expose no public equation theorems. Even the terminal
return case cannot be inverted.

## Proof or differential evidence

`coreStep_machine_related` now proves named and closure invocation conditional
on `ProgramBodiesRelated`. Discharging that ordinary premise from
`Program.ImpureHygienic` stops at the first attempted reduction of
`codeScoped`; no semantic constructor case is reached.

## Semantic impact

This does not show that the hygiene checker accepts an invalid program. It
prevents FIR from connecting the checked impure phase to declaration-entry
simulation, so whole-program correctness must retain an explicit proof-facing
body premise.

## Classification and triage

This is classified as `fir-semantics` because the opaque definitions live in
FIR rather than upstream Lean. The executable algorithms are structurally
recursive and should be replaceable with total transparent definitions or
accompanied by safe equation theorems.

## Workaround

`ProgramBodiesRelated` records exactly the missing proof-facing consequence:
every reachable internal declaration is reflexively related beneath its
parameters. Call simulation accepts that proposition explicitly without adding
a trusted axiom.

## Upstream tracking

none

## Resolution and regression

Fixed by replacing the opaque mutually recursive scope and binder traversals
with total transparent code/alternative-list traversals. Their public
`codeScoped`, `altScoped`, `funDeclScoped`, `codeBinders`, and `altBinders`
surfaces retain the executable behavior while exposing kernel equations.
`declHygienic_binderNamesUnique` proves declaration-wide pairwise binder-name
freshness from the executable checker; `HygieneExamples.twoBinderNamesDistinct`
is the kernel-facing regression. Pass-specific proof-certificate cleanup and
deriving `ProgramBodiesRelated` are follow-ups, not prerequisites for using
the repaired shared interface.
