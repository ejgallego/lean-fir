---
id: FIR-BUG-impure-elimDeadVars-nullary-fap-effects
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: elimDeadVars-0
discovered-by: proof
first-seen: 2026-07-22
reproduction: Fir/LeanIR/Passes/ElimDeadExamples.lean#deadNullaryFapBeforeProgram
regression: Fir/LeanIR/Passes/ElimDeadExamples.lean#deadNullaryFapStaticPremisesButNotCorrect
---

# Summary

FIR's current impure well-formedness and external-call semantics permit an
observable zero-argument full application that Lean 4.32's `elimDeadVars`
classifies as a removable constant when its result is unused.

## Minimal reproduction

Declare a nullary external `deadNullaryExternal`, call it with
`.fap `deadNullaryExternal #[]` in an unused let binding, and then return an
unrelated erased value.  The external implementation increments the world and
produces one trace event.  Both the source and transformed programs satisfy
the repository's current `WellFormedAt .impure` predicate.

## Exact commands

From the proof worktree using the pinned toolchain:

```sh
sed -n '45,90p' \
  /home/egallego/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Compiler/LCNF/ElimDead.lean
lake build Fir.LeanIR.Passes.ElimDeadExamples
make bug-cards
```

The upstream source says zero-argument full applications are constants and
returns `args.isEmpty` from `LetValue.safeToElim`.  The Lean regression checks
the transparent shadow against the actual pinned pass and evaluates both
programs with the same external implementation.

## Expected semantics

Under FIR's current impure semantics, a correctness theorem quantified over
arbitrary `ExternalSpec` or implemented `ExternalImpl` must preserve the
external request, world update, and trace event, even when the returned value
is dead.

## Actual behavior

Lean 4.32 removes the unused nullary `.fap`.  The source run performs one
external event and advances the world; the transformed run performs no event
and leaves the world unchanged.  Their returned values agree, but neither raw
observation equality nor `ObservationRel` can relate the world/trace fields.

## Proof or differential evidence

The actual-pass fixture `deadNullaryFapBefore` transforms to
`deadNullaryFapAfter`.  `deadNullaryFapObservableMismatch` checks that both
runs return erased while the source has world `1` and trace length `1` and the
target has world `0` and an empty trace.

`deadNullaryFapStaticPremisesButNotCorrect` strengthens this to a kernel
theorem: the source satisfies the full `ProgramElimDeadWellFormed` premise,
the transparent whole-program pass run succeeds with the actual pinned
target, and `LoweringCorrect` is false for the counted external specification.
The proof admits the concrete source run into the relational small-step
semantics and characterizes every target evaluation before refuting
`ObservationRel` from the worlds `1 ≠ 0`.

Consequently, neither `WellFormedAt .impure` nor the complete static
`ProgramElimDeadWellFormed` package can discharge the `.fap #[]` case of a
generalized deleted-let stuttering theorem.

`NullarySafeShadowCodeRun` now records the conservative compiler policy
separately from runtime/ownership admissibility.  Its soundness theorem
reconstructs the transparent `shadowCode?` result.  The positive neutral
fixture constructs `neutralCompilerAdmissibleRun`, while
`deadNullaryFapNotCompilerAdmissible` proves that this counterexample cannot
inhabit the stricter compiler-facing package.

## Semantic impact

Whole-pass correctness for `elimDeadVars` is unprovable against FIR's current
semantic contract using only the current phase well-formedness premise.  The
same boundary affects any pass that treats nullary cached declarations as pure
constants while FIR permits their external implementation to mutate the world
or emit trace events.

## Classification and triage

This is provisionally `fir-semantics`.  Lean's comment documents the intended
compiler invariant that zero-argument full applications are constants, while
FIR deliberately models arbitrary external effects and its phase invariant
does not record the corresponding purity/admissibility condition.  Triage
must decide whether to strengthen impure program/external well-formedness,
weaken which external behavior counts as observable for constant declarations,
or classify effectful nullary externals as outside the compiler contract.

## Workaround

Keep `.fap #[]` out of the local one-step deleted-let theorem.  Compiler
clients may use `ElimDeadCompilerAdmissibleRun`, whose exact policy graph
forbids precisely a deleted nullary `.fap` while retaining the independent
runtime/ownership certificate. Any later nullary-call rule must consume an
explicit semantic stuttering certificate until a shared compiler invariant is
defined and landed through the integration owner.

## Upstream tracking

none

## Resolution and regression

Unresolved.  Preserve the actual-pass fixture, executable mismatch, and
kernel-level negative theorem. Replace the explicit semantic-admissibility
premise only after a shared contract rules out or accounts for effectful
nullary constants.
