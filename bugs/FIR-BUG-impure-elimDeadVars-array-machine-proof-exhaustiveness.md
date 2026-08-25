---
id: FIR-BUG-impure-elimDeadVars-array-machine-proof-exhaustiveness
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: b3c0e83a0dfa5a0401829ce1b251282d47fbec03
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-08-25
reproduction: Fir/LeanIR/Passes/ElimDeadMachineRel.lean
regression: none
---

# Summary

Fresh elaboration of the impure `elimDeadVars` machine proof fails because
thirteen `HeapObject` case analyses were not extended for the Array runtime
object introduced on the accepted main branch.

## Minimal reproduction

On main `b3c0e83a`, refresh or forcibly rebuild
`Fir/LeanIR/Passes/ElimDeadMachineRel.lean`. The first failure is the
non-closure branch of `takeClosureApplication_expectedClosure`; twelve later
failures occur in constructor/box shape recovery, allocation-frontier
preservation, closure consumption, reset, and reuse lemmas.

## Exact commands

From the FIR root, with `TMPDIR` set to a worktree-local `.deps` directory and
the FIR Lake artifact-cache variables exported as required by `AGENTS.md`:

```text
lean-beam refresh Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean
lean-beam save Fir/LeanIR/Passes/ElimDeadRuntimeRel.lean
lean-beam refresh Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lake build +Fir.LeanIR.Passes.ElimDeadMachineRel
```

Beam reports thirteen errors of the form `Alternative array has not been
provided`; the forced Lake build exits with code 1 on the same locations.

## Expected semantics

Adding `.array elements` to `HeapObject` and `HeapObjectRel` should preserve
the complete ElimDead machine proof. Arrays contribute their elements to
owned-value/frontier reasoning, while constructor-only, boxed-only, and
closure-only runtime operations reject an Array through their existing error
paths.

## Actual behavior

Commit `9d34cf82` extends `ElimDeadRuntimeRel` with Array relation and ownership
cases, but does not adapt the dependent exhaustive matches in
`ElimDeadMachineRel`. A stale compiled machine-proof artifact can therefore
make aggregate checks appear green until the module is refreshed or forcibly
rebuilt.

## Proof or differential evidence

Lean Beam reports 13 errors and 141 warnings, with the errors at source lines
3681, 8851, 8937, 9394, 9898, 10459, 10925, 11025, 11139, 11214, 11278,
11322, and 11375. `lake build +Fir.LeanIR.Passes.ElimDeadMachineRel`
independently reproduces the same 13 errors.

## Semantic impact

No executable or differential mismatch is currently known. However, the
compiler-facing non-lockstep and `LoweringCorrect` cone cannot be freshly
elaborated on current main, so the LCNF pass-correctness lane is not green and
must not publish a new proof handoff until the Array cases are repaired and
the examples importer is forcibly rebuilt.

## Classification and triage

This is currently classified as a FIR semantic-proof adaptation omission,
not an upstream compiler discrepancy. The expected repair is local and
structural, but the ownership-bearing Array branches must use the accepted
`HeapObject.ownedValues` semantics rather than treating Arrays as root-free.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved. The permanent regression should force direct elaboration of
`Fir.LeanIR.Passes.ElimDeadMachineRel` after runtime object variants change,
then rebuild `Fir.LeanIR.Passes.ElimDeadExamples` as its dependency cone.
