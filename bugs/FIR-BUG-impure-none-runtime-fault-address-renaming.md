---
id: FIR-BUG-impure-none-runtime-fault-address-renaming
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: proof
first-seen: 2026-07-22
reproduction: Fir/LeanIR/PassCorrectness.lean
regression: none
---

# Summary

The reachable observation relation requires exact equality of runtime faults,
but `RuntimeFault.deadObject` contains a concrete semantic heap location.
Executions related by a non-identity `AddressRenaming` can therefore report
different fault payloads for the same mapped dead object.

## Minimal reproduction

Relate source location `0` to target location `1`, and put corresponding dead
heap cells at those locations.  Invoke either location as a closure, or apply
another operation whose failed live-cell read reports `deadObject`.

The source observation contains `.fault (.deadObject 0)`, while the target
observation contains `.fault (.deadObject 1)`.  The locations are correctly
related by the address renaming, but `OutcomeRel` reduces the obligation to
`RuntimeFault.deadObject 0 = RuntimeFault.deadObject 1`.

## Exact commands

Inspect the address-bearing fault and exact fault relation with:

```text
rg -n "deadObject|def OutcomeRel" Fir/LeanIR
lean-beam update Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadMachineRel.lean
```

Then attempt the dead-reference branch of reachable `.invokeValue` simulation
with `rho.forward 0 = some 1`.

## Expected semantics

Fault observations that expose semantic heap locations should be related by
the active `AddressRenaming`, just as returned heap references are.  Faults
without address payloads should retain exact equality.

## Actual behavior

`OutcomeRel` in `Fir/LeanIR/PassCorrectness.lean` defines every fault pair by
plain equality.  It cannot relate address-bearing faults at mapped locations.

## Proof or differential evidence

`ShadowRuntimeRel` proves that reachable source location `0` maps to reachable
target location `1` and that the corresponding cells have equal liveness.
`getLiveCell` therefore returns `deadObject 0` and `deadObject 1` respectively.
The final `ShadowRuntimeRel.observationRel` call fails solely because
`OutcomeRel` demands equality of these two payloads.

## Semantic impact

Whole-program reachable correctness for allocation-deleting passes is false
under the current observation relation whenever an execution can observably
fault on a mapped heap reference after source and target locations diverge.
This affects `elimDeadVars` and any other pass justified by address renaming.

## Classification and triage

This is a shared FIR semantic-contract gap.  Replace exact fault equality with
a `RuntimeFaultRel rho` that maps every address-bearing payload through `rho`
and keeps address-free faults exact.  Audit all `RuntimeFault` constructors so
the relation does not accidentally weaken non-address diagnostics.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
