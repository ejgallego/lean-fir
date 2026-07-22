---
id: FIR-BUG-impure-none-external-spec-address-parametricity
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: proof
first-seen: 2026-07-22
reproduction: Fir/LeanIR/Runtime.lean
regression: none
---

# Summary

The impure `ExternalSpec` contract may distinguish concrete heap addresses,
so a reachable-heap pass simulation cannot transport external steps across an
address renaming without an additional parametricity law.

## Minimal reproduction

Relate a source heap reference at location `0` to a target heap reference at
location `1`.  Let both machines invoke the same external declaration with
those related references as their sole arguments.  Define `ExternalSpec` to
accept only requests whose argument is exactly `.object (.heap 0)`, or to
return observably different worlds for locations `0` and `1`.

The source has an external semantic step, while the target either has no
matching response or resumes with an unrelated observation.

## Exact commands

Inspect the unrestricted contract and the simulation obligation with:

```text
rg -n "abbrev ExternalSpec|inductive Step" Fir/LeanIR
lean-beam update Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadMachineRel.lean
```

Attempt the external-declaration branch of a `ReachableMachineRelated` named
call using only `externals request source.runtime response`.  The target
obligation has a different request/runtime pair and does not follow.

## Expected semantics

Foreign-call behavior used by address-renaming compiler proofs should be
equivariant: related requests and runtimes should admit related responses,
with world and observable trace behavior preserved.

## Actual behavior

`ExternalSpec` is only
`ExternalRequest → RuntimeState → ExternalResponse → Prop`.  It has no law
connecting calls made from related runtimes or requests whose heap references
are mapped by an `AddressRenaming`.

## Proof or differential evidence

The reachable `elimDeadVars` relation can shift target allocation locations
after deleting source-only garbage.  Internal declaration entry can use
`ValueRel`, but the `Step.external` constructor supplies only the source-side
`ExternalSpec` fact.  There is no proposition from which to construct the
target-side fact required by `NonLockstep.Reaches`.

## Semantic impact

For arbitrary `ExternalSpec`, reachable-observation forward correctness of
allocation-deleting passes is false for programs that pass heap references to
external declarations.  This affects the intended whole-program theorem, not
only its proof convenience.

## Classification and triage

This is a shared FIR semantics contract gap.  Introduce a proof-visible
renaming-parametric external specification law, or restrict the correctness
theorem to an admissible external interface that cannot inspect semantic heap
locations.  The law must relate requests, pre-call runtimes, responses, and
the post-response address renaming; merely assuming deterministic calls is
insufficient.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
