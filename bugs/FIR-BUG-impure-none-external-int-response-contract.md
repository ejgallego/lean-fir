---
id: FIR-BUG-impure-none-external-int-response-contract
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.34.1
lean-revision: 5045d0056413266e57c625dcd7c365b10e377c52
phase: impure
pass: none
discovered-by: invariant-check
first-seen: 2026-09-29
reproduction: Fir/Validation/LCNF.lean
regression: none
---

# Summary

At FIR `471d0fc9f`, the executable validation external dispatcher returns small
Int results as tagged values. The current W6 `PureIntegerExternalSupported`
constructor requires an exact `semanticIntegerExternalResponse`, which always
allocates and returns a heap integer. This is a contract-coverage discrepancy;
the existing conditional compiler theorem does not claim this premise holds
for every external implementation.

## Minimal reproduction

Use Lean Beam in the saved `Fir/Validation/LCNF.lean` module, immediately before
`end Fir.Validation.Lcnf`. This successful speculative probe uses the real
private dispatcher (not a copied implementation):

```lean
example (before : Fir.LeanIR.Impure.RuntimeState)
    (types : Array Lean.Expr) (resultType : Lean.Expr) :
    validationExternals.call { name := ``Int.ofNat, paramTypes := types, resultType, args := #[.object (.tagged 0)] } before =
      .ok { value := .object (.tagged 0), heap := before.heap, nextLocation := before.nextLocation, world := before.world } := by
  rfl
```

In `blueprint/FirBlueprint/Targets/Admission.lean`, after the existing namespace
opens and before `externalSpec`, Beam also checks:

```lean
example (before : RuntimeState) (value : Int) (payload : UInt64) :
    (semanticIntegerExternalResponse before value).value ≠ .object (.tagged payload) := by
  intro same
  cases same
```

## Exact commands

From the Blueprint directory, with the FIR cache and worktree-local TMPDIR
environment configured, keep `lean-beam serve` running. At the reviewed source:

```sh
lean-beam update ../Fir/Validation/LCNF.lean
lean-beam run-at ../Fir/Validation/LCNF.lean 1 4216 0 --stdin
lean-beam update FirBlueprint/Targets/Admission.lean
lean-beam run-at FirBlueprint/Targets/Admission.lean 1 14 0 --stdin
```

Supply the respective example above on stdin, ending it with EOF. Both updates
returned version 1 in the fresh session; use the returned version if different.
Coordinates are zero-based and refer to `471d0fc9f`.

## Proof or differential evidence

Both probes return `success: true` without diagnostics on Lean 4.34.1. Request
metadata is arbitrary in the first equation, so the discrepancy is not limited
to a dummy empty type row. The two response values have different constructors.

## Expected semantics

A contract claimed to cover the validation interpreter must admit its actual
successful responses.

## Actual behavior

Its small Int handlers use `encodeIntValue`, preserving
heap and cursor when a signed 32-bit immediate is available. W6 requires a heap
response and charges `integerAllocationBytes`, including for zero.

## Semantic impact

Matching mathematical integer values or the `.tobject` ABI does not establish
equality of responses, heaps, allocation costs or observations.

## Classification and triage

Confirmed discrepancy between the source validation and proof-admission
contracts, not a counterexample to the existing conditional compiler theorem.

## Resolution and regression

Review a representation-aware response/refinement and cost model with W6 and
root. An explicit, proved normalization bridge is another possible design.
Do not declare the current validation implementation satisfies the heap-only
contract, silently change its semantics, or rule out tagged responses in the
Blueprint's primitive specification to make admission vacuous.

No fix or committed production regression yet; both Lean probes above passed.

## Workaround

None. No production semantic change is made. The Blueprint keeps its
specification hole and exposes external realization and admission as separate
open obligations. Full contract design is in the
[external contracts and request domains chapter](../blueprint/FirBlueprint/Chapters/ExternalDomains.lean).

## Upstream tracking

FIR-local W6/root semantic review; no Lean or VBP upstream bug is claimed.
