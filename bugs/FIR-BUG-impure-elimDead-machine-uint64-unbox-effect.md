---
id: FIR-BUG-impure-elimDead-machine-uint64-unbox-effect
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-08-26
reproduction: Fir/LeanIR/Passes/ElimDeadMachineRel.lean
regression: Fir/LeanIR/Passes/ElimDeadMachineRel.lean
---

# Summary

Fresh elaboration of the impure `elimDeadVars` machine proof fails because
`HeapOwnershipBelowFrontier.unboxResult` still assumes that every successful
tagged scalar unbox is described directly by `scalarFromType`. The accepted
heap-only UInt64 contract first rejects tagged UInt64 values, so the proof must
exclude that impossible branch before reusing the immediate-scalar lemma.

## Minimal reproduction

On main `fc56e2ee`, refresh `Fir/LeanIR/Passes/ElimDeadMachineRel.lean`. Lean
reports a type mismatch in the tagged branch of
`HeapOwnershipBelowFrontier.unboxResult`: simplification of the successful
`unbox` effect retains the new `type == uint64` rejection guard, while the
proof expects an unguarded `scalarFromType type payload = .ok result` fact.

## Exact commands

From `.worktrees/proof-simpcase`, with the FIR Lake artifact-cache variables
exported as required by `AGENTS.md`:

```text
lean-beam update Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lake build +Fir.LeanIR.Passes.ElimDeadMachineRel
```

## Expected semantics

A successful tagged unbox implies that the requested type is not UInt64.
After proving that guard false, the existing `scalarFromType` result-shape
lemma establishes that the result has no heap location.

## Actual behavior

The machine proof drops the new UInt64 guard by simplification and attempts to
use the guarded effect as an unguarded `scalarFromType` equality. A stale Lake
artifact can leave the aggregate root gate green until this large proof module
is refreshed or forcibly rebuilt.

## Proof or differential evidence

Lean Beam reports one save-blocking error at the construction of `scalarRead`
inside `HeapOwnershipBelowFrontier.unboxResult`. The semantic and
`ElimDeadRuntimeRel` consumers are already repaired and executable native,
LCNF, V8, and resident-Wasm UInt64 regressions pass; this is a missed dependent
proof consumer rather than a new runtime mismatch.

## Semantic impact

No executable mismatch remains, but the full ElimDead machine-correctness cone
cannot be freshly elaborated against the accepted UInt64 representation. The
LCNF proof lane must not publish its next handoff until this consumer is fixed
and the forced importer cone passes.

## Classification and triage

This is a proof adaptation omission under the existing
`UINT64-BOXING-UPSTREAM-ALIGNMENT` contract. The repair must reject the tagged
UInt64 branch explicitly; it must not weaken heap-only UInt64 semantics or
reintroduce a tagged representation.

## Workaround

none. The proof now handles the guard explicitly.

## Upstream tracking

none

## Resolution and regression

`HeapOwnershipBelowFrontier.unboxResult` now splits on the UInt64 type guard
in the tagged-reference branch. The UInt64 arm contradicts successful unbox;
all other scalar kinds recover the existing `scalarFromType` equality and
reuse its immediate-result shape proof. Heap boxing and decoding semantics are
unchanged.

The same proof slice replaces the retained-prefix singleton adapter with
`TargetLiveHeapPrefixControlAt` and
`DeletedLedgerLiveHeapPrefixOperationAt`. These interfaces quantify over an
arbitrary target frontier and may select a different live binder and source
owner at every target location. The retained-prefix fixture is now only the
constant-binder/constant-owner instance and no longer carries duplicated
singleton-specific readiness theorems.

Lean Beam freshly elaborates and checkpoints both
`Fir.LeanIR.Passes.ElimDeadMachineRel` and
`Fir.LeanIR.Passes.ElimDeadExamples` with zero errors. The forced dependency
cone and full repository gate are recorded in the LCNF handoff.
