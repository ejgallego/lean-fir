---
id: FIR-BUG-wasm-none-finite-trace-address-space-safety
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 8bcafc05cc6116beac056eaa192d60c89916acef
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-13
reproduction: integration/talos/FirTalos/ConcreteResumableWasm.lean
regression: integration/talos/FirTalos/ConcreteResumableWasm.lean
---

# Summary

The proposed compiler-wide finite-trace coverage law conflates compiler
admission with a wasm32 address-space safety property that does not follow
from lowering an unbounded-heap source program.

## Minimal reproduction

Take any related ordinary code state whose next successful source operation
allocates a positive number of bytes. `MemoryState.AddressSpaceBudget.weaken`
can re-index the same otherwise unchanged concrete frame at zero remaining
bytes, but current-step coverage then requires the positive allocation cost
to be at most zero.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteResumableWasm
```

Inspect `ConcreteStructuredCompilerCurrentStepAdmission.code`,
`ConcreteStructuredCurrentStepAddressSpaceSafety.code`, and
`MemoryState.AddressSpaceBudget.weaken` in
`Fir/Wasm/Concrete/AllocationCorrectness.lean`.

## Expected semantics

Compiler admission should prove that a successful supported source step has a
matching generated operation and an exact allocation cost. A separate theorem
boundary should either require enough finite address space for the selected
prefix, model a matching source OOM, or use an unbounded target memory model.

## Actual behavior

The old coverage structure quantified over every `remainingBytes` index
admitted by the concrete frame and concluded both current-node admission and
`requiredBytes ≤ remainingBytes`. The roadmap described this entire law as a
compiler theorem, although the inequality is a dynamic resource property.

## Proof or differential evidence

`AddressSpaceBudget.weaken` derives a zero-byte budget from every valid larger
budget. The positive costs of allocating constructor, closure, boxed scalar,
string, natural, or integer operations cannot satisfy the resulting coverage
inequality. More generally, a fixed wasm32 heap cannot match every finite
prefix of an indefinitely allocating source execution.

## Semantic impact

An unconditional `ConcreteFiniteTraceCorrect` theorem for all supported source
programs is too strong for the current source/target memory models. Leaving
the condition hidden inside a purported compiler-coverage theorem would make
the main proof obligation uninhabited rather than establish compilation
correctness.

## Classification and triage

This is a proof-contract and semantic-model boundary, not an operation-lowering
bug. The next theorem surface should separate compiler-derived admission from
finite-memory safety and state clearly which one is assumed or modeled.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Fixed in `ConcreteResumableWasm`. Compiler admission now returns only the
source/compiler judgment and its exact allocation cost. The independent
`ConcreteStructuredCurrentStepAddressSpaceSafety` law is solely responsible
for proving that cost fits the retained wasm32 budget. Their compatibility
package is a pair, and the preferred export-facing theorem exposes both
hypotheses separately. The remaining choice between a resource-safe execution
invariant and an explicitly budgeted finite prefix is roadmap work, not a
hidden compiler obligation.
