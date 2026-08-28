# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 87c0299d2bfeaae6a1ad32ee87bfa00dd31fe090
functional-head: 341888236ec021fe4565da9d1b11e800b6612ab0
contract-base: 87c0299d2bfeaae6a1ad32ee87bfa00dd31fe090
clean-at-update: true
slice: Added ConcreteStructuredValidatedCodeGlobalOutcomeAt, a witness-indexed companion covering all seven validated global constructors; existential schema agreement; erasure to the established relation; generic same-witness construction; and schema-global FVar/erased field successors.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side global relation companion only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and the established validated/finite-trace relations unchanged
checks: git diff --check PASS; Lean Beam sync/save ConcreteStructuredValidation and downstream ConcreteResumableWasm PASS; direct lake env lean on both modules PASS; lake build FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm PASS (3128 jobs); make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt 2cf08b48832249fa5c8e246182ecd1d0f71a875f299bdc821aca904b525ebdf2)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Land functional commit 341888236ec021fe4565da9d1b11e800b6612ab0 and this clean status commit. The schema-global relation is established and covers field mutation; full one-step closure is not yet claimed.
next: Lift direct/saturated/lazy/external/bind/return witness-unchanged transitions to the indexed relation, then handle witness extension and constructor bind/rebind for allocation/reuse.
```
