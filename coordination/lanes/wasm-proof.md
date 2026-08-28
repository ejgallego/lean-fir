# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 330e6366327748cbf889e5e764da8a7edd84df91
functional-head: 73379f74eb27e845cfd9b28cf3d7fa01d592caaf
contract-base: 330e6366327748cbf889e5e764da8a7edd84df91
clean-at-update: true
slice: Established the constructor-schema/active-witness agreement boundary. ConstructorSchema retains final-LCNF layout and object-slot ABIs by semantic location; WitnessAgrees relates every retained entry to the descriptor in exactly the active refinement witness. Proved empty, monotone-extension, fresh-binding, and in-place-rebinding transports, then derived active descriptor-slot alignment from source FieldKindAt plus witness agreement. The former universal-witness admission remains in production until the next threading slice.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: none; proof-side ghost provenance and relational agreement only
checks: Lean Beam update/sync/save FirTalos/ConcreteRuntime.lean, FirTalos/ConcreteStructuredValidation.lean, and downstream FirTalos/ConcreteResumableWasm.lean (green); direct batch elaboration of both edited modules (green); forced 3128-job module cone (green); git diff --check (green); make check (green, 730 unique cases and 2172/2172 comparisons); make talos-setup (green); make talos-check (green, 3182 jobs, receipt e4c600a7196e8763e5a9790dc637b0012a8c2a58df6321731b2da94600a8a828)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission (confirmed; replacement proof boundary implemented, production admission not yet fixed)
blockers: none
handoff: Ready for integration from frozen wasm/talos-runtime at the containing clean status commit.
next: Thread ConstructorSchema and WitnessAgrees through the validated global relation, replace ObjectFieldFVarEffectSupported/ObjectFieldErasedEffectSupported's universal-witness premise with source FieldKindAt, and close both object-field dispatcher successors.
```
