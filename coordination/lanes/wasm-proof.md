# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 18af585a on main
functional-head: 7943fdfa
contract-base: 18af585a on main; existing concrete heap refinement, runtime-step transport, cache-frame, and closure ABI-alignment contracts
clean-at-update: true
slice: Establish closure-allocation persistence for every currently proved non-closure concrete runtime transition; thread it through constructor allocation/reuse, scalar boxing, promoted tags, compiler runtime transports, and cache/call frames; derive transport of program-indexed closure ABI alignment without a fresh post-step premise
files: Fir/Wasm/Concrete/Refinement.lean; Fir/Wasm/Concrete/PromotedTagCorrectness.lean; Fir/Wasm/Concrete/ConstructorHeapCorrectness.lean; integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteRuntimeExamples.lean; this mailbox
contracts: Adds proof-only ClosureAllocationsPersistent and a corresponding RuntimeStepTransports field; ordinary runtime operations cannot invent closure descriptors, while actual closure allocation remains governed by the compiler-derived ABI compatibility law; no shared semantic runtime, symbolic Wasm ABI, resident-helper signature, or concrete layout changed
checks: PASS Lean Beam update/sync/save checkpoints for all changed proof modules and FirTalos.ConcreteRuntimeExamples; PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness (3103 jobs); PASS forced lake build FirTalos.ConcreteRuntimeExamples (3098 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup at a01d01c; PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration as the transport foundation for deriving DirectHereditaryGeneratedDeclarationAbiInduction from compiler operation laws
next: strengthen concrete external-operation correctness with the same persistence fact, then lift direct/effect/external generated laws to the closure-ABI frame and derive the global ABI induction
```
