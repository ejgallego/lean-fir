# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d78d128ce33e510e0164dd7f4296236a19c24c02, authoritative heap-only USize convergence base from W7-W6-20260826-028
functional-head: 0360367a3142bd707ae2100b337967971fada15a
contract-base: d78d128ce33e510e0164dd7f4296236a19c24c02
clean-at-update: true
slice: Aligns the W6 concrete scalar boundary with the converged heap-only USize source, LCNF, and resident-helper contract. BoxedScalarKind now admits tagged representation only for UInt8, UInt16, and UInt32; UInt64 and USize always allocate. allocateBoxedUSize_residentContract exposes one payload-parametric proof of the exact resident boundary: a related owned boxed object at the allocation frontier, 40 allocation bytes, scalar marker 5, payload width 8, zero reserved lanes, reference count 1, and non-persistent ownership. boxUSize_liveHeapRel carries every payload through the semantic heap-box refinement, while the tagged-read theorem excludes USize. Executable examples cover payload 42 and UInt64.max and reject a physical tagged word. The earlier validated-case, join-entry, and exact join-unwind proof stack remains cumulative after the clean rebase.
files: Fir/Wasm/Concrete/Runtime.lean; Fir/Wasm/Concrete/BoxingCorrectness.lean; Fir/Wasm/Concrete/Examples.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; coordination/lanes/wasm-proof.md
contracts: The W6 concrete boxing policy now records USize as heap-only, matching the source semantics, LCNF adaptation, and resident helper already present at the convergence base. No source semantics, LCNF lowering, W7 implementation or artifact, helper signature, semantic ABI, concrete object layout, allocator, marker, ownership rule, symbolic Wasm surface, or compiler behavior changed in this slice. The new resident and live-heap theorems are additive proof interfaces over that aligned policy.
checks: Lean Beam update/sync/save passed with zero diagnostics for Runtime.lean, BoxingCorrectness.lean, and Examples.lean. lake build Fir.Wasm.Concrete.BoxingCorrectness Fir.Wasm.Concrete.Examples passed all 27 jobs. The forced W6 downstream cone lake -d integration/talos build FirTalos.ConcreteResidentScalarBox passed all 3,125 jobs, including FirTalos.ConcreteResidentUSize. git diff --check passed. make check passed with 721/721 source cases, 9/9 direct-machine cases, 730 unique cases, 2,172/2,172 comparisons equal, zero findings, 210 active bug cards, and 31 mailbox tests. make talos-setup completed at Talos 0e05edbc. make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-impure-case-table-selector-determinism (existing; names the missing final-LCNF normalization phase bridge); FIR-BUG-wasm-none-return-admission-refinement-direction (existing; semantic transport and state-local return-safety boundaries solved; the global source-typing invariant/module dispatcher remains)
blockers: none
handoff: GREEN LIGHT. Consume the exact clean integration checkpoint published by the completion event in authoritative mailbox thread W7-W6-20260826-028 rather than following a moving branch. It is based directly on d78d128c, has functional head 0360367a, retains the rebased join/jump checkpoint, and passes every required gate.
next: Wait for fir/wasm-gen integration review and landing of this heap-only USize convergence handoff. Do not begin another dispatcher successor before that integration response.
```
