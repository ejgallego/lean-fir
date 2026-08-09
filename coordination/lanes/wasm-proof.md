# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 5307f77d on main
functional-head: bca03085
contract-base: 5307f77d on main; ownership-threaded matcher/projection and the existing concrete closure application contracts
clean-at-update: true
slice: Derive the ownership-aware saturated closure-call runtime law from the finite hereditary source derivation, exact compiler candidate identity, post-consumption matcher refinement, program-indexed closure ABI alignment, and generated-declaration induction; assemble the complete fixed-capture plus ordinary-argument callee row from compiler output; eliminate the historical selected.nextStore = initial shortcut and all per-call selected-body/argument-assembly target certificates
files: Fir/Wasm/Lower.lean; integration/talos/FirTalos/ConcreteReuseCapacityCallCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Introduces proof-only ClosureAllocationsAbiAligned, ConcreteReuseCapacityCacheAbiFrame, SaturatedClosureCandidateResolver, and DirectHereditaryGeneratedDeclarationAbiInduction boundaries; no shared semantic runtime, symbolic Wasm ABI, resident-helper signature, or concrete layout changed
checks: PASS Lean Beam update/sync/save for FirTalos.ConcreteReuseCapacityCacheCorrectness and prior focused checkpoints; PASS lake build Fir.Wasm.Lower; PASS lake build FirTalos.ConcreteReuseCapacityCallCorrectness; PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness (3103 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch is four functional commits ahead of main and clean at this mailbox update
next: prove DirectHereditaryGeneratedDeclarationAbiInduction from ABI-preserving generated operation laws, then discharge SaturatedClosureCandidateResolver from the executable adapter/resolver rather than retaining it as an external premise
```
