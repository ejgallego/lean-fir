# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: d8244e79 on main
functional-head: 9feaaa00
contract-base: d8244e79 on main; derived closure-ABI induction and production saturated-closure runtime law are linked/accepted
clean-at-update: true
slice: Extend the finite hereditary source-evaluation family with saturated closure calls and compose the derived production runtime law into an export-level partial-correctness theorem
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCallCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: Strengthens proof-side external, transport, and declaration-result packages with ClosureAllocationsPersistent; adds DirectHereditaryGeneratedDeclarationAbiInduction.ofInduction and a production saturated-closure runtime theorem derived solely from lowering, adaptation, ordinary generated-declaration induction, and executable resolver metadata; no shared source semantics, symbolic Wasm ABI, resident-helper signature, or concrete layout changed
checks: PASS Lean Beam update/sync/save checkpoints for every edited Lean module; PASS lake build FirTalos.ConcreteCompilerCorrectnessContract FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3105 jobs); after rebase onto 8ec10ffe: PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup at a01d01c; PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: the derived closure-ABI slice is linked/accepted on main at d8244e79; this lane is building the next export-level theorem from that clean base
next: add the source-recursive saturated-closure constructor, prove its erasure/source-result law, and extend the generated-declaration induction case
```
