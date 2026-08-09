# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: db1295ab on main
functional-head: feea71dc
contract-base: db1295ab on main; recursive production source evaluation, exact generated-row target boundary, and generic object-family ABI are linked/accepted
clean-at-update: true
slice: Prove the generated-row target theorem by structural induction over every finite ReuseCapacityProductionHereditaryCodeEvaluates derivation, including recursively nested named calls and saturated closure calls; exact and arbitrary-slack executions share the same recursive proof, and closure resolution uses only executable generated-candidate metadata
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Corrects the unstable proof target so the concrete reuse-capacity/cache ABI is required at recursive declaration entry, where saturated capture projection consumes it, and proves preservation at exit; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, executable artifact, or W7 contract
checks: PASS Lean Beam sync/save (0 errors, 16 warnings); PASS post-rebase lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3104 jobs); PASS git diff --check; PASS post-rebase make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-setup (Talos a01d01c); PASS post-rebase make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for the integration owner to land functional commit feea71dc followed by this containing mailbox commit from wasm/talos-runtime
next: preserve recursive direct/closure call payloads in the root-export adapter and expose the public recursive whole-export correctness theorem
```
