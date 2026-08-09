# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: de1c7ca7 on main
functional-head: d8d5e607
contract-base: de1c7ca7 on main; recursive generated closure induction and generic object-family ABI are linked/accepted
clean-at-update: true
slice: Generalize the structural production proof from generated internal rows to an explicit per-function operation/resolver interface, instantiate that interface at the exported root and every actual generated recursive row, and prove public whole-export correctness for arbitrary finite nesting of named and exactly saturated closure calls
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Refactors only the unstable proof-side function boundary so the same structural induction starts at a supported export and recurses through compiler-generated rows; the public theorem consumes finite source evaluation plus executable root/module resolver metadata and no target execution or behavior certificate; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, executable artifact, or W7 contract
checks: PASS Lean Beam sync/save (0 errors, 17 warnings, source b89a0927c9ab643f); PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteReuseCapacitySupportedExportCorrectness (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases, 1844/1844 comparisons equal, zero findings); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for the integration owner to land functional commit d8d5e607 followed by this containing mailbox commit from wasm/talos-runtime
next: simplify the public theorem's compiler-derived resolver premises where executable generation can package them automatically, then state the trace/coinductive extension separately from this finite partial-correctness theorem
```
