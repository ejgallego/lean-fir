# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 2844bc39 on main
functional-head: d8d5e607
contract-base: 2844bc39 on main; recursive whole-export correctness and generic object-family ABI are linked/accepted
clean-at-update: true
slice: Determine whether the root and generated closure-resolver metadata premises of the public theorem are constructively derivable from compilation, and package or remove them where possible without introducing behavioral certificates
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: Refactors only the unstable proof-side function boundary so the same structural induction starts at a supported export and recurses through compiler-generated rows; the public theorem consumes finite source evaluation plus executable root/module resolver metadata and no target execution or behavior certificate; changes no shared source semantics, symbolic Wasm ABI, resident-helper signature, concrete layout, executable artifact, or W7 contract
checks: pending for this active slice; preceding landed checkpoint passed Lean Beam, focused 3104-job build, git diff --check, make check with 1844/1844 equal comparisons, and all 3125 Talos jobs
bug-cards: none
blockers: none
handoff: none; recursive whole-export correctness is linked/accepted on main at 2844bc39
next: inspect the executable resolver definitions and prove a pipeline-derived packaging theorem if the current metadata equations are definitionally recoverable
```
