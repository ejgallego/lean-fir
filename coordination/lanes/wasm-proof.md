# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 77efa825 on main
functional-head: 4f42c84f (previous accepted structured direct-call entry slice; no transport functional commit yet)
contract-base: 77efa825; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, return, bind-frame, and generated direct-call entry slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Continue W6.7e by defining and proving the hereditary saved-caller invariant needed across generated callee execution. Transport the caller runtime/local/frame relation across permitted allocation, mutation, ownership, cache, and external effects, then use a related callee yield to establish the accepted ConcreteStructuredBindFrameFocus for return unwinding. Keep the relation compiler-derived and certificate-free.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Inventory the existing reuse/capacity/cache hereditary-frame theorems and identify the minimal transported caller relation that composes with ConcreteStructuredDirectCallEntryFocus and ConcreteStructuredBindFrameFocus.
```
