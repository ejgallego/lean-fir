# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 4d4e5b4c on main
functional-head: cbe31a53 (complete recursive structured simulation for direct values, pure external results, and generated named calls)
contract-base: 4d4e5b4c; proof-only extension over the accepted W6.7e recursive named-call simulation and existing concrete external-runtime contracts
clean-at-update: true
slice: The hereditary structured theorem now handles every admitted pure Nat, Int, and scalar external result at arbitrary finite nesting with generated named calls. Compiler/adapter inversion derives compiled arguments plus one resolver-proved imported declaration call and destination write. The target path is reified from the runtime WP; the source path is the exact three-step external protocol. The evolved entry-relative cache/resource witness, ABI refinement, and outer source/target frames are retained. The current no-case fragment records its empty join environment explicitly. No target path, execution certificate, or resolver package is supplied by the caller.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam save (pass, version 45, source hash eaac3110f293de68); lake env lean FirTalos/ConcreteStructuredSimulation.lean (pass); lake build FirTalos.ConcreteStructuredSimulation (pass, 3110 jobs); git diff --check (pass); make check (pass, 642 unique covered cases and 1844/1844 comparisons); make talos-setup (pass, Talos a01d01c); make talos-check (pass, 3133 jobs)
bug-cards: none
blockers: none
handoff: ready for integration; base 4d4e5b4c, functional head cbe31a53, clean worktree at status update
next: Connect the two lazy-cache paths to exact structured prefixes and extend the same hereditary theorem through cache hit and miss while preserving the explicit join/frame boundary.
```
