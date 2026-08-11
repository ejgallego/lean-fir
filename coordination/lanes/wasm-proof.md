# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: dfc5e54a on main
functional-head: 844fe9b1 (recursive structured simulation now includes singleton object-constructor dispatch)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: The first generated production dispatcher is complete. The source-only recursive admission includes a singleton object-constructor case; source/compiler facts identify the selected arm and exact generated local-read/getTag/tag-comparison/conditional shape. The target takes an exact five-step prefix into the selected compiled branch under a saved label, recursion proves that branch, and one returnLabel step restores the enclosing frames. The proof retains exact source/target counts and the complete entry-relative cache/resource invariant without accepting a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 91 hash 6b23bb640c5be1a0 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready for integration; base dfc5e54a, functional head 844fe9b1, proof-only singleton object-case slice.
next: Generalize the fixed dispatcher proof to arbitrary ordered object-constructor chains, reusing the exact five-step head-test boundary for a hit and proving the false-branch continuation boundary for a miss. Then connect tagged scalar/UInt8 chains through the same recursive relation.
```
