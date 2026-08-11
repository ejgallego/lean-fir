# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 45bb086c on main
functional-head: a4366d32 (recursive structured simulation now includes ordered two-arm object-constructor dispatch)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: Ordered object dispatch is now recursive through two constructor arms and a default. Exact helper theorems execute a successful generated getTag test, execute a failed test into the remaining chain, and pop an arbitrary number of replicated case-label frames. The recursive compiler theorem covers first-arm hit (five prefix steps, one label), second-arm hit after one miss (ten prefix steps, two labels), and default after two misses (ten prefix steps, two labels), retaining exact source/target counts and the complete entry-relative cache/resource invariant without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 96 hash 1bfc85b2d0846be7 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; the ordered two-arm object-case slice landed on main at 45bb086c and the lane is active on arbitrary case chains.
next: Generalize the now-checked hit/miss/label interface from two arms to arbitrary ObjectConstructorCaseAltsSupported chains. Then connect tagged scalar/UInt8 chains, whose generated tests omit the getTag import but use the same branch-label recursion.
```
