# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 45bb086c on main
functional-head: 1e5c19fe (recursive structured simulation now includes arbitrary normalized object-constructor dispatch)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: Object dispatch is now structural over arbitrary normalized ObjectConstructorCaseAltsSupported tables. Production compiler inversion peels each generated getTag test. A hit takes its exact five-step prefix; a miss takes the same five steps and recurses on the compiled suffix. The resulting path has exactly five target steps and one retained label per tested constructor, including a zero-test default suffix. The recursive compiler theorem executes the selected branch and unwinds exactly those labels while retaining exact source/target counts and the complete entry-relative cache/resource invariant without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 100 hash 82eb5005a4b77f26 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready for integration; base 45bb086c, functional head 1e5c19fe, proof-only arbitrary object-case slice.
next: Connect arbitrary tagged scalar/UInt8 chains. Their generated tests omit the getTag import and use a four-step local/constant/equality/conditional prefix, but reuse the same structural suffix induction and replicated-label unwinding.
```
