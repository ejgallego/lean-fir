# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3f1af4e6 on main
functional-head: 71e8fae5 (recursive structured simulation now includes arbitrary normalized scalar UInt8 dispatch)
contract-base: 745610b0; proof-only extension over the accepted W6.7e recursion and existing concrete lazy-cache runtime contracts
clean-at-update: true
slice: Scalar dispatch is now structural over arbitrary normalized ScalarUInt8CaseAltsSupported tables. StateRelated plus the semantic getTag equation identifies the direct i32 discriminator lane exactly. Production compiler inversion peels each generated local/constant/equality/conditional test; a hit enters its branch and a miss recurses on the compiled suffix. The resulting path has exactly four target steps and one retained label per tested constructor, including a zero-test default suffix and no host operation. The recursive compiler theorem executes the selected branch and unwinds exactly those labels while retaining exact counts and the complete entry-relative cache/resource invariant without a target trace or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam update/sync/save version 106 hash f14f53e237d5d195 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean (zero local warnings); lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (642 unique cases, 1844/1844 comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready for integration; base 3f1af4e6, functional head 71e8fae5, proof-only arbitrary scalar-case slice.
next: Add the first effect constructor to the recursive structured relation, prioritizing ownership/reference-count operations whose exact compiler prefixes and entry-relative preservation theorems already exist. Keep heap-valued lazy publication and saturated closure calls as separate slices.
```
