# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 77efa825 on main
functional-head: 30f3152a
contract-base: 77efa825; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, return, bind-frame, and generated direct-call entry slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Proved the hereditary saved-caller bridge across generated callee effects. ReuseCapacityCodeEntryTransports.savedStateRelated reconstructs a suspended caller StateRelated at the evolved runtime/store/witness by combining the current callee runtime relation with the accumulated witness transport. ConcreteStructuredDirectCallEntryFocus.calleeEntryRelativeCacheFrame establishes the canonical callee cache frame with reflexive entry transports. bindFrame_of_yield and its cache-frame specialization consume an evolved hereditary frame plus related callee yield and exact unwound frames to establish the accepted ConcreteStructuredBindFrameFocus. No entry/exit store equality or target-execution certificate is assumed.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: lean-beam update/sync/save +full version 4, 0 errors and 0 warnings; lake env lean FirTalos/ConcreteStructuredSimulation.lean passed; lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm passed (3111 jobs); rg sorry/admit clean; git diff --check passed; make check passed (642 unique cases, 1844/1844 comparisons equal, 124 bug cards); make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3133 jobs)
bug-cards: none
blockers: none
handoff: ready for integration from wasm/talos-runtime; functional head 30f3152a over base 77efa825
next: Prove the structural callee-body simulation that threads the entry-relative cache frame and exact saved-frame suffix through each admitted code constructor, recursively nesting the same relation for internal calls.
```
