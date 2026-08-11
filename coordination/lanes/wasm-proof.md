# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: bf00e5c9 on main
functional-head: 1f57b48d (hereditary pointwise resource stack with direct/saturated push and pop)
contract-base: bf00e5c9; accepted pointwise control/resource call boundaries and existing compiler/runtime contracts
clean-at-update: true
slice: Added ConcreteStructuredSuspendedResourceStack and ConcreteStructuredResourceStack. Adjacent active/caller scopes share exact runtime/store/witness entry boundaries by construction; frameRel transports all saved callers to the current heap and reconstructs ConcreteStructuredFrameRel. Generated direct and saturated entries push the unified relation. Direct and saturated bind returns compose the active callee into the caller, erase exactly the result fact, restore the caller scope, pop the resource chain, and construct the successor ConcreteStructuredStackRel. Updated the W6 plan and theorem roadmap.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: pre- and post-rebase Lean Beam update/sync/save zero errors; post-rebase lake build FirTalos.ConcreteStructuredSimulation passed (3110 jobs); git diff --check passed; make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; post-rebase make talos-check passed (3133 jobs); post-rebase make check passed with 653/653 native/LCNF/V8 cases, 1968/1968 equal backend comparisons, 662 unique cases, 6829 interpreter steps, 124 tag floors, 233 semantic domains, and zero findings
bug-cards: none
blockers: none
handoff: ready; base bf00e5c9, functional head 1f57b48d, worktree clean before this mailbox update
next: Define the source-only pointwise admission classifier over the combined control/resource relation and connect its first local code/control successor families. Target-only case-label control follows before relation-wide advance assembly.
```
