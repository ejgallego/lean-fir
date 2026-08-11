# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 5d4a9b3d on main
functional-head: 382998c4 (pointwise direct/saturated call resource push/pop composition)
contract-base: 5d4a9b3d; accepted pointwise control-stack and existing compiler/runtime contracts
clean-at-update: true
slice: Added the current entry-relative resource package and exact resource-scope boundary. Direct and saturated call entry now preserve the suspended caller and start a fresh exact callee scope. The general restoreCaller theorem composes arbitrary callee transports into the caller from the shared call-entry boundary, and both return protocols restore facts, budget, cache/ownership, ABI, and the structural stack without an evaluation or termination premise. Updated the W6 plan and theorem roadmap.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync/save zero errors; lake build FirTalos.ConcreteStructuredSimulation passed (3110 jobs); git diff --check passed; make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3133 jobs); make check passed, including 651/651 native/LCNF/V8 cases and 1962/1962 backend comparisons
bug-cards: none
blockers: none
handoff: ready; base 5d4a9b3d, functional head 382998c4, worktree clean before this mailbox update
next: Index exact active/suspended scopes as a parallel recursive resource stack over ConcreteStructuredFrameRel, then define the source-only local admission classifier and connect its first code/control families. Target-only case-label control follows before relation-wide advance assembly.
```
