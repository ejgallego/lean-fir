# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: cf0b6e89 on main
functional-head: 536fd94b (exact saturated-closure callee return, matcher unwind, and caller resumption)
contract-base: c90db59d; proof-only extension over the accepted saturated callee-entry and generic Flat contracts
clean-at-update: true
slice: locals_set?_idempotent proves that repeating a successful checked local write is a no-op. structuredWasmSaturatedCalleeReturnAndResumeFinitePath composes the one-result call return, selected-body result write, exact matcher-label unwind, and enclosing generic let reload/write pair in exactly matcherCount + 5 target steps. ConcreteStructuredSaturatedBindFrameFocus and its advance/advance_of_step theorems lift that path into the simulation relation: one source bind-frame step reconstructs the continuation code focus with the semantic result bound, original caller operand tail restored, local/environment relation and frame alignment preserved, and exact source/target frame suffixes. No theorem accepts a target execution, branch, or translation certificate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: rebased onto c90db59d; Lean Beam 0.2.0-beta (source 662b514f) update/sync/save ConcreteStructuredSimulation version 8 hash ed75aa0173077884 with zero errors and zero warnings; forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (122 tests, 633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 indexed comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green after rebase
bug-cards: none
blockers: none
handoff: none; the exact saturated callee-return slice landed on main at cf0b6e89 and the lane is active on hereditary-induction integration.
next: Connect the exact saturated entry theorem, recursive callee induction hypothesis, and this return/resume focus inside ReuseCapacityStructuredPureExternalLazyCodeEvaluates, then restore the enclosing ownership/resource frame with the entry-relative transports before continuation recursion. Defer heap-valued lazy publication until the entry transport is made facts-aware.
```
