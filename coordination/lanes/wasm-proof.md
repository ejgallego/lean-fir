# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f5b15d8e on main
functional-head: bdb16b24 (exact structured execution reaches the first selected saturated-closure candidate body)
contract-base: f5b15d8e; proof-only extension over the accepted W6.7e recursion and existing concrete closure matcher/dispatch contracts
clean-at-update: true
slice: ClosureCandidateCase.matcherFinitePath derives the exact local-read/imported-matcher execution from the concrete host contract. structuredWasmResolvedClosureCandidateChainSelectedPrefixFinitePath then executes the real compiler fold through every preceding zero matcher and the first nonzero matcher. A prefix of n failed candidates reaches the selected body in exactly 3 * (n + 1) target steps under the precise n + 1 conditional-label frames. Failed matchers are proved store-neutral; the selected ownership-consuming store is retained. The theorem accepts neither target execution nor selected-branch certificates.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam 0.2.0-beta (source 662b514f) update/sync/save document version 14 hash dcb22c7b502a360f (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (122 tests, 633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 indexed comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: ready for the integration owner from functional commit bdb16b24; branch rebased on local main f5b15d8e and clean at this mailbox update.
next: Compose the selected candidate's existing capture/argument assembly with generated callee entry, recursive callee simulation, result-local write, and exact unwinding of the recorded conditional labels. Defer heap-valued lazy publication until the entry transport is made facts-aware.
```
