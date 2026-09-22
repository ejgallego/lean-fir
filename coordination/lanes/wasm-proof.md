# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0f3183e3e4c506173e9bc48564bbfd9bdd751507
functional-head: b4c50358df95ec6a0bab214962aa02f8e2cedc7c
contract-base: 189fcebeab02c508674f1a823544b8e9da9a0eaf
clean-at-update: true
slice: Derive publication safety for fresh owned graphs from allocation-local closure, with actual shared string/constructor construction.
files: integration/talos/FirTalos/ConcreteLazyPublication.lean; integration/talos/FirTalos/ConcreteLazyPublicationTests.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: No shared contract changed. HeapRegionClosed is a local source-heap edge property, initially derived from existing entry refinement and preserved by actual allocation using immediate field bounds. reachable derives transitive closure without acyclicity. of_freshRegion derives caller-token disjointness; freshRegion_setGlobal composes an explicit facts-aware prefix with publication/binding. No new source-machine invariant, arbitrary initializer certificate or central relation is introduced.
checks: Actual-module Beam update/sync/save passes; regression refresh recovered a stale import barrier. Beam stopped, clean FirTalos library and focused ConcreteLazyPublication/ConcreteLazyPublicationTests/TrustAudit batch build pass. Fresh direct Lean on both changed proof/test modules passes. make check and make talos-check including forced compiled/source trust audit pass. git diff --check passes. Containing-status-only checkpoint is refreshed before handoff.
trust: 234 maintained endpoints. Seven additions: HeapRegionClosed.reachable has no axioms; freshRegionClosed and of_freshRegion use propext/Quot.sound; allocation, binding and two regressions use standard3. No new generated dependency or semantic axiom; existing executable endpoint native debt is unchanged.
regressions: freshSharedGraph_publication allocates a string and a constructor owning it twice, derives field bounds and prefix transport from those actual operations, and preserves the nonempty caller token map. freshSharedGraph_reaches_leaf proves the child is genuinely reachable. Existing older-token alias rejection remains. This is source-runtime ownership transport, not a new compiled initializer or pop execution theorem.
bug-cards: none new. FIR-BUG-wasm-none-reuse-retained-token-ordinary and FIR-BUG-wasm-none-endpoint-native-axiom-audit remain separate open debt.
blockers: None for the bounded fresh-region slice. Actual initializer-body construction facts, permitted old-heap sharing and stronger hereditary resource history remain open. No concrete ByteArray producer, object/tobject admission expansion, PA3 closure, lean-zip theorem, resident linking or encoded bytes is claimed.
handoff: W6-ROOT-20260922-044 requests separate standing fir/root review. W6-ROOT-20260922-041 is closed as an accepted source review of exact 0f3183e3e, not a main landing; W6-ROOT-20260922-040 retains exact 4eb9f8be. Maintainer requested continuation meanwhile; this later branch tip belongs to neither predecessor review. Local-only clean checkpoint, frozen at handoff. No main/board/W7 edit, remote publication or evidence cleanup. Parent implemented and ran all gates.
next: Instantiate the construction laws for actual initializer bodies and connect facts-aware transport through the stronger historical resource scope. Separately ROOT-W6-20260922-021 awaits structural reification/same-input lowering evidence for the exact retained Stored.olean. No substitute capture, historical LCNF, new native axiom or frontend framework is folded into this slice.
```
