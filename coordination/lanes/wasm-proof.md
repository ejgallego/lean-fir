# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 4eb9f8bead10dac0fd1f8c73e145b562459934f3
functional-head: 281021e305cdef3c734c6182c62a6e45bb3f6a3d
contract-base: 189fcebeab02c508674f1a823544b8e9da9a0eaf
clean-at-update: true
slice: Derive fresh-leaf allocation/publication safety from existing concrete state refinement and consume it at actual caller return/pop.
files: integration/talos/FirTalos/ConcreteLazyPublication.lean; integration/talos/FirTalos/ConcreteLazyPublicationTests.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: No shared contract changed. retainedToken_beforeNext derives token freshness from existing capacity resolution and heap refinement; reachable_eq_leafRoot proves leaf graph shape. of_allocLeaf and allocLeaf_setGlobal derive disjointness and ordinary binding for actual allocation/publication without caller-supplied freshness or separation. The existing pop consumer and its historical scope/tail, physical focus, callee frame and witness/capacity premises are unchanged.
checks: Actual-module Beam update/sync/save passes; regression refresh recovered a stale import barrier. Beam stopped, clean FirTalos library and focused ConcreteLazyPublication/ConcreteLazyPublicationTests/TrustAudit batch build pass. Fresh direct Lean on both changed proof/test modules passes. make check and make talos-check including forced compiled/source trust audit pass. git diff --check passes. Containing-status-only checkpoint is refreshed before handoff.
trust: 227 maintained endpoints. Six additions: retainedToken_beforeNext uses propext/Quot.sound; reachable_eq_leafRoot uses propext; both publication producers and both regressions use standard3. No new generated dependency or semantic axiom; existing executable endpoint native debt is unchanged.
regressions: freshString_advance_popRetainedCache uses a nonempty retained-token map and arbitrary string contents, deriving ordinary binding before the actual one-source/two-target-step pop. Exact resumed focus, caller cache/ABI frame, joins and frames are retained. freshConstructorPublication_rejects_ownedRetainedToken rejects a fresh constructor whose owned child aliases the retained token. This does not prove the preceding compiled initializer execution.
bug-cards: none new. FIR-BUG-wasm-none-reuse-retained-token-ordinary and FIR-BUG-wasm-none-endpoint-native-axiom-audit remain separate open debt.
blockers: None for the bounded leaf slice. Nonempty owned graphs and the stronger hereditary resource history remain open; freshness alone cannot establish owned-graph separation. No concrete ByteArray producer, object/tobject admission expansion, PA3 closure, lean-zip theorem, resident linking or encoded bytes is claimed.
handoff: W6-ROOT-20260922-041 requests separate standing fir/root review after W6-ROOT-20260922-040, whose immutable subject remains 4eb9f8bead10dac0fd1f8c73e145b562459934f3. Maintainer requested continued lemma wiring; this later branch tip is not implicitly part of the predecessor review. Local-only clean checkpoint, frozen at handoff. No main/board/W7 edit or remote publication. Bounded read-only helper review found no soundness blocker; parent ran all Lean gates.
next: Extend ownership-derived publication safety beyond leaves to actual initializer graphs, and preserve caller-specific transport through the stronger hereditary resource history. Separately ROOT-W6-20260922-021 awaits structural reification/same-input lowering evidence for the exact retained Stored.olean. No substitute capture, historical LCNF, new native axiom or frontend framework is folded into this slice.
```
