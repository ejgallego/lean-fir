# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c4eefca5
functional-head: 9bebfbef
contract-base: c4eefca5
clean-at-update: true
slice: Root-result foundation reuses the existing checked caller ABI spine. The actual supported export entry constructs its root index with no additional client premise. One push/pop equation handles heterogeneous caller/callee result kinds for direct, saturated and lazy calls. Case push and frame reindexing retain the index; empty-source-stack inversion recovers the exact root ABI and connects it to precise local return evidence. Entry and terminal boundaries are proved; global dispatcher preservation is not yet proved.
files: integration/talos/FirTalos/ConcreteRootResult.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: none changed. New focused internal ConcreteStructuredValidationAgreesAtRoot retains one result-kind index over existing branch-exact stack agreement; no existing relation is redesigned. No compiler-admission predicate, runtime behavior, ABI, W7 file, root gate, or resource contract changed. The index is compiler-owned proof state, not an application-supplied invariant or provenance map. All ten new lemmas are audited: two axiom-free, eight with exactly propext, Classical.choice, and Quot.sound. Existing trust debt is unchanged.
checks: Lean Beam update/sync/save of ConcreteRootResult and TrustInventory passed with zero diagnostics; refreshed TrustAudit passed all 44 exact inventories. Independent #print axioms probes measured every new lemma. Heterogeneous nested-call and wrong-root regression examples kernel-check. Stopped Beam, cleaned the Talos package, and passed focused lake -d integration/talos build FirTalos.ConcreteRootResult (3130 jobs). Forced direct lake env lean FirTalos/ConcreteRootResult.lean from integration/talos passed with empty diagnostics. make check passed: 730 cases, 2172/2172 comparisons, source/hash/trust gates, six negative trust tests, 228 bug cards and 38 mailbox tests. make talos-check passed: 3204 jobs, 243 maintained source files, 3165-job audit cone, forced 44-endpoint audit. Logs: .deps/root-result/. git diff --check passed. Clean git rebase main is up to date on c4eefca5; no source adaptation needed. Setup, manifests and toolchain retained unchanged. Exact containing-head Talos receipt is published in the canonical handoff after final verification, avoiding receipt/commit self-reference.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains confirmed with unchanged existing debt
blockers: none for this slice. A caller-spine equation is not yet global simulation preservation. The global relation still hides producer precision and root identity, so the public classified terminal theorem retains an existential represented kind. Compiler-derived admission closure and trap-aware structured semantics also remain open; no closed compiler theorem is claimed.
handoff: ready separate root-result foundation after immutable terminal-simulation 94706da7 (W6-ROOT-20260909-011). Extraction f1a5c789 and precision f5315157 remain separately queued; this successor does not replace those immutable objects or expand their review scope. The new canonical handoff pins this containing ready commit, with functional delta starting at 94706da7. No cleanup, W7 changes, main update, or remote push by W6 is included. Local-only.
next: Preserve ConcreteStructuredValidationAgreesAtRoot and exact producer kind through the global relation and its ordinary, direct, saturated, lazy and external administrative transitions. Reuse the proved root entry and empty-stack terminal consumer, then strengthen the existing classified terminal corollary to the export's selected ABI. Do not export the rooted-stack obligation as a new client premise. Discharge the universal classifier via the admission roadmap; coordinate trap semantics separately.
```
