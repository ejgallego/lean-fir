# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 4366086b8b77ffe0812adfbe848bdd1d12af553a
functional-head: 971bd45c9f2db7651779c984735bbd6e52773c9b
contract-base: 4366086b8b77ffe0812adfbe848bdd1d12af553a
clean-at-update: true
slice: Root-preserving ordinary direct-let transition. ConcreteStructuredValidatedCodeOutcome.advance_directLetWithFrames_of_step exposes the source/target frame equations already proved by the original rule; advance_directLet_of_step retains its old signature as a compatibility projection. advance_directLetAtRoot_of_step preserves the exact root index on a named validated successor by reusing the existing reindex lemma. Active/caller result indices, positive target path, witness/locals/runtime evolution and exact allocation-budget subtraction remain intact. An empty-stack regression recovers functionResult = rootResult from the successor without an extra equality premise.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteRootResult.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: none changed. Existing ReuseBudgetedDirectSupported, allocation budget, successful executeStep and internal root metadata remain premises. No shared relation, admission predicate, final-client premise, runtime ABI, W7 source, root gate or resource contract changed. All three direct-let endpoints have exactly the original rule's three standard plus 54 generated native-evaluation axioms; no new axiom, and no existing debt discharged.
checks: Lean Beam speculative producer checks, saved-source update/sync/save and refreshed TrustAudit passed all 49 exact inventories. A reconstructed original direct-let proof and the new endpoints have identical measured axiom sets. Stopped Beam, ran lake -d integration/talos clean FirTalos and the focused ConcreteRootResult build (3130 jobs). Forced direct lake env lean on ConcreteStructuredValidation and ConcreteRootResult passed; the former retains one pre-existing unused-simp warning at line 80, the latter has empty diagnostics. make talos-setup passed with unchanged manifests. make check passed: 730 cases, 2172/2172 equal comparisons, zero findings, source/hash/trust gates, six negative trust tests, 228 bug cards and 38 mailbox tests. make talos-check passed: 3204 combined jobs, 243 maintained source files, 3165-job audit cone and forced 49-endpoint audit. git diff --check passed. Rebased on accepted main 4366086b (CG-05B included); all five slice files are byte-identical to pre-rebase functional 7ecfd8f9. Logs: .deps/root-direct-let/. Exact containing-head receipt is published in the canonical handoff after final verification.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains confirmed with unchanged existing debt
blockers: none for this direct-let slice. Other local families, caller push/pop, administrative transitions and global root/precision-preserving assembly remain open. The universal classifier is still a compiler-proof obligation, the public classified terminal theorem still has an existential result kind, and trap semantics need a separately coordinated extension.
handoff: ready for standing fir/root under ROOT-W6-20260909-109. Consume only the complete clean containing checkpoint pinned by its canonical W6 completion, not an implicit later branch tip. Precise return and CG-05B are accepted ancestors. No W7 change, main update, cleanup or remote push by W6. Local-only.
next: Preserve the internal root index through the next bounded remaining transition, then caller push/pop and global assembly into the existing classified terminal theorem. Do not export the rooted premise to clients. The 14 W72 obligations remain separately queued; no whole-helper, tagged-result or CG-05B executable-source-equation debt is closed here.
```
