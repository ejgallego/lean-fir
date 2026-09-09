# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 918ed40c953b9be473bb26956b8689478addf297
functional-head: c30baa51a082c9e6d185000628dee5eb1defa07c
contract-base: 918ed40c953b9be473bb26956b8689478addf297
clean-at-update: true
slice: Precise root-preserving return transition. ConcreteStructuredValidatedCodeOutcome.advance_returnPreciseAtRoot_of_step retains the existing compiler-owned root index and the exact active functionResult in the returned outcome, reusing the prior two-step target path, witness and unchanged-frame equations. advance_returnYieldAtRoot_of_step derives an exact root-ABI yield at an empty source continuation without a new root/active-kind equality premise. The negative regression distinguishes object from tobject despite their common i32 lane.
files: integration/talos/FirTalos/ConcreteRootResult.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: none changed. Reuses advance_returnPrecise_of_step and ConcreteStructuredValidationAgreesAtRoot.reindex; no shared relation, public client premise, admission predicate, runtime ABI, W7 source, root gate or resource contract changed. Both new theorems have exactly propext, Classical.choice and Quot.sound; no generated or new trusted axiom. Existing endpoint native-evaluation debt is unchanged.
checks: Lean Beam speculative producer probe, saved-source update/sync/save of ConcreteRootResult and TrustInventory passed; refreshed TrustAudit passed all 46 exact inventories. Independent #print axioms probes measured both new theorems. Stopped Beam, ran lake -d integration/talos clean FirTalos, and passed the focused ConcreteRootResult build (3130 jobs) plus forced direct lake env lean FirTalos/ConcreteRootResult.lean with empty diagnostics. make talos-setup passed with unchanged manifests. make check passed: 730 cases, 2172/2172 equal comparisons, zero findings, source/hash/trust gates, six negative trust tests, 228 bug cards and 38 mailbox tests. make talos-check passed: 3204 combined jobs, 243 maintained source files, 3165-job audit cone and forced 46-endpoint audit. git diff --check passed. Rebased on accepted main 918ed40c (CG-05A included); proof/inventory/document trees unchanged from pre-rebase functional 23879739. Logs: .deps/root-return/. Exact containing-head receipt is published in the canonical handoff after final verification.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains confirmed with unchanged existing debt
blockers: none for this return slice. Global root preservation through the other branches and precision-preserving assembly remain open. The universal classifier is still a compiler-proof obligation, the public classified terminal theorem still has an existential result kind, and trap semantics require a separate coordinated extension.
handoff: ready for standing fir/root under ROOT-W6-20260909-107. Consume only the complete clean containing checkpoint pinned by its canonical W6 update, not an implicit later branch tip. All four predecessor W6 slices and CG-05A are accepted ancestors. No W7 change, main update, cleanup or remote push by W6. Local-only.
next: Preserve the compiler-owned root index through ordinary code and caller push/pop and administrative transitions, then compose the strengthened relation into the existing classified terminal theorem. Keep the rooted premise internal, not a new final-client obligation. The 14 W72 caller-rewrite obligations remain separately triaged behind this critical path; no whole-helper or tagged-result debt is closed here.
```
