# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7affa1d2
functional-head: 178d3762
contract-base: 08e0a763
clean-at-update: true
slice: Review follow-up: expose the limits of finite-prefix observations, prove reusable result/fault consistency lemmas against executable Wasm.run, preserve the actual pretty trace facade's styling observation, and enforce exact compiled axiom inventories for 19 named endpoints. Add source-root and compiled-environment rejection tests. The immutable canonical recycler handoff remains 7affa1d2 (W6-W7-20260902-007); this is its separate successor, not a replacement or a new allocator adaptation.
files: integration/talos/FirTalos/ConcreteObservationSensitivity.lean; integration/talos/FirTalos/TrustAuditCore.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/FirTalos/TrustAuditTests.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos.lean; integration/talos/check-proof-trust.py; integration/talos/test_proof_trust.py; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-endpoint-native-axiom-audit.md; coordination/lanes/wasm-proof.md
contracts: none changed. Runtime behavior, lowering, linker, ABI, source/target relation, and compiler admission are unchanged. The destination now explicitly includes terminal represented results and semantic faults. Existing generated assumptions are inventoried as debt, not discharged or newly approved. All ten new sensitivity lemmas have only standard logical axioms or none. The isolated native rejection fixture is not a production theorem dependency.
checks: Lean Beam update/sync/save for all five new modules (pass: zero errors; TrustAudit emits 19 inventory messages); an umbrella Beam stale-import barrier was superseded by clean batch validation, not treated as success. Stopped Beam, ran lake -d integration/talos clean FirTalos, then make talos-check (pass: 3199 jobs, receipt d46febfae612ec9ce5a177d355d40f1f7b241139d2c4428584d319126b6a26f2). Forced direct lake env lean on all five new modules (pass). python3 integration/talos/check-proof-trust.py (pass: 236 maintained Lean sources, 3161-job focused build, forced compiled audit of 19 endpoints). python3 integration/talos/test_proof_trust.py (pass: 6 tests). make check (pass: 730 cases, 2172/2172 comparisons equal, tooling/trust/bug-card/mailbox gates green). make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254). git diff --check (pass). git rebase main (already current on 08e0a763).
bug-cards: FIR-BUG-wasm-none-endpoint-native-axiom-audit (confirmed: both source-invariant export endpoints retain 57 generated axioms each; sampled resident UInt64 theorem 20; literal export example 27)
blockers: none for this checkpoint. Root source-gate wiring and repository-wide trust/roadmap claims remain integration-owned. The closed compiler-derived theorem, terminal adequacy composition, native-dependency removal, and nonempty recycler machine refinement remain separate work.
handoff: ready successor after exact recycler checkpoint 7affa1d2; integrate in dependency order. Branch remains clean and frozen pending the integration owner's acceptance. Default Talos already imports the compiled endpoint gate; root should wire the expanded Python source scan and its tests into the shared check target.
next: Audit top-level return/trap correspondence and the executable Talos adequacy bridge while retaining PA1/PA2 provenance closure. Remove fixed scalar/boxing native dependencies in separately owned slices. Do not claim this checkpoint establishes a closed result-preserving compiler theorem or deployed-byte correctness.
```
