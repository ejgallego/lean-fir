# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1121f917
functional-head: c4466855
contract-base: 1121f917
clean-at-update: true
slice: Five reusable terminal-return bridge lemmas connect the existing structured yield/frame relation to actual function and exported Wasm.run termination with RefinedReturnPost. The checked frame stack derives final case-label unwinding; adaptation supplies arity safety; exact singleton result selection, sufficient fuel, and arbitrary caller-tail restoration are derived. The yielding context need not equal the entry context. The previous review checkpoint 2d62fce5 is immutable and separately pinned by W6-ROOT-20260909-002; this is an independent successor.
files: integration/talos/FirTalos/ConcreteTerminalCorrectness.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos.lean; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: none changed. No compiler-admission predicate, source/target relation, runtime behavior, linker, ABI, W7 file, or root gate changed. The target prefix is internal simulation composition evidence, not a new client certificate. The new bridge is not the closed compiler theorem. All five new lemmas have only standard logical axioms (two or three); no generated dependencies.
checks: Lean Beam update/sync/save of ConcreteTerminalCorrectness and TrustInventory (pass: zero diagnostics); TrustAudit refreshed after a stale-import barrier and saved (pass: 24 inventory messages, zero errors); umbrella stale-import barrier was not treated as success. Stopped Beam and clean-built the Talos package before the initial checkpoint (3200 jobs, pass). Forced direct lake env lean on ConcreteTerminalCorrectness, TrustInventory, and TrustAudit (pass). Rebased onto accepted main 1121f917 with no proof-source or inventory changes. Post-rebase make check (pass: 730 cases, 2172/2172 comparisons equal, expanded source/trust/bug-card/mailbox gates green). Post-rebase make talos-check (pass: 3200 jobs, 237 maintained Lean sources, 3162-job focused trust build, forced direct audit of 24 endpoints; receipt 6827b1973ee791d7a5e4aca351cda97f65bb171cc660112f2e85ae5460d3d511). python3 integration/talos/test_proof_trust.py (pass: 6 tests, also run by the rebased root gate). Talos setup retained from the validated predecessor; toolchain and manifests unchanged. git diff --check (pass).
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains confirmed with unchanged existing debt
blockers: none for the return bridge. Global terminal extraction and root result-kind provenance remain open. The current structured control/outcome types have no trap branch, so fault adequacy needs a separate coordinated model extension.
handoff: ready independent successor rebased onto accepted main 1121f917; branch clean and frozen for integration. The predecessor's integration is accepted and closed by W6-ROOT-20260909-003. No proof or contract regression across the rebase; the new proof source and axiom inventories are identical to the pre-rebase checkpoint.
next: Derive the terminal yielded state from successful source termination and the maintained validated global relation; recover or retain precise root-result provenance before existential packaging. Reuse the new executable return bridge and the prefix constructed by simulation. Coordinate trap-aware structured semantics separately; do not add a client invariant or target path to the intended public theorem.
```
