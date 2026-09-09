# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d5e0b5ca
functional-head: 679837c9
contract-base: d5e0b5ca
clean-at-update: true
slice: Two precise-return producer lemmas retain the active function's exact result ABI through pointwise execution and validated suspended-frame transport. ConcreteStructuredCodePointwiseRel.advance_return_precise and ConcreteStructuredValidatedCodeOutcome.advance_returnPrecise_of_step expose facts previously hidden existentially. The older return APIs keep their signatures as compatibility wrappers. This removes a local hidden-interface obstruction; global/root result provenance and finite-prefix assembly remain separate.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; coordination/lanes/wasm-proof.md
contracts: none changed. No source/target relation, compiler-admission predicate, runtime behavior, ABI, W7 file, root gate, or resource contract changed. Existing semantic return admission is still required; physical lane compatibility is not promoted to semantic refinement. Neither new producer adds a precision premise. Both have exactly propext, Classical.choice, and Quot.sound, with no generated dependencies. Existing trust debt is unchanged.
checks: Lean Beam update/sync/save of both proof modules and TrustInventory passed; simulation/validation have zero errors and only the existing 19/1 warnings. Refreshed terminal-extraction importer passed with zero diagnostics; TrustAudit refreshed with 31 inventory messages and zero errors. Independent #print axioms probes verified both new exact inventories. Beam stopped; lake -d integration/talos clean FirTalos then make talos-check passed (3201 jobs, 238 maintained source files, 3163-job audit cone, forced 31-endpoint audit). Forced direct lake env lean of ConcreteStructuredSimulation.lean and ConcreteStructuredValidation.lean from integration/talos passed. make check passed: 730 cases, 2172/2172 comparisons, source/hash/trust gates, six negative trust tests, bug-card checks and 38 mailbox tests. Logs: .deps/return-precision/. git diff --check main..HEAD passed. Rebased the clean extraction predecessor onto accepted main d5e0b5ca; final git rebase main reports up to date. Setup, manifests and toolchain retained unchanged. Exact containing-head Talos receipt is published in the canonical handoff after final verification, avoiding receipt/commit self-reference.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains confirmed with unchanged existing debt
blockers: none for this slice. The general global relation still hides producer precision and does not anchor the active function's result to the root export. Finite-prefix assembly, compiler-derived admission closure, and trap-aware structured semantics remain open; no closed compiler theorem is claimed.
handoff: ready independent precision successor after the terminal-extraction review W6-ROOT-20260909-008. Its immutable f1a5c789 checkpoint remains available; rebased extraction functional/status equivalents are cb977e3c/e851efc8 on d5e0b5ca. The earlier bridge 3fc74692 is accepted on main and its thread is closed. The new canonical handoff pins this containing ready commit. No cleanup or W7 CG-01 work is included. Local-only; no main update or remote push by W6.
next: Retain the precise producer fact and root result identity across global simulation, then compose the simulation-produced finite target prefix with terminatesWith_of_validatedReturn. Preserve common finite-prefix composition and explicit runtime/resource contracts. Do not add a client provenance map, source invariant, or target-path certificate. Coordinate trap semantics separately.
```
