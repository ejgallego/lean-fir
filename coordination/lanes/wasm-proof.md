# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: e1b41b10259edf9158a9dbb92550341737a46815
functional-head: 7fb4787cb0ed4a5bd7def2b2c1cf60887fd70226
contract-base: e1b41b10259edf9158a9dbb92550341737a46815
clean-at-update: true
slice: Exact-root terminal extraction and executable return assembly. Successful source evaluation or interpreter completion yields executable Talos export termination with RefinedReturnPost at spec.sourceResultKind, rather than an existential ABI.
files: integration/talos/FirTalos/ConcreteRootedTerminal.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Original runtime, ABI, relation, rank, dispatcher and W7 sources unchanged. Compiler admission, address-space safety, entry-runtime invariant and arity remain explicit. No target-path or client root/provenance premise added.
checks: Beam update/sync/save and refreshed 159-endpoint audit pass. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteRootedTerminal/TrustAudit batch build pass. Forced direct Lean passes. make check and make talos-check pass, including forced exact dependency audit; git diff --check passes. Local main rebase is current. Final containing-checkpoint checks are reported in the canonical review request.
trust: Extraction uses exactly the standard three axioms. Three executable return endpoints inherit exactly the accepted three plus 57 individually recorded generated dependencies. No new axioms or trust approval.
regressions: Actual extraction supplies target completion despite possible target-only case labels. Exact-root endpoint entails existential-kind compatibility but rejects unjustified arbitrary-kind substitution. The function theorem retains an arbitrary caller operand tail.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Compiler admission closure, fault correspondence, resident linking and encoded-byte correspondence are not claimed.
handoff: Ready for standing fir/root; branch remains frozen at the clean containing status commit named by the canonical review request. Local-only; no main/board/W7 edits or push.
next: Fresh proof-usable captureStored subject and static export/module-route census for the user-selected final-LCNF lean-zip milestone, coordinated with root/W7. ByteArray representation, operation coverage, object-result lazy misses and dynamic admission remain explicit follow-ups; no frontend/base semantics campaign started.
```
