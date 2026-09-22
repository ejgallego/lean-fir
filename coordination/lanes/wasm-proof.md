# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 26f20a60f7322adfda66a5fbef8b4d8f65238dd4
functional-head: 6efc836c2a7b43e42236596c96f1ad748a546558
contract-base: 26f20a60f7322adfda66a5fbef8b4d8f65238dd4
clean-at-update: true
slice: Derive supported-declaration and reuse-capacity checks from successful source validation; expose the exact residual closure-flow obligation and use it in supported-export construction.
files: integration/talos/FirTalos/ConcreteSourceValidation.lean; integration/talos/FirTalos/ConcreteSourceValidationTests.lean; integration/talos/FirTalos/ConcreteSupportedPipeline.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Executable lowering/adapter/resolver, runtime, ABI, relation, dispatcher, capture and W7 sources unchanged. Under lowerSupported success, WasmSupported is equivalent to closureFlowSafeProgram = true. The constructor replaces the opaque supported premise with that explicit residual condition and derives the checked components internally. NamesUnique, classification and pipeline equations remain explicit; dynamic admission/resource/entry premises are untouched.
checks: Beam probes/update/sync/save and refreshed 186-endpoint audit pass. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteSupportedPipeline/ConcreteSourceValidationTests/TrustAudit batch build pass. Forced direct Lean for ConcreteSourceValidation, ConcreteSourceValidationTests and ConcreteSupportedPipeline passes. make check and make talos-check pass, including forced exact audit; git diff --check passes. Final containing-checkpoint rebase/checks are reported in the canonical request.
trust: Four new endpoints and the strengthened constructor use exactly the standard three axioms. Existing dynamic endpoint native dependencies unchanged; executable guards are not theorem evidence. No new axioms or trust approval.
regressions: Existing dictionary-underapplication fixture validates and lowers successfully but fails closureFlowSafeProgram and supportedProgram. Separate guards expose that intentional boundary; fixture imports stay outside reusable proof modules. Actual export constructor still retains selected declaration, function name, canonical cache row, effective result ABI and exact target lookup. Independent review found no weakened conclusion or production change.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Not full success-only compiler admission, capture fidelity, resident linking or encoded bytes.
handoff: Ready for standing fir/root; frozen at clean containing checkpoint in canonical review request. Maintainer authorized continued push to ejgallego/lean-fir; publication result is recorded in that request. No main/board/W7 edit.
next: Derive NamesUnique from successful lowering and symbolic-module validation by transporting declaration names and proving duplicate-check soundness; a CheckedProgram wrapper alone would not remove client work. Root's ROOT-LZ-20260922-001 owns input nomination, including the exact capture's still-unknown closure-flow result. Captured-program reification, closed-closure/pruning correspondence and ByteArray contracts remain separate.
```
