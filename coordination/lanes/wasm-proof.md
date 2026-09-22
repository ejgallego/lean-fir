# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 51956dd8970e3a999002135a61ccbbc80b377dac
functional-head: 6882e8f31bbdcf7511d58892c4d3e1dceeb77c7b
contract-base: 51956dd8970e3a999002135a61ccbbc80b377dac
clean-at-update: true
slice: Derive source declaration-name uniqueness from successful lowering and symbolic validation, removing the NamesUnique premise from supported-export construction.
files: integration/talos/FirTalos/ConcreteDeclarationNames.lean; integration/talos/FirTalos/ConcreteDeclarationValidation.lean; integration/talos/FirTalos/ConcreteDeclarationAdmission.lean; integration/talos/FirTalos/ConcreteSourceValidationTests.lean; integration/talos/FirTalos/ConcreteSupportedPipeline.lean; integration/talos/FirTalos/Correctness/Exports.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Executable checker/lowering/adapter/resolver, runtime, ABI, relation, dispatcher, capture and W7 sources unchanged. Lowering preserves the complete name population, including duplicates. Soundness of the actual private hash-set checker gives combined external/internal uniqueness; successful adaptation supplies its validation equation. The constructor derives NamesUnique internally. Closure flow, classification and pipeline equations remain explicit; dynamic admission/resource/entry premises are untouched.
checks: Recovered crashed Beam session with generation-specific recovery; fresh sync/save, constructor print-axioms and refreshed 193-endpoint audit pass. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteSupportedPipeline/ConcreteSourceValidationTests/TrustAudit batch build pass. Forced direct Lean for all six changed proof/test modules passes. make check and make talos-check pass, including forced exact audit; git diff --check passes. Final containing-checkpoint rebase/checks are reported in the canonical request.
trust: Seven new endpoints and the strengthened constructor use exactly the standard three axioms. Production private definitions are opened proof-side, not replaced by an assumed shadow checker. Existing dynamic endpoint native dependencies unchanged; executable guards are not theorem evidence. No new axioms or trust approval.
regressions: Duplicated scalarId declarations lower successfully but validation/adaptation reject duplicateFunction; a same-named external/internal pair lowers successfully but is rejected as duplicateDeclaration. Actual export constructor still retains selected declaration, function name, canonical cache row, effective result ABI and exact target lookup without NamesUnique. Independent review found no circular uniqueness assumption, missed cross-table collision, or weakened conclusion.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Not full success-only compiler admission, capture fidelity, resident linking or encoded bytes.
handoff: Ready for standing fir/root; frozen at clean containing checkpoint in canonical review request. Maintainer authorized continued push to ejgallego/lean-fir; publication result is recorded in that request. No main/board/W7 edit.
next: Check the nominated immutable lean-zip capture's residual closureFlowSafeProgram condition before broad closure-ingress work. Root's ROOT-LZ-20260922-001 owns input nomination. Captured-program reification, closed-closure/pruning correspondence, dynamic admission and ByteArray contracts remain separate; no new per-program execution invariant or source checker change.
```
