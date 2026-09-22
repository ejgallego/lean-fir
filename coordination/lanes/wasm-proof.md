# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1442602e985a5bb16b5470893137ec79a385bcb1
functional-head: bd242c4e0195c7ded17be77ff2faf9a58fed350d
contract-base: 1442602e985a5bb16b5470893137ec79a385bcb1
clean-at-update: true
slice: Derive canonical named-export lookup from production lowering rows and successful target validation, eliminating the caller's exported premise and arbitrary exportName from supported-export construction.
files: integration/talos/FirTalos/ConcreteExportRows.lean; integration/talos/FirTalos/Correctness/Exports.lean; integration/talos/FirTalos/ConcreteSupportedPipeline.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Executable lowering/adapter/resolver, runtime, ABI, relation, dispatcher, capture and W7 sources unchanged. Source export rows and function lookup determine the numeric target; target validation supplies public String-name uniqueness. No Name.toString injectivity assumption. The constructor returns the actual declaration.name.toString export; source checks, classification and pipeline equations remain explicit. Dynamic admission/resource/entry premises are untouched.
checks: Beam probes/update/sync/save and refreshed 182-endpoint audit pass. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteSupportedPipeline/TrustAudit batch build pass. Forced direct Lean for ConcreteExportRows, Correctness/Exports and ConcreteSupportedPipeline passes. make check and make talos-check pass, including forced exact audit; git diff --check passes. Local main rebase is current. Final containing-checkpoint gates are reported in the canonical request.
trust: Seven new endpoints use exactly the standard three axioms; valid_exportNames_nodup uses only propext and Quot.sound. Strengthened constructor remains standard-only; existing dynamic endpoint native dependencies unchanged. No new axioms or trust approval.
regressions: Actual static constructor retains selected declaration, function name, canonical cache row, effective result ABI and exact target export lookup without runtime/external alignment or export-table premises. Independent review found no loss of declaration identity or hidden injectivity assumption.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Not full success-only compiler admission, capture fidelity, resident linking or encoded bytes.
handoff: Ready for standing fir/root; frozen at clean containing checkpoint in canonical review request. Local-only; no main/board/W7 edit or push.
next: Expose exact validateSupported facts and isolate the residual closureFlowSafeProgram obligation in WasmSupported; do not pretend lowerSupported checks that condition or NamesUnique. Root's ROOT-LZ-20260922-001 owns input nomination; kernel-referable captured-program reification and closed-closure/pruning correspondence remain separately coordinated. No ByteArray contract or frontend/base framework started.
```
