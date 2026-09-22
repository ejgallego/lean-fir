# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c95ca5773d27c9356b4579181daae90bf6a8d335
functional-head: 52a6169f9579d3e0312cacc47cbe5ada1d9d3ae0
contract-base: c95ca5773d27c9356b4579181daae90bf6a8d335
clean-at-update: true
slice: Derive ConcreteRuntimeCallsAligned from successful adaptation and concrete resolution, eliminating the runtimeAligned caller premise from production supported-export construction.
files: integration/talos/FirTalos/ConcreteResolver.lean; integration/talos/FirTalos/ConcreteRuntimeAlignment.lean; integration/talos/FirTalos/ConcreteSupportedPipeline.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Resolver executable definitions, runtime, ABI, relation, dispatcher, capture and W7 sources unchanged. New proof-side equality laws expose exact runtime identity; resolver selection gives the actual host function/signature, and adaptation preserves the import slot. This derives the defined host-contract table, not a new host semantic refinement. Supported-program/names checks, external contract alignment and named export lookup remain static premises; dynamic admission/resource/entry premises are untouched.
checks: Beam probes/update/sync/save and refreshed 170-endpoint audit pass. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteSupportedPipeline/TrustAudit batch build pass. Forced direct Lean for ConcreteResolver, ConcreteRuntimeAlignment and ConcreteSupportedPipeline passes. make check and make talos-check pass, including forced exact audit; git diff --check passes. Local main rebase is current. Final containing-checkpoint gates are reported in the canonical request.
trust: All four new endpoints have exactly the standard three axioms. Strengthened constructor remains standard-only; existing dynamic endpoint native dependencies unchanged. No new axioms or trust approval.
regressions: Actual static constructor recovers selected declaration equality, function name, canonical cache row and effective result ABI without a runtime-alignment premise. Runtime call lookup cannot select an internal function, a merely name-equal import, or a different executable host contract. Independent read-only review found no hidden stronger client premise.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Not full success-only compiler admission, capture fidelity, resident linking or encoded bytes.
handoff: Ready for standing fir/root; frozen at clean containing checkpoint in canonical review request. Local-only; no main/board/W7 edit or push.
next: Derive external contract alignment generically from exact declaration import metadata and resolver selection, then named export lookup. External name lookup must first rule out internal-function fallback. Root's ROOT-LZ-20260922-001 owns input nomination; kernel-referable captured-program reification and closed-closure/pruning correspondence remain separately coordinated. No ByteArray contract or frontend/base framework started.
```
