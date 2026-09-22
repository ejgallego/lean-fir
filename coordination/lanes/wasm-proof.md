# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: edab81deca2c8e55145ee5bf8d288844e1175f1c
functional-head: 2d7cc675d7b0697ef3f911d996e00322175339e1
contract-base: edab81deca2c8e55145ee5bf8d288844e1175f1c
clean-at-update: true
slice: Derive ConcreteExternalCallsAligned from name uniqueness and successful lowering/adaptation/resolution, eliminating the externalAligned caller premise from production supported-export construction.
files: integration/talos/FirTalos/ConcreteResolver.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteExternalAlignment.lean; integration/talos/FirTalos/ConcreteSupportedPipeline.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Resolver executable definitions, runtime, ABI, relation, dispatcher, capture and W7 sources unchanged. Exact import selection recovers the original source declaration/types and rules out internal-function fallback; resolver selection supplies singleton result, parameter count and installed externalFn. This derives the defined host-contract table, not correctness of arbitrary external implementations. Supported-program/names checks and named export lookup remain static premises; dynamic admission/resource/entry premises are untouched.
checks: Beam probes/update/sync/save pass; all four new endpoint axiom probes are standard-only. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteSupportedPipeline/TrustAudit batch build pass. Forced direct Lean for ConcreteResolver, ConcreteReuseCapacityCacheCorrectness, ConcreteExternalAlignment and ConcreteSupportedPipeline passes. make check and make talos-check pass, including forced 174-endpoint exact audit; git diff --check passes. Local main rebase is current. Final containing-checkpoint gates are reported in the canonical request. A read-only restored worktree-local ilean blocked an intermediate refresh; clean package regeneration recovered it without shared-cache or source changes.
trust: All four new endpoints have exactly the standard three axioms. Strengthened constructor remains standard-only; existing dynamic endpoint native dependencies unchanged. No new axioms or trust approval.
regressions: Actual static constructor retains selected declaration, function name, canonical cache row and effective result ABI without runtime/external alignment premises. External metadata is preserved as original source expressions, not inferred from equal physical lanes. Named-call fallback cannot substitute an internal function. Independent read-only review found no metadata loss, contract weakening or hidden stronger client premise.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Not full success-only compiler admission, capture fidelity, resident linking or encoded bytes.
handoff: Ready for standing fir/root; frozen at clean containing checkpoint in canonical review request. Local-only; no main/board/W7 edit or push.
next: Derive named export lookup from production export/function rows and successful target validation, using checked string-name uniqueness rather than assuming Name.toString injective. Root's ROOT-LZ-20260922-001 owns input nomination; kernel-referable captured-program reification and closed-closure/pruning correspondence remain separately coordinated. No ByteArray contract or frontend/base framework started.
```
