# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: bd09501eecb1104e172d76dc375f816a04dd3df1
functional-head: 0fb6d9d7ec80e611dd4d5bc158ef1dabcf71a01a
contract-base: bd09501eecb1104e172d76dc375f816a04dd3df1
clean-at-update: true
slice: Generic production supported-export construction with exact declaration identity; derive concrete host key order, indexed key selection and table count, then adaptation/resolution alignment and exact host invocation-contract satisfaction.
files: integration/talos/FirTalos/ConcreteSupportedPipeline.lean; integration/talos/FirTalos/ConcreteResolver.lean; integration/talos/FirTalos/TrustAudit.lean; integration/talos/FirTalos/TrustInventory.lean; integration/talos/PLAN.md; integration/talos/W6-OBSERVABLE-CONTRACT-AND-TRUST.md; integration/talos/W6-LEAN-ZIP-FIRST-EXAMPLE.md; coordination/lanes/wasm-proof.md
contracts: none changed. Resolver executable definitions, runtime, ABI, relation, dispatcher, capture and W7 sources unchanged. The constructor derives handwritten context/function/index/body/layout and import-count fields. Supported-program/names checks, runtime/external contract alignment and named export lookup remain static premises; dynamic admission/resource/entry premises are untouched.
checks: Beam probes/update/sync/save and refreshed 166-endpoint audit pass. Beam stopped; lake -d integration/talos clean FirTalos and focused ConcreteSupportedPipeline/TrustAudit batch build pass. Forced direct Lean for ConcreteResolver and ConcreteSupportedPipeline passes. make check and make talos-check pass, including forced exact audit; git diff --check passes. Local main rebase is current. Final containing-checkpoint gates are reported in the canonical request.
trust: All seven new static endpoints have exactly the standard three axioms. Existing dynamic endpoint native dependencies unchanged. No new axioms or trust approval.
regressions: Actual static constructor recovers selected declaration equality, function name, canonical cache row and effective result ABI. Resolver key-order theorem retains positions, multiplicity and exact import identity; no semantic operation contract is inferred merely from key identity.
bug-cards: none new; FIR-BUG-wasm-none-endpoint-native-axiom-audit remains open.
blockers: none for this slice. Not full success-only compiler admission, capture fidelity, resident linking or encoded bytes.
handoff: Ready for standing fir/root; frozen at clean containing checkpoint in canonical review request. Local-only; no main/board/W7 edit or push.
next: Derive remaining runtime/external contract alignment and named export lookup generically. Root's ROOT-LZ-20260922-001 owns input nomination; kernel-referable captured-program reification and closed-closure/pruning correspondence remain separately coordinated. No ByteArray contract or frontend/base framework started.
```
