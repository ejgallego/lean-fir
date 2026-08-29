# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8b2b2a9c1c8ce5f3e552147d0f38bb3f54b65ff0
functional-head: ecd2a08d2124ef1e9fa1dd19f66b3b8b66be13c9
contract-base: 8b2b2a9c1c8ce5f3e552147d0f38bb3f54b65ff0
clean-at-update: true
slice: Strengthen the outer validated code dispatcher to return ConcreteStructuredSchemaValidatedCodeGlobalOutcome in every established branch, composing the complete direct successor with witness-indexed administrative, external, and schema-derived object-field successors.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive schema-global proof dispatcher only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, compiler admission, and established validated/finite-trace relations unchanged
checks: Lean Beam update/sync/save PASS for ConcreteStructuredValidation and ConcreteResumableWasm; lake build FirTalos.ConcreteResumableWasm PASS (3128 jobs); git diff --check PASS; make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt 4ee591f6124a8e306b82a05d163fa3f0c083e98dc3ee1bf8d71688f849504423)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: ready for integration; every ordinary-code admission now returns the schema-enriched global relation, the legacy arm proves both arbitrary-witness object-field cases unreachable, and the witness-indexed global theorem preserves or extends schema agreement across all seven validated outcome forms; no shared semantic/runtime/emission contract changed
next: Define the schema-indexed hereditary source invariant that supplies readiness for the evolving schema, instantiate the ranked finite-trace simulation with ConcreteStructuredSchemaValidatedCodeGlobalOutcome, then demote or retire the legacy module-global admission route.
```
