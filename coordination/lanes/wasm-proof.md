# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f8954036
functional-head: 7a47337c
contract-base: f8954036
clean-at-update: true
slice: Adapted the W6 declaration-parameter proof stack to the bounded structural erased-lane classifier for Lean ExplicitBoxing. Cache parameter folding, structured validation, and final-LCNF typing now branch only on the effective `erasedOnlyParameter` result rather than reimposing the obsolete `tobject`-only test. The production-shaped regression covers the exact `tobject -> tagged -> void` path and checks the tagged bridge's effective erased lane.
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; coordination/lanes/wasm-proof.md
contracts: W6 proof adaptation only. No source semantics, validation/lowering policy, runtime ABI/layout, symbolic instruction, generated-code, ownership, or resident-helper contract changed. The proof follows the shared classifier exactly and adds no global tagged/erased compatibility.
checks: Lean Beam update/sync/save for ConcreteReuseCapacityCacheCorrectness, ConcreteStructuredValidation, ConcreteFinalLcnfTyping, and ConcreteCompilerCorrectnessContract (pass: zero blocking diagnostics); focused lake builds for all changed proof cones (pass); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt 6c1ec933ce70451ff135ff4f6c85311c5d7bce185896347341dda29516173e8b)
bug-cards: FIR-BUG-wasm-none-transitive-erased-closure-dispatch (shared classifier repair covered; exact widget run exposed a separate resident zero-sentinel conformance failure handed to W7)
blockers: Await authoritative W7 completion for the resident `fir_mark_persistent` physical-zero no-op and refreshed exact VBP widget package. The W6 concrete contract already treats erased sentinel zero as a no-op, so no W6 semantic weakening is required.
handoff: clean W6 functional head `7a47337c`, based on shared correction `f8954036`; ready to rebase onto the accepted W7 completion and rerun landing gates
next: Consume the exact W7 checkpoint, verify that the helper now refines the existing W6 sentinel contract without changing ordinary object decoding, then land the converged W7/W6 stack through integration.
```
