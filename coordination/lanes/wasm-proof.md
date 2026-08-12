# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ad3bea7365c3ae9fde1899c8e2d655a18530bea7 on main; includes the accepted W7/validation stack and S7 escaping-closure fixtures
functional-head: a0bc93c3
contract-base: ad3bea73; consumes Lean 4.33, the accepted generic closure call ABI, and the current structured-Wasm/compiler contracts without changing any shared semantic or executable runtime contract
clean-at-update: true
slice: W6.7f current-node coverage derivation. ConcreteStructuredCompilerCurrentStepCoverage isolates the single ordinary-code law: a compiler-related node that actually steps has source-local admission at an exact cost within its retained budget. toCurrentStepClassifier derives the global classifier by structural inversion; the five staged call/bind/return shapes are already runnable. Coverage now directly constructs ConcreteGeneratedTraceSimulation and ConcreteFiniteTraceCorrect without exposing the classifier. The strong admission-free relation was repaired as a direct branch-exact sum after proof irrelevance invalidated its proof-indexed resource graph, and runnable code now carries canonical fact/budget indices.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, bugs/FIR-BUG-wasm-none-prop-outcome-proof-irrelevance.md, coordination/lanes/wasm-proof.md
contracts: none; proof-only relation repair and packaging over the accepted structured simulation, compiler rank, source semantics, and concrete structured-Wasm machine
checks: before rebase direct lake build FirTalos.ConcreteStructuredSimulation PASS (3119 jobs) and direct lake build FirTalos.ConcreteResumableWasm PASS (3120 jobs); Lean Beam update replayed the large dependency environment but sync did not return its readiness barrier and was cancelled after two minutes, so the direct targeted builds are the checkpoint authority; rebased conflict-free onto main ad3bea73; post-rebase git diff --check main..HEAD PASS; make check PASS (122 harness tests, 657/657 native-LCNF, 9/9 direct-machine, 657-case native-LCNF-V8 triangle, 666 unique cases, 1980/1980 comparisons, 6978 machine steps, zero findings, 146 active bug cards, Lean 4.33 trusted-assumption gate); make talos-setup retained 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check PASS (3143 jobs)
bug-cards: FIR-BUG-wasm-none-prop-outcome-proof-irrelevance fixed
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main ad3bea73 through functional head a0bc93c3 and this mailbox commit; no shared contract changed
next: prove ConcreteStructuredCompilerCurrentStepCoverage from the production compiler-supported fragment, package the canonical initial ConcreteStructuredSupportedGlobalOutcome from ConcreteSupportedExport, and remove both remaining internal premises from the final public export theorem
```
