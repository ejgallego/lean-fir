# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ee228797
functional-head: c5b28b36
contract-base: ee228797
clean-at-update: true
slice: Derived the complete lazy-cache compiler site from nullary production validation, including declaration identity, annotation/effective result lanes, and nullary arity. The supported-function package constructs the generated cache environment. `admit_lazyHit_of_compiler` closes exact zero-byte hit admission from the recursively validated outcome; `admit_lazy_of_compiler` selects hit/miss from the current runtime and isolates only unimplemented miss shapes behind `ConcreteStructuredLazyMissBackendCoverageAt`.
files: integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-side compiler admission now reconstructs all shared lazy-cache facts from production validation. The named miss boundary records backend implementation coverage only; it is not a public source invariant and is intended to disappear. Source semantics, production acceptance, public runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged.
checks: Lean Beam refresh/save for ConcreteFinalLcnfTyping (pass: zero errors/warnings); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt 36aed295c6f3c20e25047e435223e2d7c3b734a69dbe58b0725c92497caf031d)
bug-cards: none
blockers: Lazy misses accepted by production but implemented by an external initializer or returning `.object`/`.tobject` remain the exact `ConcreteStructuredLazyMissBackendCoverageAt` gap. PA3 also retains the known producer-origin, closure-ingress, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `c5b28b36`, based exactly on accepted main `ee228797`; ready for fast-forward integration
next: Continue PA2 assembly with the return/use-site producer boundary or implement the miss-only backend families; do not reintroduce a caller source invariant.
```
