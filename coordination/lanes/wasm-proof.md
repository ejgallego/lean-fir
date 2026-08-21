# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1fbe39e9
functional-head: 1952e707
contract-base: current shared admission 1fbe39e9; transparent impure-hygiene admission repair requested in W6-W7-20260820-021
clean-at-update: true
slice: Prepared the W6 side of declaration-wide local-collector agreement. Whole-program ImpureHygienic evidence now specializes to the exact source declaration selected by production lowering and exposes its binder-uniqueness Boolean. A common theorem proves that every successful supportedLetDeclKind? selection is exactly production effectiveLetValueKind, including precise box results and internal/external named-call refinement. The local-binder bug card now records that the existing opaque partial codeBinders traversal prevents a kernel collector proof even after Boolean admission, so the shared repair must expose the existing invariant structurally instead of adding a Wasm-only certificate.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-local-binder-name-uniqueness.md; coordination/lanes/wasm-proof.md
contracts: none changed. This proof-only preparation consumes current ABI classification, validator, lowering, and impure hygiene definitions. Operational thread W6-W7-20260820-021 requests the isolated shared admission/transparent-hygiene contract before the dependent collector theorem.
checks: Lean Beam update/sync/save passed for ConcreteStructuredValidation.lean with zero diagnostics and source hash bb5fe4755015c5b8. `lake build FirTalos.ConcreteStructuredValidation` passed (3,126 jobs). `git diff --check` passed. `make talos-setup` was already current at Talos 0e05edbc. `make check` passed (713 unique cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests). `make talos-check` passed (3,167 jobs). `make mailbox-check` passed (67 threads, 223 messages).
bug-cards: FIR-BUG-wasm-none-local-binder-name-uniqueness remains confirmed; FIR-BUG-impure-none-opaque-hygiene is the shared proof-interface dependency
blockers: none for this ready slice; dependent collector agreement waits for shared thread W6-W7-20260820-021
handoff: Integration may land proof commits ebadc482 and 1952e707 plus this containing mailbox commit on main 1fbe39e9. The pending shared contract must land separately and W6 must rebase before its collector-dependent continuation.
next: Rebase on the exact W6-W7-20260820-021 contract head, derive pairwise declaration binder freshness, prove collectLocals/refineNamedCallLocalKinds retains the validator-selected current let kind, eliminate the syntax-local compiled premise from ConcreteStructuredAlignedValidationState.letContinuation, and resume universal current-step compiler admission.
```
