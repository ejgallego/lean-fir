# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a6f4510e on main; includes the accepted structured validation declaration/body/result provenance slice
functional-head: 42fb2d5d
contract-base: 72856600; makes the existing structured source validator total and proof-visible while proving the new list traversal extensionally equal to the former Array.all alternative check
clean-at-update: true
slice: W6.7f residual structured-validation slice. The production `supportedCodeWithJoins` validator is now a terminating syntax traversal with proof equations; its explicit alternative-list traversal is proved equivalent to the former Array.all acceptance shape. `ConcreteStructuredValidationFocus` retains the exact current join/local/result/case/sharing judgment, reconstructs the real root from `ConcreteSupportedFunction.validatedBodyAt`, and exposes checked inversions or continuation laws for let, join/jump, cases and selected alternatives, ownership, deletion, tag mutation, and every field mutation. This is static compiler validation state, not a recursive execution certificate.
files: Fir/Wasm/WellFormed.lean, integration/talos/FirTalos/ConcreteStructuredValidation.lean, integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, bugs/FIR-BUG-wasm-none-structured-validation-provenance.md, bugs/FIR-BUG-wasm-none-return-admission-refinement-direction.md, coordination/lanes/wasm-proof.md
contracts: isolated shared contract commit 72856600 changes only proof transparency/termination structure of the production validator; the acceptance Boolean is preserved, including an explicit theorem equating the new case-list traversal with the former Array.all check. No source semantics, symbolic Wasm ABI, concrete runtime, resident-helper signature, generated code, or executable ABI changed. W7 and validation consumers should rebase but require no code adaptation.
checks: functional head 42fb2d5d on current main a6f4510e; Lean Beam update/sync/save PASS with zero proof errors for Fir.Wasm.WellFormed and ConcreteStructuredValidation; Lean Beam refresh PASS for ConcreteResumableWasm; targeted lake build FirTalos.ConcreteResumableWasm PASS (3121 jobs); git diff --check PASS; make check PASS (125 harness tests, 685 unique validation cases, 2037/2037 comparisons, all oracle/coverage/bug-card/trusted-assumption gates); make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; serial make talos-check PASS (3144 jobs)
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance remains confirmed with residual state/root/transition API complete and relation attachment remaining; FIR-BUG-wasm-none-return-admission-refinement-direction confirmed because production return validation proves leanCompatible while current proof admission overrequires directional refines
blockers: none
handoff: integration may accept isolated contract commit 72856600, then functional head 42fb2d5d and this mailbox commit. The branch is based directly on main a6f4510e and the final serial gates are green.
next: attach `ConcreteStructuredValidationFocus` to active code and suspended supported-frame relations, transporting the already-proved residual transitions through calls/cases/joins. In parallel within W6, repair return admission to use the exact production `leanCompatible` contract. Then derive `ConcreteStructuredCompilerCurrentStepAdmission` constructors from validation plus the successful source step, independently of wasm32 memory safety.
```
