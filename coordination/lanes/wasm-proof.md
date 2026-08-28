# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ef59c1a69b7c4aea03252d2aee809294cbbc30e6
functional-head: cfc9921de0ae6f2be3b9751e77ac5e4fcb5caa77
contract-base: ef59c1a69b7c4aea03252d2aee809294cbbc30e6
clean-at-update: true
slice: Repair production return admission without weakening object-family semantics, then factor the admitted primitive family through one source-facing safety judgment. Residual executable validation supplies compiler equations, the successful source step supplies dynamic effects, and ConcreteStructuredValidatedCodeCoreRel.admit_of_source_safe_step constructs exact current-node admission and allocation cost. ConcreteStructuredCompilerAdmissionLaws separates universal residual-validation provenance from source/phase safety, derives ConcreteStructuredCompilerCurrentStepAdmission, and feeds direct finite-trace and export-facing theorems. Lazy/cache was confirmed already pointwise; roadmap status was corrected.
files: bugs/FIR-BUG-wasm-none-return-admission-refinement-direction.md; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: No shared semantic contract changed. The proof-side current-step admission surface now mirrors production return leanCompatible carrier acceptance and separately requires SemanticValueAtAbi, preventing reverse object-family casts. New universal compiler-law packages are W6 proof interfaces; source semantics, concrete layout/runtime, resident-helper signatures, symbolic Wasm, and W7 artifacts are unchanged.
checks: Lean Beam update/sync/save passed with zero errors for ConcreteStructuredSimulation, ConcreteStructuredValidation, and ConcreteResumableWasm. Forced lake build FirTalos.ConcreteStructuredValidation passed all 3,127 jobs. Forced lake build FirTalos.ConcreteResumableWasm passed all 3,128 jobs. git diff --check passed. make check passed with 730 unique validation cases, 2,172/2,172 comparisons equal, zero findings, 212 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed all 3,182 jobs with exact receipt 1f33ba1a9e4d09f483b23088aa7bf887f3575324959bd98f5b489db011468efe.
bug-cards: FIR-BUG-wasm-none-return-admission-refinement-direction fixed
blockers: none
handoff: GREEN LIGHT. Fast-forward main from ef59c1a69b7c4aea03252d2aee809294cbbc30e6 through functional checkpoint cfc9921de0ae6f2be3b9751e77ac5e4fcb5caa77 plus this containing status commit. This lands the factored certificate-free compiler-admission route and fixed return boundary.
next: After integration acceptance, rebase and prove the universal residual-validation and source-safety fields from final-LCNF phase invariants. Separate root function context from active extended join context before adding join/jump admission. Keep finite wasm32 address-space safety as the independent subsequent theorem.
```
