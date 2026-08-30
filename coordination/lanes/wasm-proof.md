# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8fd317a0fecd7240df1468413e587609ab3c88f6
functional-head: c7cf66a0
contract-base: 8fd317a0fecd7240df1468413e587609ab3c88f6
clean-at-update: true
slice: Corrected the PA2 theorem boundary so ConcreteStructuredCompilerCurrentStepAdmission consumes the exact recursively validated current outcome instead of an arbitrary admission-free operational core. The current-step classifier and generated trace simulation now preserve ConcreteStructuredValidatedCodeGlobalOutcome at every successor, making residual production validation available to compiler-derived admission without a caller invariant. Updated the live roadmap, audit, and Talos plan to record this enforced boundary.
files: integration/talos/FirTalos/ConcreteResumableWasm.lean; docs/pass-correctness-plan.md; docs/w6-source-admission-audit.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-framework theorem signature and simulation relation corrected from supported-only to recursively validated; no source semantics, concrete runtime, ABI, layout, validator, lowering, instruction, emitted-code, ownership, or resident-helper contract changed
checks: Lean Beam ConcreteResumableWasm update/sync/save (pass, zero diagnostics, source hash 0795f7c78e4ceb08); lake build FirTalos.ConcreteResumableWasm (pass: 3128 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt a0f2fa0ee67d04d4c1e0da177fcd91e71347e55577a404bd417c145d2fa7d0ec)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation remains confirmed; no new card in this slice
blockers: W6-W7-20260830-003 owns the exact object-case ABI repair; W6-W7-20260830-004 audits real named-call argument/result edges before selecting a directional validator or minimal-provenance policy
handoff: clean W6 functional head `c7cf66a0`, based exactly on accepted main `8fd317a0`; ready for fast-forward integration
next: Land this proof boundary, then derive branch-local compiler admission from related.core.validation. Start with the exact named-call destination local row and continue the return/direct-let/closure provenance families while consuming W7 ABI audit responses.
```
