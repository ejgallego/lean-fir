# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1e11a8a456da5cfee4bd9d0ec63f80d80802af4e
functional-head: cb6cec5b
contract-base: 1e11a8a456da5cfee4bd9d0ec63f80d80802af4e
clean-at-update: true
slice: Factored compiler-derived ordinary internal-call admission. Successful current source execution now exposes evaluated arguments; residual validation plus compiler-local agreement reconstructs the exact production compileArgs result; arity preservation constructs the callee environment; and DirectInternalCallCompilerAdmission.toSite_of_step assembles the existing operational simulation site without a future trace or client execution certificate. The PA0 audit now distinguishes the remaining static destination-row equation from the two directional ABI facts that current leanCompatible validation cannot imply.
files: integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; coordination/lanes/wasm-proof.md
contracts: new proof-side compiler-admission record and extraction lemmas only; no semantic runtime, ABI, layout, validator, lowering, instruction, emitted-code, ownership, or resident-helper contract changed
checks: Lean Beam ConcreteFinalLcnfTyping update/sync/save (pass, zero errors and warnings, source hash ef3f143636c72dfb); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3128 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt b6402310e68d940b150bf226e8e6c13beb6ca499a4844575df2c78265fe7cc03)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation remains confirmed; no new card in this slice
blockers: W6-W7-20260830-003 owns the exact object-case ABI repair; W6-W7-20260830-004 audits real named-call argument/result edges before selecting a directional validator or minimal-provenance policy
handoff: clean W6 functional head `cb6cec5b`, based exactly on accepted main `1e11a8a4`; ready for fast-forward integration
next: Land this proof boundary, then derive the exact named-call destination local row from production collectLocals/refineNamedCallLocalKinds. Continue independent PA1 families while consuming W7 ABI audit responses; do not encode leanCompatible as a false directional theorem.
```
