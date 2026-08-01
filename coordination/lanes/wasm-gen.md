# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: 3c437f2d
functional-head: 2ed6deb4
contract-base: dbd7d934 published on integration/closure-ownership
clean-at-update: true
slice: Executable closure-application ownership adapter and twice-application regression
files: Fir/LeanIR/Runtime.lean; Fir/LeanIR/Interpreter.lean; scripts/wasm_semantic_host.mjs; scripts/test_wasm_validation_externals.mjs; closure bug card
contracts: CLOSURE-APPLICATION-OWNERSHIP published contract dbd7d934 from provenance d392e194; executable adapter 2ed6deb4
checks: The unsplit contract intentionally fails AlphaEqvCode and FirTalos.Correctness.Semantics until their owners adapt; the already-landed float-only slice passed all required gates
bug-cards: FIR-BUG-wasm-none-closure-application-ownership
blockers: lcnf-proof adaptation and wasm-proof refinement handoffs
handoff: none; keep dbd7d934 and 2ed6deb4 outside main until both proof handoffs are green
next: Hold the adapter stable, integrate green proof handoffs under the milestone lease, then rebase and rerun W7 gates
```
