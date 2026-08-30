# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 370e7e9f
functional-head: f9b0fa46
contract-base: 370e7e9f
clean-at-update: true
slice: Replaced raw declaration-local collection with an equivalent total ordered insertion traversal, alongside the already-transparent effective named-call refinement. Proved exact insertion lookup, hygiene-sublist, effective-to-raw coverage, name-unique update, and final exact-kind theorems over the production computations. Every effective compiler rewrite is now statically connected to a genuine hygienic source binder and its exact final local row, without a caller certificate.
files: Fir/Wasm/Lower.lean; coordination/lanes/wasm-proof.md
contracts: production raw local collection is now proof-transparent and list-based with the same left-to-right traversal, replacement order, error behavior, and emitted row order; no source semantics, runtime ABI, layout, instruction, validator acceptance, emitted helper, ownership, or resident-helper signature changed
checks: Lean Beam Lower update/sync/save (pass, zero diagnostics, source hash 6e1df317624eb63c); lake build Fir.Wasm.Lower (pass: 5 jobs); focused Talos proof cone FirTalos.ConcreteStructuredValidation/FirTalos.ConcreteFinalLcnfTyping (pass: 3128 jobs); git diff --check (pass); make check (pass: scalar artifact 5706 bytes/163 exports, 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: full compiler-dependent rebuild, 3189 jobs, receipt 2406503674978fceccb684e387ea46845adb3cb4bf8a354d7f368d25f1d7f471)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation remains confirmed; no new card in this slice
blockers: W6-W7-20260830-003 owns the exact object-case ABI repair; W6-W7-20260830-004 audits real named-call argument/result edges before selecting a directional validator or minimal-provenance policy
handoff: clean W6 functional head `f9b0fa46`, based exactly on accepted main `370e7e9f`; ready for fast-forward integration
next: Land this compiler-local provenance foundation, then package its root/residual current-code invariant and discharge DirectInternalCallCompilerAdmission.resultCompiled internally.
```
