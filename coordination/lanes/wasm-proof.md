# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a1dce6f5
functional-head: 85f237f8
contract-base: a1dce6f5
clean-at-update: true
slice: Replaced the opaque partial named-call local-kind refinement with an equivalent total, structurally terminating traversal that publishes the exact ordered update list used by production lowering. Proved generic lookup preservation, avoidance, existence, and name-unique exact-kind theorems over the real update application. Row order and emitted behavior remain unchanged; this removes the opacity barrier behind the PA1 named-call destination-row proof without adding a certificate.
files: Fir/Wasm/Lower.lean; coordination/lanes/wasm-proof.md
contracts: production local-kind refinement implementation is now proof-transparent with the same traversal and row-order contract; no source semantics, runtime ABI, layout, instruction, validator acceptance, emitted helper, ownership, or resident-helper signature changed
checks: Lean Beam Lower update/sync/save (pass, zero diagnostics, source hash a3ba03646cf8c908); lake build Fir.Wasm.Lower (pass: 5 jobs); git diff --check (pass); make check (pass: scalar artifact 5706 bytes/163 exports, 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: full compiler-dependent rebuild, 3189 jobs, receipt 5e7f04fd4ba7e49ae1d997f4b20ceaa638d471a4785e7bff847a8135cda7c0d6)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation remains confirmed; no new card in this slice
blockers: W6-W7-20260830-003 owns the exact object-case ABI repair; W6-W7-20260830-004 audits real named-call argument/result edges before selecting a directional validator or minimal-provenance policy
handoff: clean W6 functional head `85f237f8`, based exactly on accepted main `a1dce6f5`; ready for fast-forward integration
next: Land and notify W7 of the proof-transparent lowering surface, then derive the compiler-owned current-code local-row provenance and discharge DirectInternalCallCompilerAdmission.resultCompiled from the exact update theorem.
```
