# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 91b2f3acbf4f6a57bf73592aa53a2f6dd02aaf30
functional-head: b79a551b59f5b3b9efeae3c00126a326ebca8f5f
contract-base: 91b2f3acbf4f6a57bf73592aa53a2f6dd02aaf30
clean-at-update: true
slice: Completed PA0 with exact dispositions for all 20 admission branches (7 A, 3 B, 10 C, 0 E), settled the PA2 source-safety-first assembly boundary, and landed the first PA1 result-provenance slice: directional semantic ABI weakening, binding projection/weakening, directional return safety, and formal negative theorems for the two unsafe reverse tobject specializations.
files: docs/pass-correctness-plan.md; docs/w6-source-admission-audit.md; integration/talos/PLAN.md; integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; coordination/lanes/wasm-proof.md
contracts: proof-only semantic provenance helpers and planning status; no runtime semantics, ABI definition, layout, lowering, relation, emitted-code, or shared-contract change
checks: Lean Beam ConcreteRuntime sync (pass); Lean Beam ConcreteFinalLcnfTyping sync (pass, zero diagnostics); lake -d integration/talos build FirTalos.ConcreteFinalLcnfTyping (pass: 3128 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt feafaaab2916d91ba7d657693ee2d172efb6dc2d571a92d9550ec09875ec32fe)
bug-cards: none
blockers: none
handoff: active proof checkpoint at functional head b79a551b59f5b3b9efeae3c00126a326ebca8f5f; not yet requested for integration because PA1 continues on the same stable proof-only surface
next: Define the smallest compiler-owned use-site result provenance for reverse object-family returns, then prove the common direct-call/closure-call/lazy publication preservation theorem without adding a caller SourceInvariant.
```
