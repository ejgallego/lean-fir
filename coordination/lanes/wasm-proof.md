# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 4ca74a0cf0131a95a48a4db6c2c041339750d9c4
functional-head: e4d58c7fc25eb3fc459954e4d185cb04412588b3
contract-base: 4ca74a0cf0131a95a48a4db6c2c041339750d9c4
clean-at-update: true
slice: Audited the final object-case range premise against the concrete relation. Related heap constructors derive a UInt32 tag bound directly from their header, while immediate and promoted tagged references derive the exact UInt64 bound. The generic relation cannot derive the old UInt32 premise for promoted payloads because getTagStep truncates its UInt64 decoder result. Recorded the distinct semantic discrepancy and published W6-W7-20260830-003 requesting a non-truncating W7 case ABI. No caller provenance map or false compiler invariant was introduced.
files: Fir/Wasm/Concrete/ProjectionCorrectness.lean; bugs/FIR-BUG-wasm-none-object-case-actual-tag-truncation.md; coordination/lanes/wasm-proof.md
contracts: proof lemmas and confirmed bug card only; no semantic runtime, ABI, layout, validator, lowering, instruction, emitted-code, ownership, or resident-helper contract changed
checks: Lean Beam ProjectionCorrectness update/sync/save (pass, zero errors); lake build Fir.Wasm.Concrete.ProjectionCorrectness (pass: 24 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 1a77da3e70f929d49abaf73b49b2249559d050b97b651b0f6d70217a116c22ab)
bug-cards: FIR-BUG-wasm-none-object-case-actual-tag-truncation (confirmed)
blockers: object-case premise elimination waits on W6-W7-20260830-003; other PA1 families remain independent
handoff: clean W6 functional head `e4d58c7f`, based exactly on accepted main `4ca74a0c`; ready for fast-forward integration
next: Land this proof boundary, then continue independent PA1 return/direct-let/closure provenance while W7 implements the exact object-case ABI. Consume W6-W7-20260830-001 before choosing the non-directional return policy.
```
