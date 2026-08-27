# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 425edb8904d66475089510a09d4119e8470f5bfc, exact current main
functional-head: 17097eff5cd8813ff2e57a0854a34fe55d94c322
contract-base: 425edb8904d66475089510a09d4119e8470f5bfc; no shared semantic, helper-signature, layout, ownership, or executable runtime contract changed
clean-at-update: true
slice: Replaces the opaque partial annotation traversal with an extensionally identical total structural traversal whose recursive list worker remains private, then exports closed explicit body equations for `boxUInt16TaggedFunction` and `boxUInt64ObjectFunction`. External proof consumers can rewrite either production alias directly to its executable source instructions without unfolding the mapper or any private emitter definition. Alias construction remains single-sourced; emitted instructions are unchanged.
files: Fir/Wasm/Emit/ResidentScalarBox.lean and this lane status
contracts: proof interface only. Resident helper bodies and signatures, semantic Wasm ABI, concrete layout, memory ownership, source call sites, linker behavior, generated helper bodies, and artifact bytes are unchanged.
checks: Lean Beam update/sync/save on Fir/Wasm/Emit/ResidentScalarBox.lean passed with zero diagnostics; an external importing probe rewrote both production alias bodies with the new theorems and passed Lean Beam plus `lake env lean`; focused `lake build Fir.Wasm.Emit.ResidentScalarBox` passed 16 jobs; git diff --check passed; make check passed 730 unique cases, 2172/2172 comparisons, the 721-case native/LCNF/V8 triangle, coverage policy, 211 bug cards, trusted-source validation, and 38 mailbox tests; make talos-setup plus make talos-check passed all 3174 jobs with exact receipt 18cf26d02e0adc7875633ec3a7376487dc93085a607684822c6374053de24b20; the complete deterministic artifact gate passed all resident helpers, paired source generation, package checks, shared validation, 44/44 concrete readiness artifacts, and raw/concrete differentials. The resident scalar artifact remains 3238 bytes and prettyM remains 87396 bytes with 322 functions and 25493 instruction-origin records.
evidence: closed facts Fir.Wasm.Emit.ResidentScalarBox.boxUInt16TaggedFunction_body and boxUInt64ObjectFunction_body; private total structural traversal behind the stable public mapper; functional checkpoint 17097eff5cd8813ff2e57a0854a34fe55d94c322.
bug-cards: none
blockers: none
handoff: Integrate the containing clean status checkpoint after verifying it descends from exact base 425edb89, then notify W6 on thread W6-W7-20260827-003 so its active proof branch can rebase. Integration remains owned by fir/root.
next: W6 rewrites the two production aliases to the explicit bodies and completes its generic physical annotation-erasure attachment; W7 returns to the consumer-driven generation queue.
```
