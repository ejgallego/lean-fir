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
base: c3a35d02500ee87598f0163e2c7a4201096a9735, exact current main
functional-head: f32458a2c00e7845e1a3d0b99e1c8630459ba668
contract-base: c3a35d02500ee87598f0163e2c7a4201096a9735; no shared semantic, helper-signature, layout, ownership, or executable runtime contract changed
clean-at-update: true
slice: Exposes the annotation-only source mapper already used by scalar aliases and two closed production facts for `boxUInt16TaggedFunction` and `boxUInt64ObjectFunction`. Each fact retains the generic parameter and local identifiers, states the exact tagged/object result and final-local kind, and equates the alias body to the generic body under the mapper. Executable instructions and alias construction remain single-sourced and unchanged.
files: Fir/Wasm/Emit/ResidentScalarBox.lean and this lane status
contracts: proof interface only. Resident helper bodies and signatures, semantic Wasm ABI, concrete layout, memory ownership, source call sites, linker behavior, and generated artifact bytes are unchanged.
checks: Lean Beam update/sync/save on Fir/Wasm/Emit/ResidentScalarBox.lean passed with zero diagnostics; an external-import Lean Beam probe consumed both public body facts with zero diagnostics; focused `lake build Fir.Wasm.Emit.ResidentScalarBox` passed 16 jobs and the probe passed under `lake env lean`; git diff --check passed; make check passed 730 unique cases, 2172/2172 comparisons, the 721-case native/LCNF/V8 triangle, coverage policy, 211 bug cards, trusted-source validation, and 38 mailbox tests; make talos-setup plus make talos-check passed all 3174 jobs with exact receipt 38e336312b2247482a863b784fb16db32153de99660d5aabd05886d2bb49339a. The artifact gate was not rerun because this slice changes only source-level proof facts and leaves emitted instructions and package inputs unchanged.
evidence: public mapper Fir.Wasm.Emit.ResidentScalarBox.retypeTObjectResultInstruction; closed facts boxUInt16TaggedFunction_exactSourceShape and boxUInt64ObjectFunction_exactSourceShape; functional checkpoint f32458a2c00e7845e1a3d0b99e1c8630459ba668.
bug-cards: none
blockers: none
handoff: Integrate the containing clean status checkpoint after verifying it descends from exact base c3a35d02, then notify W6 on thread W6-W7-20260827-002 so its active proof branch can rebase. Integration remains owned by fir/root.
next: W6 attaches its generic physical annotation-erasure proof to the two production aliases; W7 returns to the consumer-driven generation queue.
```
