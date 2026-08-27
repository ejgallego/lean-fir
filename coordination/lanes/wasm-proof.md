# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 4f1ebd80e8ab47a47d17c5794422cd4c53f15b6c
functional-head: c3b8bfd54382289a5ac1109df41e079a30380269
contract-base: 4f1ebd80e8ab47a47d17c5794422cd4c53f15b6c
clean-at-update: true
slice: Completes authoritative mailbox request W7-W6-20260814-008. The already-landed shared two-immediate Nat dispatcher, payload-decoding lemmas, concrete immediate remainder refinement, and installed zero/nonzero call theorems are now joined by one public case-independent theorem for the actual adapted resident Nat.mod function. For every canonical immediate pair it returns the exact canonical encoding of left % right, including Lean's left % 0 = left rule, preserves the Wasm store exactly, and preserves the caller operand-stack tail. The checked arbitrary-precision fallback remains the same opaque adapted branch with its existing malformed-input and ownership premises; it is unreachable in this immediate theorem.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; coordination/lanes/wasm-proof.md
contracts: Additive W6 proof interface over the accepted resident Nat.mod implementation already on main. No source semantics, LCNF lowering, emitter instruction, helper body or signature, semantic ABI, concrete layout, ownership rule, arbitrary-precision fallback, symbolic Wasm surface, artifact, or compiler behavior changed.
checks: Lean Beam update/sync/save passed with zero diagnostics for FirTalos/ConcreteResidentNat.lean. lake -d integration/talos build FirTalos.ConcreteResidentNat passed all 3,123 jobs. git diff --check passed. make check passed with 721/721 source cases, 9/9 direct-machine cases, 730 unique cases, 2,172/2,172 comparisons equal, zero findings, 211 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbc. make talos-check passed all 3,174 jobs with receipt 40cb01deb7f2c37683abb39463d2f0b280847bcedf55d061c685801fa9142d72.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Consume the exact clean integration checkpoint published by the completion event in authoritative mailbox thread W7-W6-20260814-008. It is based directly on main 4f1ebd80, has functional head c3b8bfd5, changes only the W6-owned Talos proof module plus this mailbox, and passes every required W6 gate.
next: Integrate this exact immediate Nat.mod checkpoint promptly; after landing, reassess the open wasm-proof mailbox and select the next dependency-ordered proof slice.
```
