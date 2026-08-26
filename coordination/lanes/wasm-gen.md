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
base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24, accepted validated-effect checkpoint immediately below the atomic USize stack
functional-head: 9c896a1d2ba7b9559040ef9a0fab6a8d61cdc273
contract-base: 1db0b79d4b1607ee311432a27b5460853300399a; consumes the isolated heap-only USize semantic contract while retaining the existing semantic ABI signature, scalar-box layout, allocator, marker, and ownership contract
clean-at-update: true
slice: Internalizes heap-only `USize` box/unbox through the generic resident scalar-box layer. Every payload allocates the existing 40-byte owned object with marker 5, width 8, zero reserved lanes, reference count 1, and non-persistent ownership; tagged USize unboxing traps. The linked stack also contains the source semantics and fixtures, LCNF ElimDead adaptation, and W6 concrete refinement.
files: Fir/Wasm/Emit/ResidentScalarBox.lean; Fir/Wasm/Emit/ScalarBoxingExamples.lean; integration/talos/artifact/README.md; integration/talos/artifact/resident-scalar-box-client.mjs; coordination/lanes/wasm-gen.md
contracts: aligns the executable helper with the accepted heap-only USize contract. No semantic ABI signature, helper signature, concrete layout constant, allocator, marker, ownership rule, symbolic Wasm surface, public export, or unrelated scalar policy changes.
checks: Lean Beam and focused generation checks passed on the functional slice. The combined exact checkpoint passed git diff --check, the focused LCNF and W6 cones, make check with 721 source cases plus 9 direct-machine cases, 730 unique cases, and 2172/2172 comparisons equal, all 3174 Talos jobs, and bash integration/talos/artifact/check.sh including deterministic package publication, resident helpers, native/LCNF/V8 differentials, and concrete execution.
evidence: the seven-family source boxing ratchet now closes with zero imports and zero residual runtime operations. Small USize 42 and the maximum payload both allocate and round-trip through the exact owned heap representation; physical tagged USize input is rejected.
bug-cards: FIR-BUG-impure-none-usize-box-tagged fixed
blockers: none for the landed heap-only USize stack.
handoff: W7 functional head 9c896a1d is linked with LCNF proof head d78d128c and W6 functional head 0360367a through exact clean checkpoint de7c03ab on main.
next: Rebase wasm/generation on accepted main, then review the two already-claimed bounded Nat.land and USize tagged-Nat range-fact candidates independently. Tooling profile-contract v1 is next in the integration queue after its required post-USize rebase.
```
