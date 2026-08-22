# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: cf5b8b88, tracked prior W6 whole-carry-scan handoff over the accepted W7 checked-Nat contract
functional-head: 558e59e4
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved the complete per-limb data-producing prefix of W7's writeSumFrom helper. The shared arithmetic recurrence is instantiated in the writer's shifted eight-parameter/nine-local frame; exact adaptation and direct WP execute its four magnitude calls and produce the same pure low/high/carry triple as sumCarryFrom. A generic locally sourced half-limb store theorem factors the three-doubling byte address, checked local update, in-bounds write32, and non-scratch local frame. Its exact two-store composition writes the generated low then high word at offsets zero and four, and its adapter theorem matches W7's two private dynamic stores. The combined theorem materializes one pure addLimbWords digit while retaining the generated carry and exact successor memory for the back-edge. W6 PLAN records why semantic arithmetic should be shared while function-specific local layouts remain isolated.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. Proof-side helper names are explicitly unstable and may be reshaped for a cleaner induction boundary.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs without warnings. `git diff --check`, `make check`, and `make talos-check` passed; the final gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful installed writer-step checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head 558e59e4 and this containing status commit. W7 may rely on exact one-digit writer correctness without changing writeSumFrom's helper body, local layout, magnitude-accessor behavior, or signature.
next: Lift the exact writeSumFrom guard, data prefix, and back-edge through Talos's structured loop using count-index as variant and a store-indexed payload-prefix invariant. Then connect the completed payload and returned carry to allocateNatural of the operand sum and the existing checked typed-return paths.
```
