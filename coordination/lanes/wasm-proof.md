# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 09c4d5c9, pushed main accepting the exact prettyM instruction-profile stack over the pure Nat limb invariant
functional-head: c16d3d23
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved the first operational bridge for the installed sumCarryFrom loop. A public proof-side source spelling pins W7's private sumStep inside the exact public helper body, successful call-index resolution adapts it to a fixed Talos program, and direct WP theorems execute both its arithmetic suffix and the complete four-accessor step. Given read-only magnitude calls at the selected index, the exact emitted low/high/carry locals equal the pure base-2^64 limb recurrence while parameters, store, unrelated scratch, and operand-stack tail are framed. A tiny emitted-operand-order model is proved equal to the canonical UInt32 arithmetic contract. W6 PLAN records why this keeps later whole-frame simplification stable.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. Proof-side helper names are explicitly unstable and may be reshaped for a cleaner induction boundary.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,118 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the final gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,167 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful installed-step checkpoint
handoff: Integration may fast-forward main from 09c4d5c9 through W6 functional head c16d3d23 and this containing status commit. W7 may rely on the exact one-step recurrence without changing its resident helper body or signature.
next: Lift the installed sumCarryFrom step through Talos's structured-loop variant using count-index as the decreasing measure and the processed prefix/carry as the invariant. Then instantiate the same step theorem in writeSumFrom's shifted local layout, add exact low/high stores and a payload-byte frame, and compose both loops with the pure addition theorem and checked result paths.
```
