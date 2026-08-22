# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: b3b82380, pushed main accepting the exact W7 checked-Nat body and W6 typed-result checkpoint
functional-head: 95825b8c
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved the semantic arithmetic invariant shared by the installed sumCarryFrom and writeSumFrom loops. The exact two-i32 add-with-carry step preserves its base-2^32 value and derives that the generated sum of overflow flags is a bit. Its base-2^64 lift proves a processed-prefix theorem over equally sized low/high word lists. Canonical concrete UInt64 limbs split to the same word-pair value, and zero-padding the shorter operand to the validated maximum count preserves its value. The resulting end-to-end pure theorem states that the computed prefix plus final carry is exactly left + right. W6 PLAN records the machine-shaped-invariant/concrete-conversion boundary.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. Proof-side helper names are explicitly unstable and may be reshaped for a cleaner induction boundary.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,118 jobs. `git diff --check`, `make check`, `make talos-setup` at Talos 0e05edbc, and `make talos-check` passed; the final gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,167 Talos jobs.
bug-cards: none
blockers: none for landing this useful arithmetic-invariant checkpoint
handoff: Integration may fast-forward main from b3b82380 through W6 functional head 95825b8c and this containing status commit. W7 may continue consuming the already-landed typed-result checkpoint; this slice supplies the semantic equation W6 will attach to its installed helpers.
next: Prove exact adaptation and one-iteration execution for the installed sumCarryFrom/writeSumFrom machine step, then use Talos's structured-loop variant with count-index as the measure. The scan reuses the pure carry recurrence unchanged; the writer additionally proves exact low/high stores and a payload-byte frame. Compose those operational theorems with the arithmetic invariant and already-proved checked result paths.
```
