# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: eac32289, tracked prior W6 resident-writer-step handoff over the accepted W7 checked-Nat contract
functional-head: 2b2ca0a2
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved total correctness of the complete structured loop in W7's installed writeSumFrom helper. A store-indexed invariant follows the generated mutable store across each exact low/high word pair, while the independent count-index variant proves termination without conflating memory progress with control progress. The theorem returns the pure addLimbWords terminal carry and an abstract payload frame after every limb has been written. Exact source/adaptation lemmas pin the proof to W7's generated guard, data prefix, back-edge, branch, loop, and surrounding block rather than to a proof-side approximation. W6 PLAN records the resulting boundary and its intended concrete payload-prefix specialization.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. Proof-side helper names are explicitly unstable and may be reshaped for a cleaner induction boundary.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs without warnings. `git diff --check`, `make check`, and `make talos-check` passed; the final gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful installed writer-step checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head 2b2ca0a2 and this containing status commit. W7 may rely on whole-loop writer correctness without changing writeSumFrom's helper body, local layout, magnitude-accessor behavior, or signature.
next: Specialize the abstract store frame to an exact written-prefix relation over the allocated payload, prove that the completed prefix decodes to the pure addLimbWords output, and connect the result and returned carry to allocateNatural of the operand sum and the existing checked typed-return paths.
```
