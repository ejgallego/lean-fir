# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: acddf77f, tracked prior W6 allocation-bounded writer projection handoff over the accepted W7 checked-Nat contract
functional-head: 6d7ec622
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Completed the exact resident-Natural payload decoder boundary. The pure completed output appends the generated low=1/high=0 limb exactly when the final carry bit is one, has length count + carry, and denotes the exact operand sum. WrittenLimbPrefix now composes that terminal store with the writer history; ReadableLimbPrefix transports read32/read64 observations through ResidentMemoryRel; and successful raw Natural reservation discharges the payload bounds needed to prove that W6 readNaturalLimbs decodes the final W7 stores to the mathematical sum. The proof is deliberately extensional: LiveCellRel.natural requires the decoded value and payload fit, not byte-list equality with a canonical naturalLimbs representation. W6 PLAN records this correction and isolates the remaining object/header bridge.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. New theorem and proof-side helper names remain explicitly unstable.
checks: Lean Beam sync/save passed for FirTalos/ConcreteResidentNat.lean at source hash 19804e42a2c69e6e with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful completed-payload decoder checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head 6d7ec622 and this containing status commit. W7 may rely on a completed writer history plus successful raw Natural reservation and final ResidentMemoryRel yielding an exact W6 readNaturalLimbs result, without changing allocator, writeSumFrom, or carry-store signatures.
next: Factor the structural object theorem: preserve/transport the allocated Natural header and extent across disjoint payload writes, combine them with the exact decoder theorem into NaturalObjectRel or LiveCellRel.natural, and then discharge the checked helper's typed-return refinement.
```
