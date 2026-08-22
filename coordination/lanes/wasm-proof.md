# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ba92bee5, tracked prior W6 exact writer-read projection handoff over the accepted W7 checked-Nat contract
functional-head: aa382cdf
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Discharged the exact writer-read projection's pairwise-separation premise from successful Natural allocation. The generated three-doubling address is normalized to 8 * index; one payload-wide wasm32 bound removes modular reduction and proves all distinct low/high four-byte lanes disjoint. The raw allocateObject theorem consumes AllocatePost.endWithinAddressSpace directly, needing neither FrontierInvariant nor a linear-memory size premise. Both raw Natural reservation and ordinary allocateNatural now compose with WrittenLimbPrefix to yield exact final read32 output words. W6 PLAN records this address-space/runtime factoring lesson and the next canonical-limb boundary.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. New theorem and proof-side helper names remain explicitly unstable.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs without warnings. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful allocation-bounded writer projection checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head aa382cdf and this containing status commit. W7 may rely on successful raw Natural reservation discharging the exact writer's address nonwrap and disjoint-read premises without changing allocator or writeSumFrom signatures.
next: Identify the writer's count output limbs plus optional terminal carry with the canonical naturalLimbs of the mathematical sum, then connect the existing Natural decoder and NaturalResultRefines checked typed-return paths.
```
