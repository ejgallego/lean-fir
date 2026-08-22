# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: d42a46bf, tracked prior W6 resident-Natural live-heap/typed-return handoff over the accepted W7 checked-Nat contract
functional-head: c7051393
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Constructed the final W6 heap directly from the exact resident-Natural writer history. Induction over WrittenLimbPrefix pairs every Talos low/high write32 with checked W6 writeUInt32 through ResidentMemoryRel.writeUInt32, preserving the original pre-allocation PrefixExtension, FrontierInvariant, and allocator cursor. Completion includes the optional carry limb and derives final ResidentMemoryRel plus payload bounds. The self-contained live-heap and typed-return corollaries now existentially construct their final MemoryState from only the raw W6 reservation, initial allocator memory relation, exact writer history, and mathematical value equation; no final heap/header/frontier/prefix/cursor/payload assumption remains. W6 PLAN narrows the remaining whole-helper connection to W7 allocator execution and attaching the existing exact writer-loop output.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. New theorem and proof-side helper names remain explicitly unstable.
checks: Lean Beam sync/save passed for FirTalos/ConcreteResidentNat.lean at source hash de0650243ab36ce6 with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful self-contained W6 heap-construction checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head c7051393 and this containing status commit. W7 may rely on raw W6 allocation plus initial ResidentMemoryRel and exact WrittenLimbPrefix sufficing to construct the final W6 heap, whole live-heap refinement, typed object relation, and generated typed-return suffix without any final-state certificate or helper signature change.
next: Prove the resident allocator call realizes the raw W6 allocateObject transition and initial ResidentMemoryRel, then attach wp_writeSumLoopProgram_of_exactPrefix to the actual writeSumFrom call so the completed producer supplies the self-contained closure; compose with the checked Nat.add branch/dispatcher theorem.
```
