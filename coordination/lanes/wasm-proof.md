# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: waiting
base: 7aab434b on main
functional-head: d6d6e855
contract-base: 93c12c30; generic `HeapObject.array elements capacity` ownership contract, with only the live prefix owned and spare capacity nonsemantic
clean-at-update: true
slice: Complete W6 resident generic-Array relation and mutation foundation. The stack closes W6/Talos exhaustive consumers; relates the resident ARRY header, logical live prefix, physical capacity, and tobject slots to semantic Arrays; proves allocation layout and whole-heap allocation; proves borrowed reads, raw replacement, swap, logical-size transitions, unique in-place push, and successful unique in-place pop. Push initializes the spare slot before making it live. Pop shrinks the owned prefix before recursively releasing the removed child. Both whole-heap theorems preserve non-target allocations, mapped header capacity, the witness, and the concrete heap frontier. A reusable `releaseTObject_refines` theorem handles mapped heap children and tagged checked no-ops.
files: Fir/LeanIR/Runtime.lean; Fir/Wasm/Concrete/Refinement.lean; Fir/Wasm/Concrete/HeapRefinement.lean; Fir/Wasm/Concrete/Runtime.lean; Fir/Wasm/Concrete/ArrayAllocationCorrectness.lean; Fir/Wasm/Concrete/ArrayHeapCorrectness.lean; Fir/Wasm/Concrete/ArrayMutationCorrectness.lean; Fir/Wasm/Concrete/PayloadMutationFrameCorrectness.lean; Fir/Wasm/Concrete/ReferenceCountCorrectness.lean; Fir/Wasm/Concrete/ResetReuseCorrectness.lean; integration/talos/FirTalos/Differential.lean; coordination/lanes/wasm-proof.md
contracts: isolated shared Array semantic contract commit 93c12c30 adds `HeapObject.array elements capacity` and live-prefix ownership. No symbolic Wasm ABI or W7 resident-helper signature changes in the proof slices. New W6 concrete helper models are proof-side specifications matching W7's stable exclusive push/pop order.
checks: Lean Beam update/sync PASS for Runtime and ArrayMutationCorrectness; forced targeted `lake build Fir.Wasm.Concrete.ArrayMutationCorrectness` PASS (31 jobs, with artifact restore disabled after the known local read-only .ilean cache issue); `git diff --check` PASS; `make check` passes root Lean/examples, 125 harness tests, bit-exact/external contracts, 676/676 native-LCNF cases, and 9/9 direct-machine cases, then stops only at W7-owned Fir/Wasm/Emit/Manifest.lean:191 missing the Array case; `make talos-setup` PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; `make talos-check` builds the W6 Array cone including FirTalos.Differential, ResetReuseCorrectness, ArrayMutationCorrectness, lowering/simulation/program modules, then stops only at W7-owned Manifest.lean:191 and proof/simpcase-owned ElimDeadRuntimeRel.lean Array exhaustiveness sites
bug-cards: none
blockers: W7 must land its existing HeapObject.array manifest serialization adaptation; proof/simpcase must land its Array exhaustive-match adaptation. W6 owns neither file and has not modified them.
handoff: Hold the dependency stack until the W7 Manifest and proof/simpcase Array adaptations are available. Integration can then assemble contract 93c12c30 through functional head d6d6e855, rebase, and rerun the complete root/Talos/artifact gates.
next: Rebase immediately after the two cross-lane Array consumers land, resolve any contract drift, rerun git diff --check, make check, make talos-check, and the W7 artifact gate, then publish a ready handoff. After acceptance, continue shared/persistent allocation-and-copy refinement for Array push/pop.
```
