# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: e488c816
functional-head: 5d4fbaa1
contract-base: 08e0a763
clean-at-update: true
slice: Attached W7 successor e488c816's canonical payload-link recycler to the generic released-block reuse contract. The production allocator is decomposed into exact validator/search/bump source equations; its legacy byte-exact ResidentAllocatorRel is explicitly the empty-index subrelation. Release, rewind, Array transfer, and complete object-slot initialization shapes are recorded. All 256 reserved-prefix words remain segregated extent heads, private links remain at address + headerBytes, the minimum indexed extent is 36 bytes, and exact 32-byte header-only blocks fall through to bump allocation. The superseded optional 128-slot header-pool adaptation was dropped. The concrete Array mutation primitive and Talos proof use one zero-extending eight-byte store, preserving byte-exact memory without assuming stale high padding is already zero. Standalone release proofs explicitly select recycle := false.
files: Fir/Wasm/Concrete/Memory.lean; Fir/Wasm/Concrete/Runtime.lean; Fir/Wasm/Concrete/ArrayMutationCorrectness.lean; integration/talos/FirTalos.lean; integration/talos/FirTalos/ConcreteResidentAllocator.lean; integration/talos/FirTalos/ConcreteResidentArray.lean; integration/talos/FirTalos/ConcreteResidentBigNumericAllocator.lean; integration/talos/FirTalos/ConcreteResidentFloat.lean; integration/talos/FirTalos/ConcreteResidentRelease.lean; integration/talos/FirTalos/ConcreteResidentReleasedBlockReuse.lean; integration/talos/FirTalos/ConcreteResidentScalarBox.lean; coordination/lanes/wasm-proof.md
contracts: W6 concrete resident Array element and capacity writes now publish the complete eight-byte object lane with canonical zero high padding. The generic released-block contract is unchanged. W7 private links remain outside the canonical dead header at address + headerBytes, header-only blocks remain conservatively excluded, and W7-owned emitter/artifact files were read-only.
checks: Lean Beam refresh/sync/save for ConcreteResidentAllocator and ConcreteResidentReleasedBlockReuse (pass: zero diagnostics); lake build FirTalos.ConcreteResidentReleasedBlockReuse (pass: 3084 jobs); lake build FirTalos (pass: 3193 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, bug-card/trust/mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3193 jobs, receipt 5e03eb568ef21970d783872c8b33ce9a6cd31293bef681f21e7ba598d39a3afe)
bug-cards: FIR-BUG-wasm-none-resident-arena-released-block-reuse (existing); FIR-BUG-wasm-none-direct-retirement-bypasses-resident-recycler (W7-owned; validator-clean on e488c816)
blockers: none for the canonical payload-link recycler attachment. Whole-machine nonempty reuse still requires an indexed/masked resident-memory relation and compiler-derived retirement of unreachable dead witness mappings before address rebinding.
handoff: clean W6 functional checkpoint 5d4fbaa1 rebased onto exact W7 successor e488c816; all W6 gates are green and the branch is frozen for integration
next: Integrate the canonical payload-link attachment. Separately prove unreachable-dead-mapping retirement and the nonempty reuse-index machine relation; treat any future header-only pool as a distinct contract/proof successor.
```
