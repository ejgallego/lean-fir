# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: blocked
base: e560266d
functional-head: 5c574ce6
contract-base: 08e0a763
clean-at-update: true
slice: Attached W7 candidate e560266d's canonical payload-link recycler to the generic released-block reuse contract. The production allocator is decomposed into exact validator/search/bump source equations; its legacy byte-exact ResidentAllocatorRel is explicitly the empty-index subrelation. Release, rewind, Array transfer, and complete object-slot initialization shapes are recorded. The concrete Array mutation primitive and Talos proof now use one zero-extending eight-byte store, preserving byte-exact memory without assuming stale high padding is already zero. Standalone release proofs explicitly select recycle := false.
files: Fir/Wasm/Concrete/Memory.lean; Fir/Wasm/Concrete/Runtime.lean; Fir/Wasm/Concrete/ArrayMutationCorrectness.lean; integration/talos/FirTalos.lean; integration/talos/FirTalos/ConcreteResidentAllocator.lean; integration/talos/FirTalos/ConcreteResidentArray.lean; integration/talos/FirTalos/ConcreteResidentBigNumericAllocator.lean; integration/talos/FirTalos/ConcreteResidentFloat.lean; integration/talos/FirTalos/ConcreteResidentRelease.lean; integration/talos/FirTalos/ConcreteResidentReleasedBlockReuse.lean; integration/talos/FirTalos/ConcreteResidentScalarBox.lean; coordination/lanes/wasm-proof.md
contracts: W6 concrete resident Array element and capacity writes now publish the complete eight-byte object lane with canonical zero high padding. The generic released-block contract is unchanged. W7 private links remain outside the canonical dead header at address + headerBytes, header-only blocks remain excluded by this candidate, and W7-owned emitter/artifact files were read-only.
checks: Lean Beam update/sync/save and complete FirTalos umbrella (pass: zero diagnostics); lake build FirTalos (pass: 3193 jobs); git diff --check (pass); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3193 jobs, receipt 68c27519a2ff8e1d5e19a5015c72fbdc62f5663c1c10a49caacffc91d1e41d1f); make check (validation pass: 730 unique cases and 2172/2172 comparisons equal, then blocked by the W7 candidate bug card missing required heading); trusted-assumptions/no-placeholders/mailbox-test run separately (pass: exactly one registered trusted axiom and 38 mailbox tests)
bug-cards: FIR-BUG-wasm-none-resident-arena-released-block-reuse (existing); FIR-BUG-wasm-none-direct-retirement-bypasses-resident-recycler (W7-owned candidate card; schema heading missing)
blockers: The original W7 candidate fails only bug-card schema validation because its direct-retirement card lacks `## Exact commands`; authoritative update W6-W7-20260902-005 requests a hygiene-only successor. Whole-machine nonempty reuse still requires an indexed/masked resident-memory relation and compiler-derived retirement of unreachable dead witness mappings before address rebinding.
handoff: clean W6 functional checkpoint 5c574ce6; proof and Talos gates are green, but integration is intentionally withheld until W7 publishes the exact hygiene successor and authorizes its candidate
next: Rebase onto the exact W7 hygiene successor, rerun make check and make talos-check, then publish the clean production-attachment handoff. Separately prove unreachable-dead-mapping retirement and the nonempty reuse-index machine relation.
```
