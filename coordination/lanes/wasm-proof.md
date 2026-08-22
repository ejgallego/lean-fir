# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 692c3ad9, tracked prior W6 resident-Natural object-relation handoff over the accepted W7 checked-Nat contract
functional-head: c016ea29
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Lifted the derived resident-Natural object through the complete refinement witness and live heap, then through the generated typed-return suffix. A reusable fresh-Natural theorem consumes raw reservation, final NaturalObjectRel, PrefixExtension, and FrontierInvariant and derives bindNatural witness extension, closure-allocation persistence, descriptor/location freshness, spatial region/disjointness, release-fuel growth, LiveCellRel.natural, complete LiveHeapRel, and typed ValueRel. The exact completed-writer theorem now composes directly to that result; the local-get/object-round-trip suffix returns the address under the extended witness with unchanged final resident memory. W6 PLAN isolates the remaining state-transport proof: mirror every exact Talos write32 through W6 writeUInt32 to construct the final MemoryState and preserve prefix/frontier/cursor/payload facts.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. New theorem and proof-side helper names remain explicitly unstable.
checks: Lean Beam sync/save passed for FirTalos/ConcreteResidentNat.lean at source hash 851637b74f6447de with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful live-heap and typed-return checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head c016ea29 and this containing status commit. W7 may rely on exact writer state plus the raw allocator/final heap invariants yielding witness extension, closure persistence, full live-heap refinement, typed object relation, and the generated typed-return suffix without changing any helper signature.
next: Prove exact state transport for the writer history by pairing each Talos write32 with W6 writeUInt32 under ResidentMemoryRel, preserving PrefixExtension, FrontierInvariant, cursor equality, and payload bounds; attach that constructed state to the existing writer-loop execution and whole checked-addition theorem.
```
