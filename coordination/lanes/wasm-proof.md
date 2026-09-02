# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: b5b9d410
functional-head: 709e908d
contract-base: b5b9d410
clean-at-update: true
slice: Added a representation-independent exact released-block reuse contract for the concrete Wasm heap. Canonical release yields a valid reusable block; a valid index contains unique, pairwise-disjoint dead extents; exact first-match removal returns a dead extent-compatible block and removes it uniquely; mismatch falls back to the existing bump allocator; rewind conservatively invalidates the index; full initialization restores a fresh live header without weakening live-object decoding. The proof audit rejected W7's first aux0-link candidate because it violated DeadCellRel and Header.isCanonicalFreedAt, and requested the bounded payload-link representation recorded in W6-W7-20260902-002. A witness-level theorem isolates the remaining global obligation: an old dead semantic location and a new live location cannot share one physical address in the current injective refinement witness.
files: Fir/Wasm/Concrete.lean; Fir/Wasm/Concrete/ReleasedBlockReuseCorrectness.lean; integration/talos/W6-RELEASED-BLOCK-REUSE-CONTRACT.md; coordination/lanes/wasm-proof.md
contracts: New proof-only ReleasedBlock, ReleasedBlockIndex, AllocatorInvariant, allocateReusing, rewind, initialization, and postcondition surfaces. Existing concrete layout, live/dead cell relations, runtime semantics, symbolic Wasm, resident-helper signatures, public ABI, and W7-owned emitter files are unchanged. W7's executable representation must keep private links outside the canonical dead header, expose exact unique unlink, and initialize the complete producer header before re-exposure.
checks: Lean Beam update/sync/save for ReleasedBlockReuseCorrectness and Fir.Wasm.Concrete (pass: zero diagnostics); focused lake build Fir.Wasm.Concrete.ReleasedBlockReuseCorrectness Fir.Wasm.Concrete (pass: 64 jobs); post-rebase git diff --check (pass); post-rebase make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one registered trusted axiom); post-rebase make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); post-rebase make talos-check (pass: 3191 jobs, exact receipt 5d97d20214d7e35312c82a5220aeaf4d207876a2a830fd1efaf451ef84b9557b); public theorem axiom audit (pass: no new project trusted axiom)
bug-cards: FIR-BUG-wasm-none-resident-arena-released-block-reuse (existing W7 card; proof boundary modeled, production repair still active)
blockers: Production attachment awaits W7's clean generation-ready candidate with the payload-link repair. Whole-machine reuse additionally requires compiler-derived retirement of unreachable dead witness mappings before an address is rebound.
handoff: clean W6 proof-only checkpoint rebased onto accepted main b5b9d410; ready for prompt integration independently of W7 production attachment
next: Land this abstract contract. Then prove unreachable-dead-mapping retirement from current roots/ownership, while W7 validates and publishes the bounded payload-link allocator candidate. Attach the executable implementation only after both sides have clean immutable checkpoints.
```
