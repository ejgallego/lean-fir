# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: b8e847f99a1beb5e74630236a58c9f6ea2fdadc6, accepted main containing the exact scalar-box result-kind contract and the aligned W6 structured-validation checkpoint
functional-head: b766ebf4818b20c29a9a421246e75872853aa68d
contract-base: 29aff57112f19a1dece46aec5c7ea584cb2c91e3; W7 consumes the accepted upstream-derived scalar-box result mapping and the resident helpers already accepted on main without changing the physical Wasm representation, allocator, ownership policy, source semantics, or symbolic instruction surface
clean-at-update: true
slice: Add a permanent real-source conformance fixture for all seven final-LCNF scalar boxing families. Fourteen entries exercise both generic polymorphic round trips and the compiler-generated `_boxed` wrapper for each family. Exact wrapper result kinds come from `upstreamBoxResultKind?`. UInt8, UInt16, UInt32, UInt64, and Float must link to zero imports and zero runtime operations. USize and Float32 remain fully compiled and must expose exactly their matching box/unbox pair, with no unrelated residual operation.
files: Fir/Wasm/Emit/ScalarBoxingExamples.lean; Fir/Wasm/Emit/SourceExamples.lean; Fir/Wasm/Emit/SCALAR_BOXING_CONFORMANCE.md; coordination/lanes/wasm-gen.md
contracts: consumes the exact result-kind mapping at 29aff571 and the accepted resident linker/helper surface. No helper signature, physical representation, concrete layout, allocator, ownership, source semantic, or symbolic Wasm contract changed.
checks: Lean Beam sync/save passed ScalarBoxingExamples and SourceExamples with zero diagnostics. The focused `lake build Fir.Wasm.Emit.ScalarBoxingExamples Fir.Wasm.Emit.SourceExamples` dependency cone passed 59 jobs. git diff --check passed. make check passed with 719 source cases, 9 direct-machine cases, 728 unique cases, and 2166/2166 comparisons equal. make talos-setup completed and make talos-check passed all 3174 jobs. bash integration/talos/artifact/check.sh passed deterministic helper generation, every resident helper, both complete prettyM packages, the full 719-case validation cone, and concrete readiness; no browser executable was configured.
evidence: the source fixture recognizes exactly seven families and fourteen source entries. Five families close to zero imports and operations; the unresolved-family guard is exactly #["USize", "Float32"], and each of those retains only its own box/unbox pair. The resident-scalar-box module remained 2789 bytes. The final artifact gate selected immutable prettyM package _build/prettyM-current-releases/b8e847f99a1b-ba74bb8accdddede; plain and styled complete Wasm sizes remained 83982 and 87396 bytes.
bug-cards: none new
blockers: USize and Float32 require their shared contract/proof and resident-helper stacks before their readiness flags can become zero-frontier ratchets
handoff: Fast-forward the clean containing status commit onto main. Functional head b766ebf4818b20c29a9a421246e75872853aa68d is based on accepted main b8e847f99a1beb5e74630236a58c9f6ea2fdadc6. The fixture is internal validation infrastructure and does not advance a canonical consumer package pointer.
next: Land USize, then Float32, and flip each existing readiness flag only after its shared contract and resident helpers are accepted. Once both close, add the final external-engine all-fourteen-entry ratchet.
```
