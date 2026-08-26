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
base: e5e4775a5197e3afd9899d79f5847e7bd1c5e1df, accepted main containing the exact scalar-box result-kind admission contract, the W6 heap-only UInt64 proof, the source-only carrier proof, and the scalar-box conformance audit
functional-head: bf4c9f4fdff1ba2461a88e607bb215982853f737
contract-base: 29aff57112f19a1dece46aec5c7ea584cb2c91e3; W7 consumes the accepted upstream-derived scalar-box result mapping without changing the physical Wasm representation, generic helper bodies, allocator, ownership policy, source entry, or symbolic instruction surface
clean-at-update: true
slice: Internalize the exact physical signatures emitted by Lean's ExplicitBoxing pass. The resident scalar-box module now exports fir_box_uint16_tagged and fir_box_uint64_object beside the generic object-family helpers. Exact aliases are derived mechanically from the existing generic bodies by retagging symbolic object-family result metadata only, so the generated Wasm instructions and W6-reviewed runtime implementations remain unchanged.
files: Fir/Wasm/Emit/ResidentScalarBox.lean; integration/talos/artifact/resident-scalar-box-client.mjs; Fir/Wasm/Emit/SCALAR_BOXING_CONFORMANCE.md; bugs/FIR-BUG-wasm-none-boxed-scalar-result-kind-drift.md; coordination/lanes/wasm-gen.md
contracts: consumes the exact result-kind admission contract at 29aff571. The helper frontier gains two exact aliases for .box .uint16 .tagged and .box .uint64 .object. Generic production helpers, concrete layouts, allocator and ownership operations, source semantics, and the physical i32/i64 Wasm ABI are unchanged.
checks: Lean Beam sync/save passed ResidentScalarBox with zero diagnostics. The focused ResidentScalarBox and Emit.Examples dependency cone passed. The standalone resident-scalar-box package built deterministically with module-owned memory and zero imports; the Node client exhaustively checked all 65,536 UInt16 inputs through generic and exact helpers and checked seven UInt64 boundary values with identical 40-byte layout and bit-exact results. git diff --check passed. make check passed with 719 source cases, 9 direct-machine cases, 728 unique cases, and 2166/2166 comparisons equal. make talos-setup completed and make talos-check passed all 3174 jobs. bash integration/talos/artifact/check.sh passed deterministic helper generation, every resident helper, both complete prettyM packages, the full validation cone, and concrete readiness; no browser executable was configured.
evidence: resident-scalar-box.wasm is 2789 bytes with SHA-256 0a41bb1b5d4f6facdcee75ff3a23af42e932757226b4aeac378ba3ee18a4b357. Its 999-byte manifest has SHA-256 b593d04c69ce9f2846789f3710f18b7a494991c1777af1447c9108a39db59a51. The final artifact gate selected immutable prettyM package _build/prettyM-current-releases/e5e4775a5197-3e354e562c4187bf; plain and styled complete Wasm sizes remained 83982 and 87396 bytes.
bug-cards: FIR-BUG-wasm-none-boxed-scalar-result-kind-drift fixed; no new cards
blockers: none
handoff: Fast-forward the clean containing status commit onto main. Functional head bf4c9f4fdff1ba2461a88e607bb215982853f737 is based on accepted contract head 29aff57112f19a1dece46aec5c7ea584cb2c91e3. Publication remains local-only; generated artifacts are validation evidence rather than a canonical package-pointer advance.
next: Ask W6 for the small refinement theorem connecting each exact alias to its already-proved generic helper; no runtime reimplementation is requested. Then continue the upstream mapping audit with USize and Float32 before closing the remaining seven scalar families.
```
