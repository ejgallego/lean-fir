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
base: 45761d92ade3c9c9eaa0b19629269206a56fb2c1, accepted main including the complete semantic, LCNF, concrete-runtime, and W6 heap-only UInt64 contract stack
functional-head: af7d10a807c7d401c9dac1b5d261688277d66d98
contract-base: 45761d92ade3c9c9eaa0b19629269206a56fb2c1; W7 consumes the accepted heap-only UInt64 representation without changing the semantic ABI, concrete layout constants, helper signatures, ownership policy, source entry, or symbolic Wasm instruction surface
clean-at-update: true
slice: Align the resident UInt64 box/unbox implementation and temporary concrete JavaScript host with upstream lean_box_uint64 and lean_unbox_uint64. Every UInt64 payload now allocates one ordinary 40-byte box; the decoder accepts only that box shape and rejects immediate or promoted tagged representations. Direct UInt64 values remain on the Wasm i64 lane and are unaffected.
files: Fir/Wasm/Emit/ResidentScalarBox.lean; integration/talos/artifact/concrete-host.mjs; integration/talos/artifact/resident-scalar-box-client.mjs; integration/talos/artifact/test-concrete-initial-runtime.mjs; bugs/FIR-BUG-impure-none-uint64-box-tagged.md; coordination/lanes/wasm-gen.md
contracts: consumes the accepted heap-only UInt64 contract at 45761d92. Helper names/signatures, the ordinary boxed layout, allocator, ownership operations, imports/exports, source semantics, and direct i64 ABI are unchanged. Only the invalid value-dependent representation split is removed.
checks: Lean Beam sync/save passed ResidentScalarBox with zero diagnostics. The focused resident-scalar-box build and Node client passed; all seven boundary payloads allocate exactly 40 bytes and round-trip bit-exactly, while immediate and promoted UInt64 inputs trap. The focused concrete-host regression passed. git diff --check passed. make check passed with 719 source cases, 9 direct-machine cases, 728 unique cases, 2166/2166 comparisons equal, and zero findings. make talos-setup selected Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254 and make talos-check passed all 3172 jobs. bash integration/talos/artifact/check.sh passed deterministic generation, every resident helper, both complete prettyM packages, the 719-case native/LCNF/V8 cone, concrete readiness, and both concrete artifact runs. No browser executable was configured.
evidence: The standalone resident-scalar-box module is 2364 bytes with SHA-256 0a93bcc3f7a90cf87a5a1cbec7bb1aee5f410e796e41b279d68272e2796840f6, module-owned memory, and zero imports. Plain closed prettyM is 83982 bytes with SHA-256 8e732adf8d9434f7eb80ca374b94c8f7c99c964a38c14838c2786a9f40e96e9e. Styled prettyM is 87396 bytes with SHA-256 77cbce512aab105978111efef15a784e263bbfe6237be1cfa5a149fedb66b254. The immutable tested package is _build/prettyM-current-releases/af7d10a807c7-40f7aa5e4847152e.
bug-cards: FIR-BUG-impure-none-uint64-box-tagged fixed
blockers: none
handoff: Fast-forward the clean containing status commit onto main. Functional head af7d10a807c7d401c9dac1b5d261688277d66d98 is based on accepted contract head 45761d92. Publication remains local-only; the deterministic prettyM package is validation evidence rather than a canonical pointer advance.
next: Ask W6 to connect the now-generation-ready resident UInt64 helper to the accepted concrete heap-only refinement. Audit USize separately against upstream; do not infer a representation change from this UInt64 repair. The already-open checked-decrement proof bridge remains independent.
```
