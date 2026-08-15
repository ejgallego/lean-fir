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
base: f3b24d80 on main
functional-head: bda81d3a, direct core-Wasm fixed-width and USize resident helpers
contract-base: f3b24d80, including released WASM-CORE-SCALAR-SURFACE contract 43ab6619. The semantic ABI, concrete scalar layouts, ownership rules, helper signatures, and source semantics are unchanged
clean-at-update: true
slice: Every fixed-width resident helper that formerly synthesized a standard scalar operation now uses the released core Wasm instruction: UInt8/UInt16/UInt32 OR/XOR/shift/comparison, UInt32 CLZ and multiplication, UInt64 equality/add/sub/and/xor/complement/multiply/CTZ/remainder, and the corresponding USize comparison/arithmetic/bit/remainder family. UInt64.mod and USize.mod retain an explicit zero-divisor branch because Lean specifies n % 0 = n while i64.rem_u traps. Structural guards reject any reintroduced fixed-width/USize scalar loop and pin the direct CLZ, CTZ, multiply, and remainder operations
files: Fir/Wasm/Emit/ResidentFixedWidth.lean; Fir/Wasm/Emit/ResidentUSize.lean; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: no shared contract change. This is a W7 consumer of released contract 43ab6619. Source declarations, ABI kinds, helper names/signatures, concrete layouts, ownership, zero-divisor semantics, module memory ownership, import/export inventory, and W6 proof obligations are unchanged
artifacts: zero-import resident fixed-width module decreases from 13433 to 11608 bytes, a reduction of 1825 bytes (13.6%). Manifest records scalarStrategy direct-core-wasm and structuredScalarLoops 0. The complete deterministic prettyM gate remains green; no package is externally published by this slice
performance: seven AB/BA V8 rounds after warmup. UInt64.mod, 50000 calls: old [7.460320, 7.124759, 6.639175, 6.607987, 6.678680, 6.618997, 7.492992] ms, new [2.954911, 2.730950, 2.373457, 2.358288, 2.328222, 2.267658, 2.366353] ms; medians 6.678680 -> 2.366353, 2.822x. UInt64.mul, 100000 calls: old [11.057821, 12.872416, 13.178482, 12.735338, 12.958038, 12.636502, 13.028670] ms, new [5.942614, 4.743988, 4.747826, 4.777732, 4.733829, 4.622219, 4.617821] ms; medians 12.872416 -> 4.743988, 2.713x. UInt64.ctzFast, 200000 calls: old [6.772737, 8.060991, 7.856426, 7.944923, 7.860324, 7.886392, 7.883447] ms, new [8.669296, 7.165305, 7.105212, 7.268650, 7.148654, 7.102246, 7.100253] ms; medians 7.883447 -> 7.148654, 1.103x. Identical accumulators were checked each round
checks: Lean Beam update/sync/save PASS with zero diagnostics for ResidentUSize and ResidentFixedWidth. Focused artifact build PASS; the Node fixed-width client checks all exports, edge cases, scratch restoration, 1000 deterministic UInt64.mod differential cases, zero imports, and module-owned memory. git diff --check PASS. make check PASS 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 188 active bug cards, and 25 mailbox tests. make talos-setup PASS at Talos 0e05edbc and make talos-check PASS 3148 jobs. bash integration/talos/artifact/check.sh PASS deterministic resident and prettyM artifacts, exact fixed-width size 11608, 642/704 concrete products with the existing 62 initial-ByteArray blockers, 44/44 readiness artifacts, and all executable concrete cases
bug-cards: none
blockers: none
handoff: integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head bda81d3a is based directly on f3b24d80. No W6-owned file or shared contract changed, and no external artifact publication is authorized
next: integrate this direct fixed-width/USize consumer. Then audit the remaining resident floating-point and conversion helpers for hand-synthesized sequences that can consume the released scalar surface without changing Lean edge semantics
```
