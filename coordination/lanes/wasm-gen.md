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
base: f5cfd054 on main
functional-head: 4b5838a3, regenerate lean-zip raw against source Float construction and the standard libm v2 provider
contract-base: f5cfd054. No shared semantic contract changed; this package consumes the accepted source-unit capture, source-compiled Float, resident-helper, and fir.standard-libm/v2 surfaces without changing their signatures
clean-at-update: true
slice: The canonical Zip.Wasm.compressRaw package now compiles Lean's real Float.ofNat and Float.ofScientific definitions from final LCNF. Its reviewed symbolic frontier shrinks from three Float imports to exactly Float.log2, which is linked through the accepted generic standard-libm/v2 provider. The adapter and immutable exporter carry the v2 reservation/capability contract. The final module owns memory, has zero function and memory imports, preserves persistent-cache plus scratch-checkpoint ownership, and passes levels 1 through 10 against the native oracle
files: integration/lean-zip/EmitRaw.lean; integration/lean-zip/ProbeRaw.lean; integration/lean-zip/README.md; integration/lean-zip/export-raw-package.mjs; integration/lean-zip/export-raw-package.test.mjs; integration/lean-zip/lean-zip-raw-browser-adapter.mjs; integration/lean-zip/package-raw.mjs; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/raw-package-smoke.mjs; integration/lean-zip/raw-smoke.mjs; integration/lean-zip/standard-libm-runtime-contract.mjs; coordination/lanes/wasm-gen.md
contracts: No shared semantic contract changed. The raw input layout, public entry, module-memory ABI, exported allocator/frontier/rewind functions, ownership model, and package schema remain stable. The packaged runtime capability changes from the legacy heap-aware fir.standard-math/v1 facade to fir.standard-libm/v2 with its 65536-byte reserved-memory contract and platform-libm special-value/bounded-error policy
artifacts: immutable package integration/lean-zip/_build/lean-zip-raw-packages/4b5838a351f9-273d0d6cd9ca-2f49e64b74ce0c2a7c2c; canonical pointer integration/lean-zip/_build/lean-zip-raw-current. The 936001-byte Wasm is SHA-256 b0eaf85bb2ae2691329a966e8c01a80b661799919291b32358368e147a2cff3d. The 999548-byte function sidecar is SHA-256 e58efca4b9d9023754cd47044f4a7c3149273b812c8798fc6b250154a51154a5. BUILD.json records clean FIR 4b5838a351f9, lean-zip 273d0d6cd9ca, and zip-common 4425bab1f952
inventory: capture 769 declarations and 139 reviewed externals; pre-optimization closure 630 source functions plus 2782 resident helpers; final module 2305 functions, comprising 390 Lean-source and 1915 resident-helper functions with zero optimizer-or-linked-runtime functions. The 1619165-byte frontier has exactly lean.extern/Float.log2; the complete module has zero imports and exports Zip.Wasm.compressRaw, fir_heap_frontier, fir_heap_set_frontier, fir_heap_rewind, fir_heap_alloc, and memory
checks: LeanZipFir.Compile 102 jobs PASS. Raw package exporter tests 6/6 PASS. Repeated raw generation byte-identical; native/Wasm dispatcher differential PASS for five cases at levels 1 through 10; zero-import complete-runtime ByteArray adapter PASS; persistent-cache/scratch checkpoint reclamation PASS; package smoke and SHA256SUMS PASS. git diff --check PASS. make check PASS 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 188 active bug cards, and 25 mailbox tests. make talos-setup PASS at Talos 0e05edbc; make talos-check PASS 3148 jobs. bash integration/talos/artifact/check.sh PASS, including deterministic libm/source-Float/resident/prettyM artifacts, 642/704 concrete products with the existing 62 initial-ByteArray blockers, 44/44 readiness artifacts, and all executable concrete cases
bug-cards: none
blockers: none
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 4b5838a3 is based directly on f5cfd054. No W6-owned file changed and no feature branch or external package publication is authorized
follow-up: integration/lean-zip/check.sh reaches and passes the unrelated stored native/Wasm differential before its legacy stored package stops at a pre-existing completeWasmBytes ratchet (actual 12779, expected 12794); this slice does not touch that driver or contract. A future isolated stored-package metadata review may refresh it. The requested raw v2 package and every required FIR/W7 gate are green
```
