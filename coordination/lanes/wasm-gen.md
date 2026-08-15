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
base: 12562b90 on main
functional-head: 0c5dda71, close the genuine standard libm frontier with an upstream-aligned Wasm provider
contract-base: 12562b90. The six existing Float external names and binary64 signatures are unchanged; the semantic ABI, concrete layouts, arena ownership, and W6 proof contracts are unchanged
clean-at-update: true
slice: Lean upstream implements Float.sin, Float.cos, Float.acos, Float.atan2, Float.cbrt, and Float.log2 as opaque platform-C externals rather than Lean definitions or core Wasm operations. FIR now preserves that boundary explicitly, compiles a six-function-only Emscripten libm provider, and closes it through the existing exact-name/signature runtime linker. The linked acceptance module owns memory, has zero imports, and exposes only bit-lane probes plus memory. Core-Wasm Float helpers and source-compiled Float.ofNat/ofScientific remain outside this provider
files: Fir/Wasm/Emit/ResidentLibm.lean; integration/wasm-runtime/libm-runtime.c; integration/wasm-runtime/contract.mjs; integration/wasm-runtime/README.md; integration/talos/artifact/FirWasmArtifactMain.lean; integration/talos/artifact/run-resident-libm.mjs; integration/talos/artifact/check.sh; coordination/lanes/wasm-gen.md
contracts: No shared semantic contract changed. The additive fir.standard-libm/v2 packaging capability records the existing six external declarations, 65536-byte Emscripten low-memory reservation, and platform-libm special-value/bounded-error numeric policy. The legacy fir.standard-math/v1 compatibility surface remains intact for packages not yet regenerated
artifacts: symbolic frontier is 486 bytes at SHA-256 3eacb18c3d611f6af09574559ca2697ca919cbd3006b5164021c511d1fb78beb with exactly six lean.extern function imports. The six-only provider is 11516 bytes at SHA-256 e1df729b532f240137c26fca28f09c6d66e043e8441bf64e4af9560ab4247f5c. The linked module is 11454 bytes at SHA-256 f5e516e1f237c3dd641317338e445844fc20c8cbefcc26f21deb501cb29cdd4f, owns memory, has zero imports, and exports resident_Float_{sin,cos,acos,atan2,cbrt,log2}_bits plus memory. No external package was published
numeric-policy: Platform libm implementations are not universally bit-identical. Native glibc and Emscripten differ by one or two ULP for valid cbrt inputs and can choose different NaN signs for out-of-domain acos. The acceptance gate therefore checks exact binary64 transport and mandated special values, NaN classification, deterministic Wasm bytes, and an eight-ULP finite-result bound against an independent JavaScript libm. This matches rather than strengthens Lean's upstream portability boundary
performance: no headline runtime benchmark was run. The complete six-function artifact is 11454 bytes; consumer performance needs an order-balanced application benchmark after regeneration
checks: Lean Beam update/sync/save PASS with zero diagnostics for ResidentLibm. Focused 93-job artifact dependency cone PASS. Node syntax and focused frontier/link/runtime behavior PASS. git diff --check PASS. Final make check PASS 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 188 active bug cards, and 25 mailbox tests. make talos-setup PASS at Talos 0e05edbc; make talos-check PASS 3148 jobs. Final bash integration/talos/artifact/check.sh PASS, including byte-identical repeated libm provider and linked module, deterministic resident and prettyM artifacts, 642/704 concrete products with the existing 62 initial-ByteArray blockers, 44/44 readiness artifacts, and all executable concrete cases
bug-cards: none
blockers: none
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 0c5dda71 is based directly on 12562b90. No W6-owned file changed and no external artifact publication is authorized
follow-up: Regenerate interested closed applications so their actual remaining import inventory can select fir.standard-libm/v2 and retire the heap-aware fir.standard-math/v1 provider. W6 may separately state/refine the stable six-signature external-runtime contract; provider-specific transcendental approximation is intentionally not presented as a core-Wasm theorem
```
