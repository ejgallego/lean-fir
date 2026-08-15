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
base: ba6b1c31 on main
functional-head: dc3d70af, direct core-Wasm Float and conversion resident helpers
contract-base: ba6b1c31, including released WASM-CORE-SCALAR-SURFACE contract 43ab6619. The semantic ABI, concrete Float/Nat layouts, ownership rules, helper signatures, and source semantics are unchanged
clean-at-update: true
slice: The resident linker now internalizes every standard Float/conversion external with an exact core-Wasm meaning: UInt64.toFloat; Float.add/sub/mul/div; Float.neg/beq/decLt/decLe; and Float.abs/sqrt/floor. Existing Float.toUInt64 and UInt64.toNat helpers remain available. Available linking is now source-selective: it emits, rewrites, and exports only helpers actually imported by the captured closure, and requires allocation or Natural construction support only when the selected operation needs it. Float.round deliberately retains its checked floor/ceil synthesis because Lean rounds ties away from zero and preserves signed zero, unlike Wasm f64.nearest ties-to-even
files: Fir/Wasm/Emit/ExternalRuntime.lean; Fir/Wasm/Emit/ResidentFloat.lean; Fir/Wasm/Emit/ROADMAP.md; integration/talos/artifact/FirWasmArtifactMain.lean; integration/talos/artifact/check.sh; integration/talos/artifact/resident-float-client.mjs; integration/talos/artifact/run-resident-float.mjs; coordination/lanes/wasm-gen.md
contracts: no shared contract change. This is a W7 consumer of released symbolic-Wasm contract 43ab6619. Source declarations, ABI kinds, concrete layouts, ownership, module memory, resident-helper names/signatures, and W6 proof obligations are unchanged. The ExternalRuntime inventory now gives canonical disjoint core-scalar and compiled-math partitions of the existing opaque capture frontier
artifacts: zero-import, module-memory resident Float fixture is 5673 bytes and covers all 15 helpers. It checks exact NaN sign/payload behavior for neg/abs, signed zero, infinities, half-away-from-zero rounding, saturating Float.toUInt64, UInt64.toFloat max rounding, decision-helper scratch restoration, and immediate/heap UInt64.toNat. The complete deterministic prettyM gate remains green; no package is externally published by this slice
external-frontier: Float.ofNat; Float.ofScientific; Float.sin; Float.cos; Float.acos; Float.atan2; Float.cbrt; Float.log2. These require Natural/decimal logic or libm and remain in the checked compiled runtime rather than receiving approximations
performance: no headline benchmark was run. Direct helpers remove the compiled-math dependency for source closures using only exact core operations; runtime speed is deliberately not claimed without an order-balanced measurement
checks: Lean Beam update/sync/save PASS with zero diagnostics for ExternalRuntime, ResidentFloat, and the nested FirWasmArtifactMain module after one recovered Beam daemon disconnect. Focused Lake builds for Fir.Wasm.Emit.ResidentLinker and fir-wasm-artifact PASS. Focused zero-import resident Float Node fixture PASS at 5673 bytes. git diff --check PASS. make check PASS 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 188 active bug cards, and 25 mailbox tests. make talos-setup PASS at Talos 0e05edbc and final make talos-check PASS 3148 jobs. Final bash integration/talos/artifact/check.sh PASS deterministic resident and prettyM artifacts, exact resident Float size 5673, 642/704 concrete products with the existing 62 initial-ByteArray blockers, 44/44 readiness artifacts, and all executable concrete cases
bug-cards: none
blockers: none
handoff: integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head dc3d70af is based directly on ba6b1c31. No W6-owned file or shared contract changed, and no external artifact publication is authorized
follow-up: The focused Illuminate regeneration reaches its stale complete-size ratchet because its canonical package predates several already-landed Nat/scalar changes; this slice does not alter or publish Illuminate. The next independent generation question is whether Float.ofNat/ofScientific can reuse one faithful generic Natural-to-binary64 implementation, leaving only the six libm operations in the compiled frontier
```
