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
base: 345a0cb3 on clean local main, including W6's accepted resident Nat limb invariant checkpoint
functional-head: f74709fc, publish exact prettyM final-function indices; generic exact emitter-final capture f661a080; opt-in real-package instruction-origin regeneration f701b8bf
contract-base: 345a0cb3. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, natural arithmetic implementation, or local array contract changed. The new inventory is observation-only and binds the emitter's final function order to the exact unchanged release bytes
clean-at-update: true
slice: Added a generic read-only direct function-index capture for final emitter modules. Pinned Binaryen supplies only the call graph and its default final map; the release module is never rewritten, and the tool rejects order/count drift. The prettyM emitter now writes an opt-in exact function inventory, the artifact gate reproduces it and its 393-function sidecar twice, and immutable prettyM packages checksum and smoke-test the sidecar without making it a browser payload. The parked real-package instruction-origin slice is also integrated as opt-in diagnostic evidence and leaves ordinary package bytes unchanged
files: tooling/wasm/function-index.mjs; tooling/wasm/function-index.test.mjs; Fir/Wasm/Emit/Source.lean; FirPrettyMArtifactMain.lean; Fir/Wasm/Emit/INSTRUCTION_PROVENANCE.md; integration/talos/artifact/check-instruction-origins.mjs; integration/talos/artifact/check.sh; integration/talos/artifact/package-pretty-format.sh; integration/talos/artifact/prettyM-package/README.md; integration/talos/artifact/prettyM-package/smoke.mjs; coordination/lanes/wasm-gen.md
contracts: Canonical prettyM release is integration/talos/artifact/_build/prettyM-current-releases/f74709fc47a4-d8da040f4d1369c9, selected by prettyM-current. Wasm remains 120739 bytes, zero-import and module-memory-owned, SHA-256 06cb977fa8a0815c2bfd1762ff08031daa1f723221dd6054b39f32f823210119. Its 164320-byte fir.wasm.function-index/v1 sidecar has SHA-256 569c327ae3cb986aa67ba0ac5b7f564798cfbd4b753388b26bda8bcab3b96b04 and exact-emitter-final-order/v1 identity. SHA256SUMS is d8da040f4d1369c93776737279108cfca7635effb5f87356af1273292a441931. Lean-zip remains the accepted 936072-byte release e20df1c562cf8a3acaf80ac2d0868660aa3afa2a7e8ad6a98a371687c8b1659d with sidecar 22b304489260ccf819de7aef50359275943a69c3ddf11777f293e3153ca660cb and flat frontier 9237304
checks: TMPDIR, TMP, and TEMP stayed worktree-local. Lean Beam sync PASS with zero diagnostics for Source.lean and FirPrettyMArtifactMain.lean; focused fir-prettyM-artifact build PASS 112 jobs. Generic function-index external gate PASS 5/5. git diff --check PASS. make check PASS with 713 unique cases and 2121/2121 equal comparisons. make talos-setup PASS at pinned Talos 0e05edbc; make talos-check PASS all 3167 jobs. Complete W7 artifact gate PASS: two identical 120739-byte modules, two identical inventories and sidecars, 393 indexed functions, 35615 checked instruction origins, immutable package checksum/smoke, 44 concrete artifacts, 15 source probes, and the 704-case V8 triangle. Fresh exact-release lean-zip profile: four bound runs, zero unresolved Wasm samples, identical output 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751 and frontier 9237304; median Wasm-self shares lz77LazyMergedLoop 25.59%, fir_dec_once 14.24%, fir_byte_array_validate 5.93%, USize.ofNat 3.67%, Nat.shiftRight 3.60%, big Nat.add 3.47%. Fresh exact-release prettyM profile: four bound runs of 256 pre-encoded executions plus two checked decodes, zero unresolved Wasm samples, identical trace digest 09d0a45f826aff7fdf59dbb31ad0c1c03fe4a0d622d94a5023974a98e6c59b5f, 3070 text characters, 1025 styling events, frontier 124730520; median Wasm-self shares fir_dec_once 9.55%, fir_alloc_ctor_10 8.72%, fir_inc_0 4.23%, main pretty worker 4.13%, fir_getTag 3.97%
bug-cards: none; no semantic discrepancy was observed
blockers: none. W7-W6-20260821-005 remains open for W6's stronger full checked Nat.add loop theorem and is independent of this observation-only W7 slice
handoff: Rebased cleanly onto W6 checkpoint 345a0cb3. Integration may fast-forward main through f701b8bf, f661a080, f74709fc, then this containing status commit. The package pointer is already clean and tested; no consumer API changes are required
next: Begin the thin shared package verifier/descriptor extraction. Keep fir_dec_once as the strongest cross-package performance candidate, but do not mix that experiment into package maturity or W6's current Nat proof thread
```
