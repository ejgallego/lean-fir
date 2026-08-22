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
base: b626350d on clean local main, including the accepted aggregate-v2 exact Wasm caller-attribution tooling
functional-head: 3ee84c76, upstream-shaped ordinary shared-reference decrement
contract-base: b626350d. No Lean semantics, concrete header layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or closure-descriptor contract changed. The stable fir_dec_once implementation shape changed and is queued for independent W6 refinement in W7-W6-20260822-001
clean-at-update: true
slice: fir_dec_once now reads header flags once, probes the terminal header word to preserve the complete 32-byte-header bounds trap, and decrements a live nonpersistent refCount greater than one before decoding cold kind or auxiliary metadata. Persistent and last-reference paths load exactly the metadata they interpret. Generated-shape guards pin the probe and ordinary refcount prefix; the external-engine matrix adds a truncated shared-header trap. The deterministic result is five fewer header reads on the common shared-reference path
files: Fir/Wasm/Emit/ResidentRelease.lean; integration/talos/artifact/resident-release-client.mjs; Fir/Wasm/Emit/ROADMAP.md; integration/lean-zip/README.md; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: prettyM fir_dec_once is 2540 bytes (+17), 19 descriptors, and 8 direct sidecar callers; complete package 120756 bytes / 576a9c5a3bb62fd6764e6c5cd431f074127617b5bddc16045142644f089fb959, sidecar 99f6505bffe1194ce14b3f300da7e59d853585eb417e05c861c0e7a0bdbd96f6, immutable package 3ee84c76a763-7bcb0e4198a649fa. lean-zip fir_dec_once is 19652 bytes (+10), 194 descriptors, and 295 direct callers; complete package 936082 bytes / 8141c21d68f281319dfa33196d2093cbd02e650fb64e7413837ca712916b77a7, sidecar 3a4826ef51324d86a4ea1cc0eb7cffc7a6413fcf255ed4956382f84161e585ac, immutable package 3ee84c76a763-273d0d6cd9ca-2512d78734338383a021. Both remain module-memory-owned and zero-import
performance: Four fresh bound profiles move median normalized fir_dec_once self share from 9.55% to 8.12% in prettyM and 14.24% to 13.59% in lean-zip. Sixteen paired AB/BA rows give median changes of -14.41 ms with 12/16 prettyM pairs improving and -31.90 ms with 9/16 lean-zip pairs improving. Exact trace/compressed digests and frontiers match. Dispersion is high, especially for lean-zip; the accepted claim is the five removed common-path loads, not a precise end-to-end speedup. Raw bound evidence remains ignored under .deps/experiments/dec-once-v1
checks: TMPDIR, TMP, and TEMP stayed worktree-local. Lean Beam update/sync/save PASS with zero diagnostics. Focused ResidentRelease dependency cone and old/new external-engine release matrix PASS, including malformed/truncated headers, persistence, last-reference recursion, and zero imports. git diff --check PASS. make check PASS with 713 unique cases and 2121/2121 equal comparisons. make talos-setup PASS at pinned Talos 0e05edbc; make talos-check PASS all 3167 jobs. Complete W7 artifact gate PASS with deterministic 120756-byte prettyM regeneration, exact 393-function sidecar and 35622 origins, immutable package checksum/smoke, 44 concrete artifacts, 15 source probes, and the 704-case native/LCNF/V8 triangle with 2112/2112 comparisons and zero findings. Clean lean-zip double generation, 5 cases x 10 levels, package smoke, zero imports, and persistent-cache/scratch reclamation PASS
bug-cards: none; no semantic discrepancy was observed
blockers: none for W7 generation integration. W6 refinement is independently queued in W7-W6-20260822-001 after the stable implementation, as required by the concurrent W6/W7 protocol. TOOL-W7-20260822-006 is a diagnostic-only live caller-attribution gate queued after this landing so it does not invalidate package provenance
handoff: Built and rebased on clean local main b626350d. Integration may fast-forward main through functional head 3ee84c76 and this containing status commit. The package pointers above are tested local immutable publications at the functional head; no client API changed
next: Integrate the independent live caller-attribution external gate, consume W6's release refinement when ready, and keep constructor allocation/scratch-retyping experiments separate until the carrier/provenance boundary is stable
```
