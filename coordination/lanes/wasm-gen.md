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
base: 56406a31 on clean local main, including the accepted bounded instruction-origin scaling stack
functional-head: d97fb643, closed final-LCNF partial-application target dispatch and complete lean-zip ratchets; generic compiler head e05cbc80
contract-base: 56406a31. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or W6 closure descriptor/dispatch metadata changed. The new optimization is opt-in for package boundaries that do not admit pre-existing Lean closure objects; the generic opaque-closure compiler path is unchanged
clean-at-update: true
slice: Added an explicit closed heap-closure source API. It collects declaration targets from actual final-LCNF pap nodes, removes only the compiler-generated closure matcher branches for other declarations, rebuilds the runtime frontier, rejects any residual non-source target, validates the rewritten module, and preserves W6 closureDispatch/closureDescriptors tables. prettyM and all three lean-zip entries opt in because their transferred data boundaries cannot carry closures. Production package inventories now ratchet exact ordered source-target lists or their hashes
files: Fir/Wasm/Emit/ClosureDispatch.lean; Fir/Wasm/Emit/Source.lean; Fir/Wasm/Emit/SourceExamples.lean; Fir/Wasm/Emit/ResidentPrettyFormat.lean; Fir/Wasm/Emit/ROADMAP.md; integration/lean-zip/LeanZipFir/Compile.lean; integration/lean-zip/Level1ArtifactMain.lean; integration/lean-zip/Emit.lean; EmitStored.lean; EmitRaw.lean; package.mjs; package-raw.mjs; raw-package-smoke.mjs; closure contracts; README; coordination/lanes/wasm-gen.md
contracts: prettyM has 11 source targets, retains 394 matcher candidates, removes 625, and decreases complete Wasm from 120756 to 84161 bytes (30.3%); the styled trace is 88197 bytes, 314 functions, and 25535 origins. lean-zip stored has 0 targets and is 12747 bytes; Level-1 has 15 targets, 472 helpers, 768 pre-optimization functions, and is 179656 bytes versus the observed 331234-byte generic build. Raw has 23 targets, 630 source functions, 831 helpers, 1461 pre-optimization functions, and 508 final functions; complete Wasm decreases from 936082 to 393070 bytes (58.0%) and from 2305 to 508 final functions (78.0%). All complete packages retain module-owned memory and zero imports
performance: This post-lowering slice removes package/link/validation surface, not the all-target lowering cost. Raw runtime execution was not claimed faster. Package timing probes still spend roughly 18--23 seconds in all-target lowering; the coordinated next step is to pass the same finite target set into lowering so removed candidates are never constructed
checks: No system /tmp input was used; current scratch and source views stayed under worktree-local .deps (artifact-cache replay warnings contain historical paths only). Lean Beam refresh/save PASS with zero diagnostics for ClosureDispatch, Source, SourceExamples, and ResidentPrettyFormat; the lean-zip subproject is batch-only and its focused 216-job build PASS. git diff --check and JS syntax PASS. make check PASS with 713 unique cases and 2121/2121 comparisons. make talos-setup PASS at pinned Talos 0e05edbc; make talos-check PASS all 3167 jobs. Complete deterministic W7 artifact script PASS with zero-import 84161-byte prettyM, 88197-byte styled trace, package checksum/smoke, 44 concrete artifacts, 15 source probes, and the 704-case native/LCNF/V8 triangle; standalone Chrome Worker/fetch gate PASS. lean-zip stored/Level-1 full gate PASS native differentials, zero imports, lazy-cache floor, scratch rewind, deterministic package smoke, and Chrome. Raw double generation PASS with five native/Wasm cases across all ten levels, independent inflate, persistent cache/scratch rewind, function sidecar, package smoke, zero imports, and exact deterministic hashes
bug-cards: none; no semantic discrepancy was observed
blockers: none for generation integration. The current post-pass is generation-ready under the closed-boundary premise. W6 should review the next shared move of the finite target set into compileClosureDispatch and the corresponding refinement premise; opaque host closure ingress must continue using the all-target path
handoff: Built and rebased on clean local main 56406a31. Integration may fast-forward main through functional head d97fb643 and this containing status commit. Tested local package pointers are pre-integration dirty-build evidence and must be regenerated from clean main before external publication
next: Land this generation-ready slice; publish a clean-main package refresh; ask W6 to shape the closed-boundary theorem and early-lowering target parameter; then compare lowering timelines without changing the package boundary or runtime semantics
```
