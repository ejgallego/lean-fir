# wasm-gen lane

The generation roadmap lives in `Fir/Wasm/Emit/ROADMAP.md`; accepted history
remains on `coordination/BOARD.md`. This is the current clean W7-1 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: d5e0b5caa087954cdd094df3bfbd8408826db8c0
functional-head: 7e1ee053b315aa35803ad015acf7d0839adb550a
contract-base: d5e0b5caa087954cdd094df3bfbd8408826db8c0
clean-at-update: true
slice: CG-01 production capture extraction. Fir.Compiler.LCNF owns the reusable artifact, capture and formatting implementation. Validation schemas/invocations move above Source into Fir.Validation.WasmSource; coverage/execution stay in validation. Legacy capture names remain aliases. No source-unit, capture-policy, runtime, lowering, or artifact behavior changes.
files: Fir/Compiler/{LCNF.lean,README.md}; Fir/Validation/{LCNF.lean,WasmSource.lean}; Fir/Wasm/Emit/{Source.lean,Command.lean,SourceExamples.lean,SourceDependencyExamples.lean,ROADMAP.md}; FirValidationWasm.lean; this status
contracts: none; root's narrow module/importer extraction lease is recorded in the board at base d5e0b5ca. No W6 or resident-helper source is edited.
checks: git diff --check passes. Lean Beam accepts Compiler.LCNF, refreshed Source, SourceDependencyExamples and WasmSource with zero blocking diagnostics; stale importer barriers were not treated as green. After stopping Beam and a local Lake clean, the final focused lake build passes all 67 jobs. make check passes 730 unique cases / 2172 equal comparisons and 38 mailbox tests. make talos-setup passes; make talos-check passes 3201 combined and 3162 focused jobs plus forced 24-endpoint audit, receipt 6dcf0bae76f2bb1265a5ebafa3832bdec75edc9383b294786af4aa87a72ff30b. bash integration/talos/artifact/check.sh passes, including paired deterministic emissions, Node checks and immutable package checksums. No browser campaign was requested or run. All 239 existing Wasm/LCNF output files compare unchanged against the pre-refactor snapshot. Regenerated prettyM Wasm and LCNF exactly match the previously accepted package. A mechanical source check confirms unchanged capture/formatting and moved invocation bodies.
bug-cards: none; no semantic discrepancy
blockers: none
handoff: Clean output-neutral CG-01 slice ready for root fast-forward after the board acceptance. No remote push or external consumer-pointer update requested.
next: Keep CG-02 provider consolidation separate. The next generated-code slice is CG-05A scratch-free closure allocator result transport, then CG-05B selective initialization, with poisoned recycled-memory tests and W6 coordination before helper acceptance.
```

Production Source's FIR dependency graph falls from 21 modules to 16,
including Source itself: Checkpoint, Pipeline, Interpreter, Validation.Corpus,
Validation.LCNF and Validation.Protocol leave; Compiler.LCNF is added. This
is measured dependency reduction, not a build-time or runtime speedup claim.

Immutable local acceptance package:
`integration/talos/artifact/_build/prettyM-current-releases/7e1ee053b315-b1090a3bad749828`.
The worktree-local `prettyM-current` pointer resolves there. Wasm is 87,840
bytes, SHA-256 `ffc980d8981a4bea7f5455426728653254c131e1d7ca612df6d371eb65332d09`;
LCNF SHA-256 `712521f31f7516542154b4c4da5973a246d2e4f3da6acdb4f0b9563b0e2b2736`.
Gate logs and the comparison snapshot are under `.deps/cg01-*`.
