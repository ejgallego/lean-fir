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
base: 0e836ad5c4f636f2a2cd2fda41c4472427079bc6, accepted main containing heap-only USize convergence, sampled-profile contract v1, and the integration-lease handoff to fir/root
functional-head: 66c325df2045cab022a8deb671019e2a69ef7cd5
contract-base: 1db0b79d4b1607ee311432a27b5460853300399a; consumes the isolated heap-only USize semantic contract while retaining the existing semantic ABI signature, scalar-box layout, allocator, marker, and ownership contract
clean-at-update: true
slice: Retires the remaining operational Lean 4.32 generation residue. The LLVM selection adapter and generated manifest now identify the same Lean 4.33 SelectionAnimation/v4 layout as the FIR-native adapter, and the lean-zip integration describes its actual Lean 4.33 source boundary. Five inactive 4.32 worktrees and two stale 4.32 Lean Beam caches were retired locally; valuable historical branch and bug-card provenance remains intact. The worktree-local lcnf-c-wasm Lean source/runtime was refreshed from the stale 4.32 checkout to the exact pinned 4.33 commit d8b18978322de05a8f3dba51ef03cf5461676c17.
files: integration/illuminate-player-llvm/enhance-manifest.mjs, integration/illuminate-player-llvm/illuminate-selection-player-emscripten-adapter.mjs, integration/lean-zip/README.md, and this lane status
contracts: package metadata correction only. SelectionAnimation/v4 data layout, adapter API, ownership, transport, exports, and runtime behavior are unchanged; the LLVM package now truthfully advertises the already-current Lean 4.33 layout identifier.
checks: git diff --check; integration/illuminate-player-llvm/check.sh passed immutable packaging, checksum verification, Emscripten smoke, and 12-job wire cone; make check passed 730 unique cases, 2172/2172 comparisons, 721-case native/LCNF/V8 triangle, coverage policy, bug-card validation, trusted-source validation, and mailbox tests. Final scans find no v4.32 toolchain pin in any active worktree or W7 source view and no 4.32 reference in current LLVM/lean-zip package sources or generated LLVM package metadata.
evidence: immutable LLVM package integration/illuminate-player-llvm/_build/packages/illuminate-selection-player-a9828b1c6a9e17b81a24215edf0fdda86159bbfe01bc31adc8075691e8859d3f; generated Wasm SHA-256 568a0670611bb40235556adf74fca480367cafc0b8415991180577cfd078b4b2. Retired worktrees were compile-times, integration-closure-ownership, lcnf-research, native-validation, and validation-float-w7-probe; branch refs with unique research history were preserved.
bug-cards: none
blockers: none in the compiler. Shared SOURCE_PACKAGE publication remains intentionally deferred until Illuminate completes the third consumer review; no client has supplied a new unsupported source closure.
handoff: Integrate functional head 66c325df after consuming the containing clean status checkpoint. Integration is owned by fir/root; W7-1 will not land W7-2, tooling, W6, or LCNF checkpoints.
next: After this cleanup lands, stay checkpointed until either Illuminate returns the SOURCE_PACKAGE review or a real source closure exposes a missing generic compiler/runtime capability. Do not preemptively implement fail-closed FloatArray/DataArray/DOM/callback or other unused families, and do not overlap W7-2's Nat.land/USize fact work.
```
