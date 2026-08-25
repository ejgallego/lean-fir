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
base: 62c4ca81471951121fa48de793e7ae85907bfd97
functional-head: f5e29648bae3333c62aa81a1c6613cbb56955f5d
contract-base: a823686b
clean-at-update: true
slice: Remove the trap-backed `instInhabitedOfMonad._redArg` resident fallback. The real Lean declaration is now retained as ordinary source code and compiled through the generic final-LCNF path; the only remaining fail-closed resident fallback is `panicCore`. A production-shaped generic-monad probe executes the actual declaration and returns 42 through native Lean, the FIR LCNF interpreter, and zero-import Wasm.
files: Fir/Wasm/Emit/PrettyFormat.lean; Fir/Wasm/Emit/ResidentFallback.lean; Fir/Wasm/Emit/SourceExamples.lean; integration/talos/artifact/FirWasmSourceExample.lean; integration/talos/artifact/FirWasmPrettyTraceExample.lean; integration/talos/artifact/concrete-corpus.mjs; integration/talos/artifact/check-concrete-source-probes.mjs; integration/talos/artifact/check-resident-pretty-format.mjs; integration/talos/artifact/resident-fallback-client.mjs; integration/talos/artifact/test-concrete-readiness.mjs; integration/talos/artifact/package-pretty-format.sh; integration/talos/artifact/README.md; integration/talos/artifact/prettyM-package/README.md; bugs/FIR-BUG-wasm-none-generic-inhabited-fallback-trap.md; bugs/FIR-BUG-impure-none-uint64-box-tagged.md; coordination/lanes/wasm-gen.md
contracts: Consumes the released dynamic-closure-underapplication admission contract at a823686b. No helper signature consumed by W6, semantic ABI, concrete layout, ownership/reclamation rule, symbolic Wasm instruction surface, or source semantics changed. The resident import frontier loses the inhabited trap declaration and body; generated source code gains the real declaration. The independently discovered UInt64 boxing discrepancy is recorded but not worked around here.
checks: Lean Beam sync/save passed SourceExamples.lean and ResidentFallback.lean with zero diagnostics (source hashes 64ecf20a60092748 and 3e3aecfe62e5dfbf); the artifact-only source example synchronized with zero diagnostics. The exact probe returned 42 in native Lean, FIR LCNF, and external-engine zero-import Wasm. git diff --check passed. make check passed with 717 native/LCNF cases, 9 direct-machine cases, 717 V8 cases, and all 2160 comparisons green. make talos-check passed all 3172 jobs. bash integration/talos/artifact/check.sh passed deterministic generation, packaging, Node/Chrome ownership and stack-safety checks, the 44-case concrete readiness audit, and all 16 source probes. The exhaustive resident pretty-format ratchet passed from 453 imports to zero, with only the fail-closed panic fallback retained.
bug-cards: FIR-BUG-wasm-none-generic-inhabited-fallback-trap fixed; FIR-BUG-impure-none-uint64-box-tagged confirmed and queued for a separate shared-layout repair.
blockers: none for this slice.
handoff: Fast-forward this clean lane-status commit, whose functional head is f5e29648bae3333c62aa81a1c6613cbb56955f5d, onto main. The canonical prettyM package is integration/talos/artifact/_build/prettyM-current and the immutable release is integration/talos/artifact/_build/prettyM-current-releases/d18badf63dba-a00c95fabe894096. Plain and styled Wasm remain module-memory-owned and zero-import at 82104 and 85518 bytes respectively.
next: Coordinate FIR-BUG-impure-none-uint64-box-tagged through integration, W6, and W7 before changing the shared scalar-box representation. Continue the broader runtime audit independently.
```
