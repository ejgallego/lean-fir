# lean-zip-perf lane

This is the narrowly scoped successor to the W7-2 optimization role. It owns
one lean-zip performance experiment at a time; `wasm-gen` remains the stable
generation and integration owner.

```text
lane: lean-zip-perf
owner: lean-zip-perf
branch: perf/lean-zip-loop
worktree: .worktrees/lean-zip-perf
state: ready
base: d199458796a72b015b2e44a98ce7d628c95bf936, clean local main including the accepted ElimDead Array proof recovery
functional-head: 499d41a00c4e237f72fa5b8e5577aa1003550f71
contract-base: d199458796a72b015b2e44a98ce7d628c95bf936; no shared semantic, ABI, layout, ownership, helper-signature, proof, or source-entry contract change
clean-at-update: true
slice: Replaced the generic fixed-width i32 result scratch-memory retype with a typed extend/wrap bridge. The i64 path is unchanged. Structural guards require all resident i32 result wrappers to stay memory-free and retain the typed bridge, while representative i64 wrappers retain their existing memory operations
files: Fir/Wasm/Emit/ResidentFixedWidth.lean; integration/lean-zip/README.md; integration/lean-zip/package-raw.mjs; integration/lean-zip/raw-closure-contract.json; coordination/lanes/lean-zip-perf.md
contracts: No shared contract changed. The fixed-width resident helper declarations, signatures, and observable semantics are unchanged; only the private executable implementation and lean-zip release ratchets changed
performance: Thirty-two diagnostics-off, order-balanced fresh-process pairs on the exact 256 KiB level-6 workload move median exported-entry time from 41.50ms to 39.07ms, with a -2.15ms paired median (-5.3%) and 21/32 wins. Both order halves improve. The complete zero-import module shrinks 414753 to 367176 bytes (-11.5%); lzMatchP shrinks 36982 to 31706 bytes and 1056 to 272 memory operations. Exact output digest and the flat 9237304-byte frontier are unchanged
checks: Lean Beam update/sync/save passed with zero diagnostics and source hash 5997959cfc20f997. The 54-job ResidentLinker dependency cone passed. The immutable preview package passed deterministic double generation, native/Wasm raw dispatcher levels 1-10, complete-runtime adapter, scratch rewind, sidecar, checksum, and smoke checks. make check passed: 726 unique cases, 2160/2160 comparisons equal across native/LCNF/V8, zero findings, 9077 machine steps, 196 active bug cards, and 25 mailbox tests. git diff --check passed
bug-cards: none
blockers: none
handoff: Functional head 499d41a0 is ready for wasm-gen review and integration. Preview package .deps/perf/fixed-width-i32-candidate-package has package ID d199458796a7-273d0d6cd9ca-bc63347c1b634a7d0530 and complete Wasm SHA-256 63426392249011cf27cf2fc56fcb1caeb6ffd7f84101da24d2f8fbfe7e0efd59. Publication remains local-only
next: wasm-gen reruns the full W7 make talos-setup, make talos-check, and canonical lean-zip artifact gate, then lands or returns the candidate. After integration, rebase this lane before selecting another bounded hotspot
```
