# lean-zip-perf lane

This is the narrowly scoped successor to the W7-2 optimization role. It owns
one lean-zip performance experiment at a time; `wasm-gen` remains the stable
generation and integration owner.

```text
lane: lean-zip-perf
owner: lean-zip-perf
branch: perf/lean-zip-loop-s4
worktree: .worktrees/lean-zip-perf
state: ready
base: 631fe8e1e3cbb8e2b4893db24231011b5ac78091, accepted main including upstream Array.set! alignment
functional-head: 2abea9cea4b2925a343b552e356d9edf024d2bac
contract-base: 631fe8e1e3cbb8e2b4893db24231011b5ac78091; no shared semantic, ABI, layout, ownership, helper-signature, proof, or source-entry contract change
clean-at-update: true
slice: Replaced the generic fixed-width i64 result scratch-memory retype with direct UInt64 return and a typed i64/f64 reinterpret bridge for UInt64.toUSize. UInt64.mod retains only its actual raw operand local. Provider-level structural guards require all UInt64-result wrappers to stay memory-free, same-kind UInt64.add to avoid needless reinterpretation, and UInt64.toUSize to retain the typed semantic bridge
files: Fir/Wasm/Emit/ResidentFixedWidth.lean; integration/lean-zip/README.md; integration/lean-zip/level1-closure-contract.json; integration/lean-zip/package-raw.mjs; integration/lean-zip/raw-closure-contract.json; coordination/lanes/lean-zip-perf.md
contracts: No shared contract changed. The fixed-width resident helper declarations, signatures, and observable semantics are unchanged; only the private executable implementation and lean-zip release ratchets changed
performance: Two independent diagnostics-off, order-balanced 32-pair fresh-process campaigns on the exact 256 KiB level-6 workload produce a combined -0.477ms paired median, median ratio 0.987829 (about -1.22%), and 41/64 wins. Both invocation orders improve; three of four 16-pair blocks improve, so the result is recorded as a modest winner with observed host drift. The complete zero-import module shrinks 366796 to 359760 bytes and 501 to 500 functions. chooseSplitsHeuristicPUPacked shrinks 9542 to 6634 bytes, 4699 to 3410 instructions, and 220/220 to 26/26 i64 loads/stores; every removed pair was scratch traffic. Aggregate post profiles retain the same top-five ranking and show no replacement hotspot
checks: Lean Beam update/sync/save passed with zero diagnostics and source hash b68a3a33a72d420c. The 54-job ResidentLinker dependency cone passed. The immutable raw preview passed deterministic double generation, native/Wasm dispatcher levels 1-10, zero-import complete runtime, persistent-cache and scratch-rewind checks, sidecar checks, checksum verification, and smoke. make check passed: 726 unique cases, 2160/2160 comparisons equal across native/LCNF/V8, zero findings, 9077 machine steps, 201 active bug cards, and 26 mailbox tests. make talos-setup and make talos-check passed, including 3172 jobs. The complete Talos artifact gate passed with 717 V8 cases, 654 concrete cases, and the exact 63-case ByteArray blocker inventory. The lean-zip gate passed stored and Level-1 native/Wasm, zero-import, reclaim, checksum, and smoke checks. git diff --check and package script syntax passed
bug-cards: none
blockers: none
handoff: Functional head 2abea9ce is ready for wasm-gen review and integration. Preview package .deps/perf/s4-i64-candidate-package has package ID 631fe8e1e3cb-273d0d6cd9ca-6e3e61d985948a6674f1, complete Wasm SHA-256 5be5d7e64a41b7bf29da2f1c0516b2db32e6c8c2f3689be2ba0c81e4ea8eb, size 359760 bytes, zero imports, and four exports. The deterministic preview at .deps/previews/lean-zip-raw-determinism-631fe8e1e3cb is byte-identical. Publication remains local-only
next: wasm-gen reviews and integrates the green candidate. W6 reviews the unchanged fixed-width implementation against its existing concrete scalar contract. After integration, rebase this lane before selecting another bounded hotspot
```
