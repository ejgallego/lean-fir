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
state: active
base: d1994587 on clean local main, including S20 ByteArray mutual-tail validation and the ElimDead Array proof recovery
functional-head: 40456cf4, replaying W7-2 functional head 499d41a0; exact consumer-ratchet head 3fb8f4eb and acceptance-harness repairs afe1ba12/a528ac47 are included in the integration stack
contract-base: d1994587. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed
clean-at-update: true
slice: Fixed-width i32 results now preserve their physical lane through the typed i64.extend_i32_u/i32.wrap_i64 bridge rather than scratch-memory address zero. Shape guards cover UInt8/UInt16/UInt32 result families and Boolean/object conversions; the i64 retype path remains unchanged. W7 also repaired two exact artifact ratchets exposed by the combined gate and regenerated all lean-zip consumers
files: Fir/Wasm/Emit/ResidentFixedWidth.lean; integration/lean-zip package contracts, README, and publication; integration/talos/artifact acceptance assertions; W7 bug cards; coordination lane and board records
contracts: Helper signatures, fixed-width masks and validation, i64 result retyping, layouts, ownership, symbolic Wasm surface, and source/pre-optimization inventories are unchanged. The implementation removes only redundant linear-memory reclassification for physical i32 results
performance: On 32 order-balanced 256-KiB level-6 pairs, exported-entry median improves from 41.50ms to 39.07ms; paired median -2.15ms (-5.3%), 21/32 wins. Complete raw Wasm shrinks 414753 to 367176 bytes (-11.5%); lzMatchP shrinks 36982 to 31706 bytes, 18123 to 15869 instructions, and 1056 to 272 memory operations. Exact output and flat 9237304-byte frontier are unchanged
checks: No system /tmp input was used; TMPDIR and source views were worktree-local under .deps. Lean Beam update/sync/save passed with zero diagnostics and source hash 5997959cfc20f997; the 54-job emitter/linker cone, make check at 726 unique cases and 2160/2160 comparisons, and all 3172 Talos jobs pass. The exhaustive prettyM gate passes deterministic generation, Node/package/ownership checks, 717 native/LCNF/V8 cases and 2151/2151 comparisons, and the exact concrete audit at 654 executed plus 63 reviewed ByteArray blockers; its Chrome Worker/Fetch gate passes independently after one transient browser-process abort. The canonical lean-zip gate passes stored and Level-1 native differentials, Node, Chrome, and reclamation; raw generation is byte-deterministic and passes 5 cases across all 10 levels, sidecar/checksum/smoke, zero imports, and persistent-cache/scratch reclamation
packages: styled prettyM 83996 bytes, SHA-256 fc61301d946b1596ad08c9b20d51d2e1f68d60ca0c04b0f9d56e298c2ec6408d; stored lean-zip 12418 bytes, SHA-256 3343c2d1c2656c19ceac6c19a6c7cca0162f96e6d28929999f70dba465e6a8f0; Level-1 193661 bytes, SHA-256 ad76031185f4bbef644066bb944f214500f70a2bcc9bf191bf311504b978339d; raw levels 1-10 367176 bytes, SHA-256 63426392249011cf27cf2fc56fcb1caeb6ffd7f84101da24d2f8fbfe7e0efd59, 501 final functions. All are module-memory and zero-import
bug-cards: FIR-BUG-wasm-none-exhaustive-pretty-closed-dispatch-ratchet and FIR-BUG-wasm-none-mutual-tail-byte-array-blocker-ratchet are fixed; neither exposed a semantic mismatch
blockers: none
handoff: The fixed-width winner is complete and accepted for fast-forward integration from clean W7 head. Original W7-2 branch perf/lean-zip-loop remains untouched at tracked handoff 702e6e4c; W6 remains active independently and must rebase after this shared main advance
next: Complete mailbox thread W72-W7-20260825-002 after main lands. Then review the independent mailbox-protocol request W72-W7-20260825-004; otherwise hold new runtime optimization until the active W6 proof handoff is ready
```
