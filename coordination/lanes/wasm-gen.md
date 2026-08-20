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
state: waiting
base: 7d298c59 on main
functional-head: fd00971a, use a scratch-free typed result path for Nat.decEq, Nat.decLt, and Nat.decLe and ratchet the exact lean-zip release
contract-base: 7d298c59. No Lean semantic, concrete layout, helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, or arena contract changed. The existing i64ExtendI32U/i32WrapI64 symbolic instructions witness the raw UInt32 to semantic UInt8 retype
clean-at-update: true
slice: Nat.decEq, Nat.decLt, and Nat.decLe retain their immediate-pair dispatch and checked arbitrary-precision fallback, but return the normalized 0/1 result through i64ExtendI32U .uint64 followed by i32WrapI64 .uint8 instead of borrowing linear-memory scratch. Binaryen erases that typed physical no-op. Exact final bodies contain zero memory operations and shrink from 70/72/72 to 42/44/44 bytes. Seven order-balanced lean-zip rounds improve the median of round medians from 133.467072 ms to 127.5336945 ms, 4.446%; four exact-function profiles reduce combined Nat.decLe/Nat.decLt self-sample share from 7.69--9.23% to 0.67--1.04%
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. It retains zero function and memory imports, module-owned memory, the same exports, zero runtime operations, and a flat 9237304-byte post-call frontier. Complete Wasm is 936140 bytes, frontier Wasm is 1619477 bytes, function-index digest b6296297ba55cae7592654702941e238d9ccf698de4bda3f424f68640fb84223, and the 999568-byte sidecar SHA-256 is 7183dca61b17253ace15c8159d19a614e10a6a982f24df67ddeab7ff6241d9e1
checks: TMPDIR fixed under the W7 worktree. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentBigNumeric build PASS. Standalone resident-big-numeric V8 fixture PASS, including immediate, heap, persistent, malformed-input, and stack-safe cases. Deterministic lean-zip package native/Wasm differential, independent inflate, levels 1--10 adapter, zero-import complete runtime, persistent-cache scratch reclamation, checksums, and smoke PASS twice; exact Wasm SHA-256 d5099c066729568c00e1c91bebb47cc23fb1221d17a1827a8359fa1ceef6a40d. Seven-per-side order-balanced timing PASS with identical output SHA-256 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751; baseline median/MAD 133.467/0.809 ms, candidate 127.534/2.429 ms. Four 500-microsecond V8 profiles contain 5149/5252/5336/5267 Wasm samples. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 191 active bug cards. bash integration/talos/artifact/check.sh PASS, including 44 concrete artifacts and 15 source probes. make talos-check reaches 3163/3167 then fails only in ConcreteResidentNatDecision at its intentionally stale scratch-result program, four-local size, and removed result local
bug-cards: none; the Talos failure is the expected cross-lane proof adaptation for an intentional generation body change, recorded in W7-W6-20260820-012 rather than a semantic discrepancy
blockers: W7-W6-20260820-012 asks W6 to adapt the exact UInt8/no-memory refinement and restore the required complete Talos gate. W7 generation and external-engine evidence are otherwise complete
handoff: none until W6 returns the proof adaptation. Integration should then land W7 functional commits 09cf05f8 and fd00971a first, followed by the W6 proof commit and this tracked W7 status commit after rebase. No canonical-pointer advance, push, or external publication is authorized by this mailbox
next: after the proof stack is accepted, rerun make talos-check, rebase onto current main, resolve the containing clean W7 branch head, and fast-forward main in dependency order. The next profile-selected generic runtime candidate is Nat.add; fir_dec_once remains parked behind the ownership-semantics question
```
