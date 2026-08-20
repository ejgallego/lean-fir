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
state: released
base: d6b8d030 on main, including the atomically accepted W7 generation and W6 proof stack
functional-head: c96cf72d, use a scratch-free typed result path for Nat.decEq, Nat.decLt, and Nat.decLe; exact lean-zip ratchet bd5e28ab and W6 proof 18bb219e are accepted through tracked proof handoff 8ae0f5c3
contract-base: 3fdbfc6d. No Lean semantic, concrete layout, helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, or arena contract changed. The existing i64ExtendI32U/i32WrapI64 symbolic instructions witness the raw UInt32 to semantic UInt8 retype
clean-at-update: true
slice: Nat.decEq, Nat.decLt, and Nat.decLe retain their immediate-pair dispatch and checked arbitrary-precision fallback, but return the normalized 0/1 result through i64ExtendI32U .uint64 followed by i32WrapI64 .uint8 instead of borrowing linear-memory scratch. Binaryen erases that typed physical no-op. Exact final bodies contain zero memory operations and shrink from 70/72/72 to 42/44/44 bytes. Seven order-balanced lean-zip rounds improve the median of round medians from 133.467072 ms to 127.5336945 ms, 4.446%; four exact-function profiles reduce combined Nat.decLe/Nat.decLt self-sample share from 7.69--9.23% to 0.67--1.04%
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. It retains zero function and memory imports, module-owned memory, the same exports, zero runtime operations, and a flat 9237304-byte post-call frontier. Complete Wasm is 936140 bytes, frontier Wasm is 1619477 bytes, function-index digest b6296297ba55cae7592654702941e238d9ccf698de4bda3f424f68640fb84223, and the 999568-byte sidecar SHA-256 is 7183dca61b17253ace15c8159d19a614e10a6a982f24df67ddeab7ff6241d9e1
checks: TMPDIR fixed under the W7 worktree. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentBigNumeric build PASS. Standalone resident-big-numeric V8 fixture PASS, including immediate, heap, persistent, malformed-input, and stack-safe cases. Deterministic lean-zip package native/Wasm differential, independent inflate, levels 1--10 adapter, zero-import complete runtime, persistent-cache scratch reclamation, checksums, and smoke PASS twice; exact Wasm SHA-256 d5099c066729568c00e1c91bebb47cc23fb1221d17a1827a8359fa1ceef6a40d. Seven-per-side order-balanced timing PASS with identical output SHA-256 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751; baseline median/MAD 133.467/0.809 ms, candidate 127.534/2.429 ms. Four 500-microsecond V8 profiles contain 5149/5252/5336/5267 Wasm samples. git diff --check PASS. The complete W7 artifact gate PASS includes 44 concrete artifacts and 15 source probes. W6's adapted proof passes Lean Beam with zero diagnostics, its focused 3079-job build, make check, and all 3167 Talos jobs. Integration independently reran make check on main with 713 unique cases and 2121/2121 equal comparisons, followed by make talos-check with all 3167 jobs
bug-cards: none; the Talos failure is the expected cross-lane proof adaptation for an intentional generation body change, recorded in W7-W6-20260820-012 rather than a semantic discrepancy
blockers: none. Operational proof thread W7-W6-20260820-012 is closed with disposition landed
handoff: Integration atomically accepted W7 generation c96cf72d and ratchet bd5e28ab followed by W6 proof 18bb219e and tracked proof handoff 8ae0f5c3. Board commit d6b8d030 records the green landing; no canonical pointer or external package was advanced
next: Start the bounded Nat.add object-result retype experiment after refreshing exact profile/tooling evidence. Preserve all natural-sum, allocation, arbitrary-precision, and malformed-input paths; fir_dec_once remains parked behind the ownership-semantics question
```
