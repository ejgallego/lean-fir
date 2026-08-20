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
base: 5c9449e9 on main
functional-head: 0811a912, multiply two tagged Nat inputs directly with Wasm i64 arithmetic while preserving the generic checked multiplication fallback
contract-base: 5c9449e9. No Lean semantic, semantic Wasm ABI, resident-helper signature, symbolic-module, source entry, adapter API, ownership contract, or arena contract changed. The implementation composes the already-linked tagged-Nat dispatcher, payload decoder, and canonical natural constructor
clean-at-update: true
slice: Nat.mul dispatches a canonical tagged/tagged pair before the checked arbitrary-precision implementation. It widens the two 31-bit payloads, multiplies with Wasm i64.mul, and passes the exact low/high words to the existing canonical natural constructor. Immediate results allocate nothing; larger products promote canonically. Promoted, mixed, arbitrary-limb, and malformed inputs retain the checked path. Against the accepted USize package, exact lean-zip 256-KiB seeded-random level-6 medians fall from 219.84/220.72 ms to 190.94/187.20 ms, about 13%/15%; Nat.mul self samples fall from 901 to 57, about 94%, with identical compressed bytes and a flat 9237304-byte frontier
files: Fir/Wasm/Emit/ResidentNatArithmetic.lean; integration/talos/artifact/resident-nat-arithmetic-client.mjs; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. The package has zero function and memory imports, module-owned memory, and the existing five function exports plus memory. Reviewed artifact-only ratchets are frontier bytes 1619354 to 1619480, complete bytes 936077 to 936147, final function-index digest b604ebe28ad3b01cd919917320853e18ff27b900e3987f9fc6fe4743e0831312, and sidecar digest ca3a93079144b8e4fbff53a0503a6a89b4edd14fa4f20499083cba2ee8be37cf
artifacts: clean FIR producer 0811a9121bcba84c7de412bfc8a2e8eea6b70b1e, lean-zip source 273d0d6cd9cab77c7f3489b0b0b1f6e543315d21, and zipCommon 4425bab1f9522307d77e8d485bc536149ba31c36. Immutable local preview .deps/evidence/lean-zip-numeric/natmul-clean-package has package ID 0811a9121bcb-273d0d6cd9ca-2a356c8efc03281f8e97. Its 936147-byte Wasm SHA-256 is 4bba5f05b5559996624df992592f64ffe9b631e81621c9ffc9afaa9ef461de19; its 999568-byte sidecar SHA-256 is ca3a93079144b8e4fbff53a0503a6a89b4edd14fa4f20499083cba2ee8be37cf
checks: All accepted temporary state, profiles, source views, and packages are persistent under the W7 worktree; active commands fixed TMPDIR to .deps/tmp. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentNatArithmetic build and real-Wasm fixture PASS for allocating and nonallocating tagged products, promoted one- and multi-limb products, ownership, and malformed operands. Two exact warmed profiles PASS with candidate medians 190.94/187.20 ms, identical output SHA-256 859d82686a2b7251db69a5cf63f2f8b2dfb7950938663d155eae66dbb6a6b751, and flat frontier. Deterministic clean package generation, exact sidecar verification, five inputs x levels 1--10 native/Wasm byte comparison, independent inflate, zero imports, rewind, and flat warm frontier PASS. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 190 active bug cards. make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including all 44 concrete artifacts and all 15 source probes
bug-cards: none
blockers: none. The lean-zip lane retains the independent Chrome and order-balanced FIR-native/FIR-C acceptance campaign
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 0811a912 is based directly on 5c9449e9. No W6-owned file or shared signature changed, and no canonical-pointer advance or external package publication is authorized
follow-up: request W6 adaptation for the stable Nat.mul implementation. The next profile-selected queue starts with the remaining USize.ofNat call overhead and immediate Nat.sub; ownership-heavy fir_dec_once requires a separate proof-aware audit
```
