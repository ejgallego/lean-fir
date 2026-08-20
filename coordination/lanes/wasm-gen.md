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
base: 1f4509fa on main
functional-head: db6d46a7, return immediate Nat-to-USize conversions directly while retaining the checked arbitrary-precision fallback
contract-base: 1f4509fa. No Lean semantic, semantic Wasm ABI, resident-helper signature, symbolic-module, source entry, adapter API, ownership contract, or arena contract changed. The implementation uses the existing i64ExtendI32U instruction with semantic result kind .usize; no new instruction or same-width cast was introduced
clean-at-update: true
slice: USize.ofNat and USize.ofNatLT now dispatch canonical tagged Nat inputs to a direct unsigned i32-to-i64 extension and return a semantic .usize value without scratch-memory stores or loads. Promoted and arbitrary-limb values retain the validator-first modulo-2^64 calculation and scratch-memory semantic retyping, so malformed-input failure behavior and the full natural-number semantics are unchanged. The order-balanced lean-zip experiment lowers median wall time from 143.16 ms to 140.26 ms, about 2.03%, while two independent CPU profiles reduce fir_ext_USize_ofNat self samples from 735 to 132/128, about 82%. fir_dec_once remains independent and is deliberately parked
files: Fir/Wasm/Emit/ResidentUSize.lean; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. The package has zero function and memory imports, module-owned memory, and the existing five function exports plus memory. Complete Wasm remains 936202 bytes and the final function-index digest remains 08a0a777bc116ab685d9c6c221a8efa708c38440d6ade06ee46d3117afe38d7e. Reviewed artifact-only ratchets are frontier bytes 1619585 to 1619583 and sidecar digest aa3d60d8910e65f62d2bc1726a12b64cf60a4c5b1ae9cdf62ac49437d91d0ed5
artifacts: clean FIR producer 05dc1f0c41e131af63e350571a3a55f4915c8bec, lean-zip source 273d0d6cd9cab77c7f3489b0b0b1f6e543315d21, and zipCommon 4425bab1f9522307d77e8d485bc536149ba31c36. Immutable local preview .deps/evidence/lean-zip-numeric/usize-direct-clean-package has package ID 05dc1f0c41e1-273d0d6cd9ca-aef61428f530ebfb13b2. Its 936202-byte Wasm SHA-256 is 95a575a3ef7928b406d02a167daffee0362728a8346fcc3b1109f4e55f509dc4; its 999568-byte sidecar SHA-256 is aa3d60d8910e65f62d2bc1726a12b64cf60a4c5b1ae9cdf62ac49437d91d0ed5
checks: All accepted profiles, source views, and packages are persistent under the W7 worktree; active commands fixed TMPDIR to .deps/tmp. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentUSize build and real-Wasm fixed-width fixture PASS for boundaries, ofNat/ofNatLT, promoted one-limb and arbitrary-limb modulo semantics. Order-balanced eight-process baseline/candidate campaign PASS with median-of-medians 143.16195775 to 140.25860675 ms, MAD 0.457906 to 0.724261 ms, identical output SHA-256 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751, and flat 9237304-byte frontier. Clean profile SHA-256 values are baseline 6297e27581b9eaf851a5d0d4869e036a831e6df0af19054276303a2cca22fd33 and candidates 8a0629f5e04a4ab4d2292e9d7a3f3f3889e046928c80b32d722868df6b01fe60 / 651c1e51ef22d5b2a30f0964fcd9986eef02911f5da42e8e7da5792ef1575291. Deterministic clean package generation, exact sidecar verification, five inputs x levels 1--10 native/Wasm byte comparison, independent inflate, zero imports, rewind, and flat warm frontier PASS. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 190 active bug cards. The W7-only make talos-check correctly identified the stale W6 USize body theorem; W6 successor a85a5511 adapts both plain and proof-bearing helpers and passes make talos-check with 3165 jobs. The complete W7 artifact gate passed all 44 concrete artifacts and all 15 source probes before that expected proof dependency was linked
bug-cards: none
blockers: none. W6 completion W6-W7-20260820-008 supplies the green proof successor; integration must preserve W7-before-W6 commit order
handoff: Integration resolves the containing clean branch head after this tracked status commit, has W6 rebase its completed proof stack onto that head, validates the combined candidate, and may then fast-forward main. Functional head db6d46a7 is based directly on 1f4509fa. No W6-owned file or shared signature changed, and no canonical-pointer advance or external package publication is authorized
follow-up: integrate the direct USize generation/proof stack. The next profile-selected candidates are USize.toNat and remaining Nat decision/arithmetic calls; ownership-heavy fir_dec_once remains parked until a separate upstream-faithful ownership design is justified
```
