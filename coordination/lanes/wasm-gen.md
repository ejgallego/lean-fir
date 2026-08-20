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
base: 181b1097 on main
functional-head: 9dd5ea7a, dispatch arbitrary-precision Nat equality and order directly for two canonical immediate words
contract-base: 181b1097. No Lean semantic, semantic Wasm ABI, resident-helper signature, symbolic-module, source entry, adapter API, ownership contract, or arena contract changed. W6 proof adaptation is requested as W7-W6-20260820-001
clean-at-update: true
slice: fir_big_ext_Nat_decEq, fir_big_ext_Nat_decLt, and fir_big_ext_Nat_decLe now branch on the existing reusable both-immediate representation predicate. The immediate branch compares the tagged words directly; unsigned tagged-word order equals Nat payload order. Promoted, heap-backed, persistent, mixed-representation, and arbitrary-limb inputs retain the previous validation/count/magnitude fallback. Exact release profiles lower lean-zip 256-KiB seeded-random level-6 medians from 391.71/387.83 ms to 270.49/284.03 ms. Compare samples fall 89.8%, magnitude low/high 62.8%/76.2%, and natural validation 75.7%, with identical compressed bytes and frontier
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; integration/talos/artifact/resident-big-numeric-client.mjs; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. The package has zero function and memory imports, module-owned memory, and the existing five function exports plus memory. Reviewed artifact-only ratchets are frontier bytes 1619165 to 1619270, complete bytes 936001 to 936061, final function-index digest 44d1a5bd49aa22a04160b652104c13a2cedd8db85f2efd807ae4124e9eb3318a, and sidecar digest 5b4b3cf83f9bdd60894dbf7cedf00353735374db78d86d934d47442ece003093
artifacts: clean FIR producer 9dd5ea7a9960055ebfd6c26a4e1b1a9799bce193, lean-zip source 273d0d6cd9cab77c7f3489b0b0b1f6e543315d21, and zipCommon 4425bab1f9522307d77e8d485bc536149ba31c36. Immutable local preview .deps/evidence/lean-zip-numeric/clean-package has package ID 9dd5ea7a9960-273d0d6cd9ca-e2c1415d3adddc83beda. Its 936061-byte Wasm SHA-256 is fafdd9a9a8fdb7f42983596b49eccb9554f9deca05045fb0f99cd4103e4bbb21; its 999548-byte sidecar SHA-256 is 5b4b3cf83f9bdd60894dbf7cedf00353735374db78d86d934d47442ece003093
checks: All accepted scratch, profile, source-view, and package paths are persistent under the W7 worktree; active commands fixed TMPDIR to .deps/tmp. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentBigNumeric build and real-Wasm fixture PASS, including immediate boundaries, promoted/heap/persistent cases, mixed representations, and 8192-limb stack-safe walkers. Deterministic package generation, exact sidecar verification, five inputs x levels 1--10 native/Wasm byte comparison, independent inflate, zero imports, rewind, and flat warm frontier PASS. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 189 active bug cards. make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including all 44 concrete artifacts and all 15 source probes
bug-cards: none; the profile exposed avoidable generic dispatch overhead, not a semantic discrepancy
blockers: none. The lean-zip lane retains the independent Chrome and order-balanced FIR-native/FIR-C acceptance campaign
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 9dd5ea7a is based directly on 181b1097. No W6-owned file or shared signature changed, and no push, canonical-pointer advance, or external package publication is authorized
follow-up: W6 proves the stable helper bodies under W7-W6-20260820-001 while lean-zip/root reviews the local clean package from ROOT-FIR-20260820-001. The next profile-selected generation candidates are USize.ofNat and immediate Nat.mul; neither should begin until this slice lands and the acceptance campaign confirms the gain
```
