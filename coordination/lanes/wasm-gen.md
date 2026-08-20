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
base: 4fea3692 on main
functional-head: 2e9040e0, subtract two tagged Nat inputs directly while preserving the checked arbitrary-precision fallback
contract-base: 4fea3692. No Lean semantic, semantic Wasm ABI, resident-helper signature, symbolic-module, source entry, adapter API, ownership contract, or arena contract changed. The implementation composes the already-linked tagged-Nat dispatcher and FIR's established scratch-memory result retyping convention
clean-at-update: true
slice: Nat.sub dispatches a canonical tagged/tagged pair before the checked arbitrary-precision implementation. Tagged object words preserve unsigned payload order; when left is at least right, subtracting the words and adding one produces the exact canonical tagged difference, while left below right returns tagged zero. The branch allocates nothing. Promoted, mixed, arbitrary-limb, and malformed inputs retain full validation and the structured difference walkers. Against the accepted Nat.mul package, exact lean-zip 256-KiB seeded-random level-6 medians fall from 190.94/187.20 ms to 141.08/142.32 ms, about 26%/24%; Nat.sub combined self samples fall about 75% and magnitude-low samples about 98%, with identical compressed bytes and a flat 9237304-byte frontier
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; integration/talos/artifact/resident-big-numeric-client.mjs; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. The package has zero function and memory imports, module-owned memory, and the existing five function exports plus memory. Reviewed artifact-only ratchets are frontier bytes 1619480 to 1619585, complete bytes 936147 to 936202, final function-index digest 08a0a777bc116ab685d9c6c221a8efa708c38440d6ade06ee46d3117afe38d7e, and sidecar digest a245a858c1297f90e7b584b47489361f5f7aec394c6380ecb7cbc9f24580d5ff
artifacts: clean FIR producer 2e9040e01ee4e54ecad96e89c10239646d43f3a8, lean-zip source 273d0d6cd9cab77c7f3489b0b0b1f6e543315d21, and zipCommon 4425bab1f9522307d77e8d485bc536149ba31c36. Immutable local preview .deps/evidence/lean-zip-numeric/natsub-clean-package has package ID 2e9040e01ee4-273d0d6cd9ca-c3a99b3c7a6a4ef61fe1. Its 936202-byte Wasm SHA-256 is 8aa5a302e328b1b60cc8a5d2f41998e831547d114022336ca3c64cbeb11711e6; its 999568-byte sidecar SHA-256 is a245a858c1297f90e7b584b47489361f5f7aec394c6380ecb7cbc9f24580d5ff
checks: All accepted temporary state, profiles, source views, and packages are persistent under the W7 worktree; active commands fixed TMPDIR to .deps/tmp. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentBigNumeric build and real-Wasm fixture PASS for tagged subtraction boundaries, truncation at zero, no allocation, promoted and arbitrary-limb values, stack-safe walkers, ownership, and malformed operands. Two exact warmed profiles PASS with candidate medians 141.08/142.32 ms, identical output SHA-256 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751, and flat frontier; profile SHA-256 values are ff0f350b08b6d06b3f52791ebb6e755754124f9796a5d72907ab579c932ea754 and 9da245dbbb0c2d946bbbb111b9f7709b9b185927122aed31f13ec6b447955881. Deterministic clean package generation, exact sidecar verification, five inputs x levels 1--10 native/Wasm byte comparison, independent inflate, zero imports, rewind, and flat warm frontier PASS. git diff --check PASS. make check PASS: 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 190 active bug cards. make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including all 44 concrete artifacts and all 15 source probes
bug-cards: none
blockers: none. The lean-zip lane retains the independent Chrome and order-balanced FIR-native/FIR-C acceptance campaign
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 2e9040e0 is based directly on 4fea3692. No W6-owned file or shared signature changed, and no canonical-pointer advance or external package publication is authorized
follow-up: request W6 adaptation for the stable Nat.sub implementation. The next profile-selected queue is headed by USize.ofNat's scalar-result retyping cost, then ownership-heavy fir_dec_once; both require a principled ABI/proof audit rather than another arithmetic special case
```
