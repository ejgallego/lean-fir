# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 8484c0be on main
functional-head: cb04d7ee (landed on main through f37af09e)
contract-base: 8484c0be; consume the landed resident Array and immediate-Nat helper implementations without changing their signatures or shared ABI
clean-at-update: true
slice: Checkpoint after the W6/W7 bridge intake. W7-W6-20260814-001 is complete with no action: ResidentArrayObjectRel already discharges trusted header elision. W7-W6-20260814-004 is complete with a precise blocking admission gap: the unchecked typed path needs the erased bounds witness and canonical Nat-index representation at the source/compiler boundary. W7-W6-20260814-007/008 are claimed as one dependency-ordered immediate-Nat dispatch/add/remainder refinement milestone.
files: coordination/lanes/wasm-proof.md only; both Array audits were read-only and their conclusions are in the canonical local mailbox
contracts: none planned. The accepted W7 Array and Nat helper implementations retain the existing semantic ABI, concrete layout, ownership model, and helper signatures.
checks: git diff --check pass; make check pass (125 unit tests, 704 source cases across native/LCNF/V8 with 2,112/2,112 comparisons equal, 713-case aggregate coverage, zero findings, 188 active bug cards, 25 mailbox tests); make talos-setup pass at Talos 0e05edbc; make talos-check pass (3,148 jobs); canonical mailbox validation pass (39 threads, 148 messages)
bug-cards: none yet
blockers: Proof acceptance of W7's typed unchecked Array paths needs a source/compiler admission theorem carrying erased bounds and canonical Nat/USize decode facts; the lower checked runtime theorems and fault semantics remain intact. This does not block the independent immediate-Nat milestone.
handoff: none; local-only checkpoint on current main 8484c0be
next: After user checkpoint, prove the shared immediate-Nat representation dispatcher once, reuse it for the Nat.add immediate branch and Nat.mod including divisor zero, preserve the arbitrary-precision fallback contract, and run the focused Lean Beam/dependency-cone gates.
```
