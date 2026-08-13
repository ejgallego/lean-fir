# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 515bf401 on main
functional-head: cb423308
contract-base: 71471a5d; accepted generic `HeapObject.array elements capacity` ownership contract, with only the live prefix owned and spare capacity nonsemantic
clean-at-update: true
slice: The generic Array stack is linked/accepted on main. W6 relates the resident ARRY header, logical live prefix, physical capacity, and tobject slots to semantic Arrays; proves allocation layout and whole-heap allocation; proves borrowed reads, raw replacement, swap, logical-size transitions, unique in-place push/pop, recursive release and recursive release faults; and closes reset/reuse plus scalar/constructor exhaustiveness. Push initializes the spare slot before making it live. Pop shrinks the owned prefix before recursively releasing the removed child. Whole-heap theorems preserve non-target allocations, mapped header capacity, witnesses, and the concrete heap frontier.
files: Fir/Wasm/Concrete/; Fir/Wasm/Concrete.lean; integration/talos/FirTalos/; coordination/lanes/wasm-proof.md
contracts: Generic Array semantics and all current proof/runtime/generation consumers are released on main at 515bf401. The independently landed active-data-segment contract c8770e42 changes no current W6 theorem; W6 will add an initialization/refinement theorem when a nonempty data-segment module enters its proof surface.
checks: Lean Beam zero diagnostics for the edited pass and recursive-fault proofs; git diff --check PASS; make check PASS with 125 harness tests, 701 source cases, 9 direct-machine cases, 710 unique cases, and 2112/2112 comparisons equal; make talos-setup PASS; make talos-check PASS (3147 jobs); deterministic artifact/check.sh PASS with 701 validation cases and 44/44 concrete artifacts
bug-cards: none
blockers: none
handoff: Integration accepted the complete Array contract stack at main 515bf401. The lane is clean and rebased for continuation.
next: Prove shared/persistent Array push/pop allocation-and-copy refinement, beginning with the concrete copy/allocation frame and preserving the live-prefix ownership invariant. Coordinate only if the stable resident helper signature or shared semantic contract must change.
```
