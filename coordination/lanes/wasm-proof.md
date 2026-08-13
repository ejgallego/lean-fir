# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 515bf401 on main
functional-head: 0b3f466c
contract-base: 71471a5d; accepted generic `HeapObject.array elements capacity` ownership contract, with only the live prefix owned and spare capacity nonsemantic
clean-at-update: true
slice: W6 closes shared/persistent resident Array push/pop copy-on-write refinement. A fresh copy/allocation frame extends the witness without changing the source Array. Ordered prefix retain refinement follows semantic retainOwnedValue exactly. The complete shared-push theorem retains the old live prefix, allocates it, transfers the new element without retaining it, publishes the pushed Array, then consumes one source reference. The complete shared-pop theorem retains and publishes exactly elements.pop—including the empty case—then consumes one source reference, so the removed last element receives no retain. Both complete theorems preserve full heap refinement, old allocation extents, closure allocations, fresh-reference refinement, source/fresh address distinction, and exact post-allocation cursor stability.
files: Fir/Wasm/Concrete/; Fir/Wasm/Concrete.lean; integration/talos/FirTalos/; coordination/lanes/wasm-proof.md
contracts: none; consumes the accepted generic Array semantics/layout contract at 71471a5d and changes no shared semantic, resident-helper signature, symbolic-Wasm, compiler, or W7 generation surface
checks: Lean Beam update/sync/save PASS with zero errors for Fir/Wasm/Concrete/ArrayCopyCorrectness.lean; direct lake build Fir.Wasm.Concrete.ArrayCopyCorrectness Fir.Wasm.Concrete PASS (61 jobs); direct Talos lake build Fir.Wasm.Concrete.ArrayCopyCorrectness PASS; git diff --check PASS; make check PASS (125 tests); make talos-setup PASS; make talos-check PASS (3148 jobs)
bug-cards: none
blockers: none
handoff: Ready to fast-forward main from 515bf401 through functional head 0b3f466c and this clean mailbox commit. Commits 54f8acd1, 95a476be, 0f232b6f, and 0b3f466c are the coherent proof stack; earlier branch-only mailbox commits are coordination records only.
next: After acceptance and rebase, connect these complete resident copy-path contracts to the compiler-facing finite-trace current-step admission when emitted resident Array calls enter that structured proof surface. Independently add active-data-segment initialization refinement only when a nonempty segment enters W6's proof model.
```
