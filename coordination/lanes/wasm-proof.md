# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7d298c59 on main; accepted W7 USize.toNat generation and prior W6 Nat mul/sub refinements
functional-head: 3c89859a
contract-base: W7 USize.toNat functional source 124ea621 and tested package 07f73191, integrated in main base 7d298c59
clean-at-update: true
slice: Closed W7-W6-20260820-011 for resident USize.toNat. The proof reconstructs the exact public helper body and proves FIR-to-Talos adaptation. Below 2^31, the actual adapted function returns encodeImmediate payload with unchanged store and caller tail; the arm contains no call, load, store, allocation, or scratch-local write. At and above 2^31, the actual function passes the exact high/low wasm64 decomposition to fir_numeric_make_natural, preserves that constructor's exact result store and physical word, then restores the complete eight-byte scratch lane around the transient 32-bit object write. Explicit theorems cover 0x7fffffff as canonical 0xffffffff and 0x80000000 as the first constructor case with (low, high) = (0x80000000, 0).
files: integration/talos/FirTalos/ConcreteResidentMemory.lean; integration/talos/FirTalos/ConcreteResidentUSize.lean; coordination/lanes/wasm-proof.md
contracts: none changed. The proof consumes the existing semantic ABI, wasm32-lean64 USize width, concrete tagged-Nat layout, W7 toNatFunction body, and resident makeNatural signature. The allocating constructor remains a supplied exact termination/refinement boundary; its store, result, ownership effects, and nontermination/failure behavior are not weakened or duplicated.
checks: Lean Beam update/sync/save passed for ConcreteResidentMemory.lean and ConcreteResidentUSize.lean; the latter finished with zero diagnostics and source hash 7bae13ca6f95d55f. `lake -d integration/talos build FirTalos.ConcreteResidentUSize` passed (3,080 jobs). `git diff --check` passed. `make talos-setup` passed at Talos 0e05edbc. `make check` passed (713 unique cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests). `make talos-check` passed (3,167 jobs).
bug-cards: none
blockers: none
handoff: Integration may validate and fast-forward functional commit 3c89859a plus this containing tracked-mailbox commit over base 7d298c59. No W7 implementation, artifact, fixture, profile, shared contract, root umbrella, BOARD file, or target-width bug card was modified.
next: Factor the resident makeNatural allocating branches into a reusable implementation-to-concrete-runtime theorem, then consume the next W7 proof request from the operational mailbox.
```
