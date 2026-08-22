# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 90b52741, tracked prior W6 installed-step handoff over the accepted exact prettyM instruction-profile stack
functional-head: 5ac4f417
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved the complete installed sumCarryFrom scan. A generic Talos structured-loop theorem separates an abstract index/carry invariant from the decreasing count-index variant, proves non-wrapping wasm32 increment below count, and permits the adapter's unreachable terminal suffix. Its concrete limb-list instance uses unprocessed list suffixes to return exactly the final carry of addLimbWords from index zero. Factored adapter lemmas identify W7's exact symbolic guard, private four-accessor step, increment, and back-edge with that loop; successful function adaptation therefore installs precisely the proved program. The final body-WP theorem applies directly to the actual adapted target function under pointwise read-only magnitude-accessor results. W6 PLAN records the reusable invariant/variant separation and the next writeSumFrom memory-frame boundary.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. Proof-side helper names are explicitly unstable and may be reshaped for a cleaner induction boundary.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the final gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful installed whole-scan checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head 5ac4f417 and this containing status commit. W7 may rely on exact whole-scan carry correctness without changing the resident helper body, magnitude-accessor behavior, or signature.
next: Instantiate the factored arithmetic step in writeSumFrom's shifted local layout, prove the exact low/high stores with a growing payload-byte frame, and lift that installed loop with the same semantic carry invariant. Then connect the completed payload and carry branch to allocateNatural of the operand sum and the existing checked typed-return paths.
```
