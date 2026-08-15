# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: ba6b1c31 on main
functional-head: 0ecf86c7
contract-base: ba6b1c31; consume the landed resident Array, immediate-Nat, complete scalar Wasm, and direct fixed-width/USize helper surfaces without changing their signatures or shared ABI
clean-at-update: true
slice: W7-W6-20260814-007/008 proof foundation is green but the requests remain active. The shared odd-word dispatcher selects exactly two canonical immediate Nat representations, shift-right decodes their exact payloads, and the complementary branch heap-classifies at least one operand. Nat.add reuses canonical natural allocation, including promoted persistent sums. Nat.mod has an exact concrete immediate-branch model and refinement theorem: divisor zero returns the original left word; a nonzero remainder is below the immediate range, so canonical construction leaves memory and the refinement witness exactly unchanged. These theorems do not yet establish that the emitted W7 helper instruction bodies implement the contracts, nor that replacing the concrete-host external with the resident helper preserves the compiler simulation. The checked arbitrary-precision fallback is unchanged.
files: Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean; Fir/Wasm/Concrete.lean; coordination/lanes/wasm-proof.md
contracts: none. No helper signature, ABI, concrete layout, ownership rule, semantic relation, or W7-owned source changed.
checks: Lean Beam update/sync/save pass for Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean with zero errors or warnings; lake build Fir.Wasm.Concrete.NaturalDispatchCorrectness Fir.Wasm.Concrete pass (62 jobs); git diff --check pass; make check pass (163 scalar Wasm exports, 125 unit tests, 704 source cases across native/LCNF/V8 with 2,112/2,112 comparisons equal, 713-case aggregate coverage, zero findings, 188 active bug cards, 25 mailbox tests); make talos-setup pass at Talos 0e05edbc; make talos-check pass (3,149 jobs)
bug-cards: none
blockers: no representational blocker. Closing W7-W6-20260814-007/008 requires a factored generated-instruction execution/refinement layer for the actual resident Nat.add and Nat.mod bodies, followed by the resident-helper replacement/linking theorem. The separate unchecked typed Array admission gap remains recorded in W7-W6-20260814-004 and does not affect the Nat foundation.
handoff: Not ready for integration as contract-proved. Functional head 0ecf86c7 is a green proof-foundation checkpoint rebased on ba6b1c31.
next: Factor the common scalar/local/control/call primitive proofs used by resident helpers; connect the actual emitted Nat.add and Nat.mod bodies to these contracts; then prove the resident replacement boundary and close W7-W6-20260814-007/008. Coordinate the Array compiler-admission premise separately through the integration-owned shared contract.
```
