# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c4c9fb4c on main
functional-head: 33d2b3f7
contract-base: c12dba9c; consume the landed W7 immediate Nat-to-USize dispatcher and generic BigNumeric limb accessors without changing helper signatures, semantic ABI, concrete layout, ownership, or failure contracts
clean-at-update: true
slice: Stacked on the preceding ready Nat-decision proof, ConcreteResidentUSize proves the exact adaptation and actual-function execution of both USize.ofNat and USize.ofNatLT. Canonical tagged inputs take the direct decoder, return the exact UInt64 payload, and account for ofNatLT's erased argument. Non-immediate promoted or heap inputs take the validation-first checked branch; CheckedNaturalCalls packages unchanged-store validateNatural/naturalHigh/naturalLow calls and an exact UInt64.ofNat natural modulo-2^64 equation, and the actual adapted outer helpers terminate with that result under this stable contract. Invalid representations retain the original validator-first failure path because no termination theorem is claimed without the contract. New generic 64-bit scratch lemmas prove read-after-write and full byte-for-byte memory restoration. Both paths preserve signatures, stores, and caller tails and conclude with the exact W6 USize ValueRel.
files: integration/talos/FirTalos/ConcreteResidentMemory.lean; integration/talos/FirTalos/ConcreteResidentUSize.lean; integration/talos/W6-COVERAGE.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md; plus the preceding stacked Nat-decision files already reported at e077b34a
contracts: none shared changed. CheckedNaturalCalls is a new proof-side implementation boundary, not a weakened runtime or semantic contract. No W7 generator/artifact file, helper signature, semantic ABI, concrete layout, ownership rule, source semantics, compiler relation, failure behavior, or shared integration-owned source file changed.
checks: After rebasing the full W6 stack on main c4c9fb4c, Lean Beam refresh/sync/save passes for ConcreteResidentMemory and ConcreteResidentUSize with zero module errors or warnings; lake build FirTalos.ConcreteResidentUSize passes (3,080 jobs); git diff --check passes; make check passes (163 scalar Wasm exports, 125 unit tests, 704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713-case aggregate coverage, zero findings, 190 active bug cards, 25 mailbox tests); make talos-setup passes at Talos 0e05edbc; make talos-check passes (3,162 jobs)
bug-cards: none new
blockers: none for this handoff. The new proof-owned module is intentionally not added to integration/talos/FirTalos.lean because that umbrella is integration-owned; integration should add imports for ConcreteResidentNatDecision and ConcreteResidentUSize while consuming the stacked candidate. The installed BigNumeric validate/accessor bodies still need their implementation-to-CheckedNaturalCalls theorem, and both helper families still need operation-specific StateRelated replacement instances; these are explicit follow-ups, not defects in the proved outer helpers.
handoff: The green stacked W6 proof candidate at functional head 33d2b3f7 was rebased on main c4c9fb4c and fast-forwarded to local main through tracked status 3ab5b747 by the active integration owner. This mailbox correction records the final rebased hashes. Integration still owns the umbrella imports for `FirTalos.ConcreteResidentNatDecision` and `FirTalos.ConcreteResidentUSize` plus the BOARD acceptance update. The USize slice proves the actual immediate helper completely and the actual checked outer helper against the stable concrete numeric call boundary, including exact modulo-2^64 semantics and scratch restoration.
next: Prove the installed validateNatural/naturalHigh/naturalLow helpers satisfy CheckedNaturalCalls for promoted and arbitrary-limb NaturalObjectRel inputs, then instantiate the USize and Nat-decision StateRelated resident-replacement theorems. Promoted/heap-backed Nat arithmetic remains parallel W6 work.
```
