# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1f4509fa on main; proof stack consumes rebased W7 source commit db6d46a7
functional-head: a85a5511
contract-base: db6d46a7; rebased equivalent of requested W7 functional head 970e0087, changing only the immediate USize conversion implementation to return i64ExtendI32U .usize directly
clean-at-update: true
slice: Closed W7-W6-20260820-006. Adapted the exact USize.ofNat/USize.ofNatLT source-to-Talos body theorem and fuel-free termination theorem to W7's direct immediate result. Canonical tagged Nats are decoded by shift-right-one, zero-extended, and returned directly. The immediate theorem now has no positive-memory premise and no local-set witnesses; its exact final-store equality records that memory, allocation state, ownership state, globals, host state, and scratch state are unchanged. Both public signatures remain covered through NatConversionKind/callArguments, including USize.ofNatLT's compiler-generated erased proof argument. The checked promoted/arbitrary-limb arm remains validator-first, composes validateNatural/naturalHigh/naturalLow through CheckedNaturalCalls, recombines the result modulo 2^64, uses the restoring scratch cast, and returns the exact unchanged store.
files: integration/talos/FirTalos/ConcreteResidentUSize.lean; coordination/lanes/wasm-proof.md
contracts: none changed. The proof consumes the existing typed i64ExtendI32U .usize instruction and existing helper signatures, semantic ABI, concrete layout, ownership, validation, and modulo-2^64 contracts. CheckedNaturalCalls is unchanged; its WP lemma is factored over an arbitrary continuation solely because the scratch cast now resides inside the checked ifElse arm.
checks: Lean Beam held worker update/sync/save for FirTalos/ConcreteResidentUSize.lean passed with zero diagnostics and emitted source hash 9a80e0a2a69d7077; `lake -d integration/talos build FirTalos.ConcreteResidentUSize` passed (3,080 jobs); `git diff --check` passed; `make check` passed (704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713 unique cases, zero findings, 190 active bug cards, 25 mailbox tests); `make talos-setup` passed at Talos 0e05edbc; `make talos-check` passed (3,165 jobs).
bug-cards: none
blockers: none. Dependency ordering is explicit: W7's generation branch contains db6d46a7 plus its lean-zip fixture/profile commits; integration should accept that W7 stack before rebasing the W6 proof stack onto the resulting main.
handoff: After accepting W7 head 05dc1f0c (which contains db6d46a7), rebase wasm/talos-runtime onto the new main and land the W6 commits f3ab25c5 (independent green BigNumeric accessor boundary) and a85a5511 (this direct-USize proof), followed by this containing mailbox commit. No W7 implementation, fixture, profile, shared symbolic instruction, root umbrella, or BOARD file was modified by W6.
next: After integration, resume the substantive W6 frontier: discharge the validator-side canonical extent/reserved-lane/ownership/top-nonzero facts needed to construct CheckedNaturalCalls from NaturalObjectRel, then instantiate the resident replacement theorem. Immediate Nat multiplication and subtraction adaptation requests remain separately queued.
```
