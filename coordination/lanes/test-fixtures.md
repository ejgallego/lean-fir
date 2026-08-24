# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 9f53aca11e400f1cb9b6a6f5c54cac913e3aa8ce on main
functional-head: none; S17 planning/status only
contract-base: 9f53aca11e400f1cb9b6a6f5c54cac913e3aa8ce on main; consumes the accepted cache/persistence semantics, repeated cached String child vocabulary, self-tail LCNF lowering, recursive release, copy-on-write append, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S17 tail-position ownership fidelity: compare zero and repeated self-tail transfers of a cached repeated-child String survivor while sibling aliases and loop-carried aggregate owners are released; retain an independent outside alias, append through the returned survivor, and reread the cache
files: planned Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none. S17 is fixture, observation, exact telemetry, and coverage-policy work only; it does not change self-tail lowering, recursive release, interpreter, semantic-Wasm, W6/W7, proof, generator, concrete layout, or artifact contracts
checks: branch rebased cleanly on current main; W7 operational mailbox confirms E3e landed; detached dominance probe, Lean Beam checkpoint, focused native/LCNF/V8, complete make check, and Talos checks pending
bug-cards: none
blockers: none
handoff: not ready; the branch is owned by test-fixtures until the S17 fixture and evidence are complete
next: run the zero-versus-repeated detached dominance probe and promote only if executed self-tail and ownership traces add signal beyond the existing ByteArray tail pair
```
