# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 67bfb3d0665da4c99a473bca95f4df7c210f3c6a on main
functional-head: none; E3e fixture implementation has not yet been committed. E3d cached release-across-effect fidelity is accepted on main through 67bfb3d0
contract-base: 67bfb3d0665da4c99a473bca95f4df7c210f3c6a on main; consumes the accepted cache/persistence semantics, repeated cached String child vocabulary, `Except.tryCatch` source semantics, recursive release, copy-on-write append, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S16/E3e caught-error recursive release fidelity: retain one cached String survivor while the error path constructs an ignored aggregate containing two more aliases of the same repeated child, catches and drops that aggregate, appends through the survivor, and rereads the cache. Pair it with the success path, which avoids the error aggregate and releases the unused aliases separately
files: anticipated Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none. E3e is fixture, observation, exact telemetry, and coverage-policy work only; it does not change `Except`, recursive release, interpreter, semantic-Wasm, W6/W7, proof, generator, concrete layout, or artifact contracts
checks: detached probe on accepted E3d: Lean Beam update/sync, zero diagnostics; focused native/LCNF equality, 2/2 comparisons equal; focused native/LCNF/V8 with exact traces, 6/6 comparisons equal, zero findings, four/four products opened under strace. Both paths execute exactly 90 interpreter steps; success has five ctor, four dec, and six oproj, while caught error has six ctor, three dec, and five oproj, proving separate releases versus one recursive aggregate release
bug-cards: none
blockers: none
handoff: none; tracked implementation and coverage policy are in progress
next: transfer the pinned detached fixture to the tracked lane, add dedicated source/V8 semantic domains, then run focused and required full gates
```
