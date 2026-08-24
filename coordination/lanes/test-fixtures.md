# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 67bfb3d0665da4c99a473bca95f4df7c210f3c6a on main
functional-head: 86857ebf, E3e cached caught-error recursive release fixture and coverage policy
contract-base: 67bfb3d0665da4c99a473bca95f4df7c210f3c6a on main; consumes the accepted cache/persistence semantics, repeated cached String child vocabulary, `Except.tryCatch` source semantics, recursive release, copy-on-write append, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S16/E3e caught-error recursive release fidelity: retain one cached String survivor while the error path constructs an ignored aggregate containing two more aliases of the same repeated child, catches and drops that aggregate, appends through the survivor, and rereads the cache. Pair it with the success path, which avoids the error aggregate and releases the unused aliases separately
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none. E3e is fixture, observation, exact telemetry, and coverage-policy work only; it does not change `Except`, recursive release, interpreter, semantic-Wasm, W6/W7, proof, generator, concrete layout, or artifact contracts
checks: detached dominance probe and tracked Lean Beam update/sync/save on Fir/Validation/Corpus.lean, zero diagnostics, save-ready at source hash b45ee77b1531af17; focused native/LCNF equality, 2/2 comparisons equal; focused native/LCNF/V8 with exact traces, 6/6 comparisons equal, zero findings, four/four products opened under strace. Both paths execute exactly 90 interpreter steps; success has five ctor, four dec, and six oproj, while caught error has six ctor, three dec, and five oproj, proving separate releases versus one recursive aggregate release. Clean lean-beam shutdown then make clean and make check, pass: tooling 21 tests, core build 22 jobs, examples 42 jobs, scalar surface 163/163, harness 125 tests, source native/LCNF 712/712 equal, direct machines 9/9 equal, V8 three-way 2136/2136 results equal with 1424/1424 products opened under strace, 1424 native witnesses accepted and verified, coverage 721 unique cases with 2145/2145 policy comparisons equal and 8290 machine steps, all 188 tag and 283 domain floors satisfied, zero findings; make talos-setup, pass at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check, 3172 jobs pass; git diff --check and mailbox protocol validation, pass
bug-cards: none
blockers: none
handoff: integration may land the two-commit E3e test-fixtures stack through the containing ready mailbox commit; the boundary is fixture-only and independently useful
next: after integration, schedule S17 tail-position ownership fidelity: compare zero and repeated tail-recursive transfers of a cached survivor while sibling aliases are released, then observe the survivor and reread the cache
```
