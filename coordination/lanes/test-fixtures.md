# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 72a2faa10effcd54584867791adf124d49c382fc on main
functional-head: 5c66972a, rebased E3c cached repeated-child generic UInt8 Array DAG fixture and validation-gap cards; rebased E3b functional head 0c001e39 remains the first independently landable boundary
contract-base: 72a2faa10effcd54584867791adf124d49c382fc on main; consumes the accepted cache/persistence semantics, deterministic semantic-Wasm product publication, real-V8 surface, direct ByteArray-size closure, trusted Array mutation setup, and USize caller fast path; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S14/E3c cached repeated-child generic UInt8 Array fidelity: construct one nullary cached owner whose two fields share the same Array child, retain an outside alias, pair a skipped path with copy-on-write set!, read the cache again, and observe both original fields, the outside alias, the result, and the second owner. Exact executed LCNF form counts/traces pin cache initialization/hit, projections, ownership increments, allocation, decrement, mutation, construction, and completion; exact external counts distinguish the skipped one-allocation path from the taken two-allocation path
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; bugs/FIR-BUG-impure-none-array-mkempty-validation-external.md; bugs/FIR-BUG-impure-none-byte-array-mk-validation-external.md; coordination/lanes/test-fixtures.md
contracts: none. E3c adds only corpus cases, observations, exact telemetry, dedicated cached-array-DAG coverage floors, and discrepancy records; no shared protocol, interpreter, semantic-Wasm, concrete-runtime, proof, generator, or artifact surface changes
checks: revalidation pending on rebased main 72a2faa1; the e2cf1c31-based stack was fully green under rebased Lean Beam, focused native/LCNF/V8, clean make check, and 3171-job Talos gates
bug-cards: FIR-BUG-impure-none-array-mkempty-validation-external, existing candidate refreshed with the cold cached-DAG boundary; FIR-BUG-impure-none-byte-array-mk-validation-external, new candidate for the independent wrapper-construction external
blockers: none. Source-built cached ByteArray coverage remains explicitly deferred until the two validation-external candidates receive shared ownership contracts; no workaround was added
handoff: none until the 72a2faa1-based E3b/E3c stack passes the focused and required repository gates
next: revalidate after the accepted USize caller fast path, publish the refreshed ready head, then continue fixture-only memory fidelity with a cached alias surviving an effect/suspension or caught-exception boundary before a second alias is reused
```
