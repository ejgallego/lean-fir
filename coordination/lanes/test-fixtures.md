# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 6910495c6a98b7b3439b6083a3cb8dd50cd4180a on main
functional-head: a6543da1f90712075947b0afff1bd883002f834f, admit cached recursive heap persistence and child copy-on-write against native Lean
contract-base: 6910495c6a98b7b3439b6083a3cb8dd50cd4180a on main; consumes the accepted cache/persistence semantics, deterministic semantic-Wasm product publication, real-V8 surface, checked-Nat producer proofs, and checked-decrement gates; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S13/E3b cached shared-DAG alias fidelity: construct one cached owner whose two fields share the same heap child, retain an independent alias outside the owner, optionally mutate through one projection, call the nullary cache again, and observe both original fields, the outside alias, the mutation result, and the second cached owner. Pair the taken path with path exclusion to distinguish recursive publication, repeated-child ownership, alias preservation, and copy-on-write
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none planned. The fixture lane owns only corpus cases, observations, exact telemetry, and coverage requirements; no interpreter, semantic-Wasm, concrete-runtime, proof, generator, or artifact change is in scope
checks: not-run for S13/E3b
bug-cards: FIR-BUG-impure-none-cached-heap-persistence and FIR-BUG-wasm-none-validation-product-cold-publication are accepted fixed history; none new
blockers: none. W6 has active uncommitted Natural-validator work and W7 has an independent proof-blocked early closure-lowering branch; S13/E3b does not touch either ownership surface
handoff: none until the exact native/LCNF/V8 pair and required gates are green
next: admit the smallest repeated-child cached graph with an independently retained alias; pin taken/skipped execution signatures before expanding to cache reuse across effects or exceptions
```
