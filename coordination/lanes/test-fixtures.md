# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 837e760135e1ba3952177c2e4b7107e561b4df7c on main
functional-head: a9ced6ff0686f1f2da157c25ff789dd91cb45ff2, prior E3b cached repeated-child String DAG fixture, still independently landable
contract-base: 837e760135e1ba3952177c2e4b7107e561b4df7c on main; consumes the accepted cache/persistence semantics, deterministic semantic-Wasm product publication, real-V8 surface, and direct ByteArray-size closure; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S14/E3c cached repeated-child ByteArray fidelity: construct one cached owner whose two fields share the same ByteArray child and therefore the same backing Array, retain an independent alias outside the owner, optionally mutate one byte through the sibling, call the nullary cache again, and observe both original fields, the outside alias, the result, and the second cached owner. Pair mutation with path exclusion and pin the exact execution signature
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none planned. E3c is limited to corpus cases, observations, exact telemetry, and coverage requirements; no interpreter, semantic-Wasm, concrete-runtime, proof, generator, or artifact change is in scope
checks: not-run for S14/E3c; prior E3b handoff was fully green
bug-cards: FIR-BUG-impure-none-cached-heap-persistence and FIR-BUG-wasm-none-validation-product-cold-publication are accepted fixed history; none new
blockers: none. Active W6/W7 trusted-ByteArray helper/proof work owns different files and contracts; E3c consumes only the already accepted source/interpreter/V8 ByteArray.set! surface
handoff: none for E3c until its exact native/LCNF/V8 pair and required gates are green. Integration may still select the prior functional-head a9ced6ff as the independent E3b landing boundary
next: admit the smallest cached repeated-child ByteArray graph, derive its taken/skipped traces from execution, and reject or card any unsupported or divergent semantic boundary before accommodation
```
