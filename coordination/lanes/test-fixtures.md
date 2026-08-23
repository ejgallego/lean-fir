# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 63204d2e068e663da1e20351f7527d924dad71b3 on main
functional-head: 83faa835, rebased E3c cached repeated-child generic UInt8 Array DAG fixture and validation-gap cards; rebased E3b functional head 410ea2d4 remains the first independently landable boundary
contract-base: 63204d2e068e663da1e20351f7527d924dad71b3 on main; consumes the accepted cache/persistence semantics, deterministic semantic-Wasm product publication, real-V8 surface, direct ByteArray-size closure, trusted Array mutation setup, USize caller fast path, and sparse constructor initialization; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S14/E3c cached repeated-child generic UInt8 Array fidelity: construct one nullary cached owner whose two fields share the same Array child, retain an outside alias, pair a skipped path with copy-on-write set!, read the cache again, and observe both original fields, the outside alias, the result, and the second owner. Exact executed LCNF form counts/traces pin cache initialization/hit, projections, ownership increments, allocation, decrement, mutation, construction, and completion; exact external counts distinguish the skipped one-allocation path from the taken two-allocation path
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; bugs/FIR-BUG-impure-none-array-mkempty-validation-external.md; bugs/FIR-BUG-impure-none-byte-array-mk-validation-external.md; coordination/lanes/test-fixtures.md
contracts: none. E3c adds only corpus cases, observations, exact telemetry, dedicated cached-array-DAG coverage floors, and discrepancy records; no shared protocol, interpreter, semantic-Wasm, concrete-runtime, proof, generator, or artifact surface changes
checks: on base 63204d2e, git diff --check, pass; focused native-lcnf-v8 pair, 6/6 backend results equal with zero findings and all 4 semantic-Wasm products opened; both focused Wasm modules and manifests are byte-identical to the prior complete green run, so the rebase changed no focused generated or semantic result. Prior applicable complete gates: rebased Lean Beam refresh/save on Fir/Validation/Corpus.lean, zero diagnostics and save-ready; clean lake clean then make check, pass: source-lcnf 708/708 equal, direct-lcnf 9/9 equal, V8 three-way 2124/2124 results equal, coverage 717 unique cases and 7947 machine steps with all 184 tag and 271 domain floors satisfied, zero findings; make talos-setup, pass at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check, 3172 jobs pass; mailbox protocol validation, pass
bug-cards: FIR-BUG-impure-none-array-mkempty-validation-external, existing candidate refreshed with the cold cached-DAG boundary; FIR-BUG-impure-none-byte-array-mk-validation-external, new candidate for the independent wrapper-construction external
blockers: none. Source-built cached ByteArray coverage remains explicitly deferred until the two validation-external candidates receive shared ownership contracts; no workaround was added
handoff: integration may land the rebased green test-fixtures stack through the containing ready mailbox commit. E3b at 410ea2d4 is the smaller boundary; E3c at 83faa835 adds the generic Array DAG pair and both explicit ByteArray-frontier cards
next: after integration, continue fixture-only memory fidelity with a cached alias surviving an effect/suspension or caught-exception boundary before a second alias is reused
```
