# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 07bb49616a85bfa4c11f629e3dc9b6d3050bc2ab on main
functional-head: b19992882b868251489242322c253a707528153f, admit cached recursive heap persistence and child copy-on-write against native Lean
contract-base: 07bb49616a85bfa4c11f629e3dc9b6d3050bc2ab on main; consumes the accepted nullary-cache interpreter semantics, semantic Wasm cache publication, String append external, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S12/E3 cached recursive heap persistence: call one nullary cached constructor twice; retain the first owner and its String child; optionally append to the child between calls; then return the first owner, observed child, and second cached owner. The skipped/taken pair jointly observes cache miss plus cache hit, recursive persistence of String and large-Nat children, and child copy-on-write versus path exclusion. Exact 37/46-transition LCNF paths, cache administrative yields, and zero/one String.Internal.append execution are pinned
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none changed. The slice adds source corpus cases and sorted coverage floors/domains only. It neither repairs nor approximates cache publication, ownership, external, concrete-runtime, proof, generation, or artifact behavior
checks: PASS Lean Beam save with zero diagnostics and Corpus source hash f2dab1a2e0b49d71; PASS focused rebased native/LCNF/V8 triangle with 6/6 equal comparisons, exact 37/46-transition paths, and 4/4 products opened under strace (29 trace paths); PASS git diff --check; PASS complete rebased make check including 125 harness tests, 704/704 source native/LCNF cases, 9/9 direct machines, 704/704 native/LCNF/V8 triangles, 713 unique cases, 1,417 tier cases, 2,121/2,121 equal comparisons, 7,685 interpreter steps, 178/178 tag floors, 259/259 semantic domains, 1,408/1,408 V8 products opened under strace (1,434 trace paths), 186 bug cards, and 25 mailbox tests; PASS make talos-check (3,148 jobs); findings 0. The final rebase from f204a8b8 to 07bb4961 changes only the accepted Verso Flat source pin and integration board; fixture, semantic compiler, validation harness, Talos tree, and build inputs are unchanged, and post-rebase git diff --check passes
bug-cards: FIR-BUG-impure-none-cached-heap-persistence (existing fixed discrepancy; now strengthened with a source-native/V8 regression); no new discrepancy
blockers: none for S12/E3 semantic admission. Concrete-product execution/classification belongs to W7 after landing and must not change this fixture
handoff: integration may fast-forward the two-commit S12/E3 stack after confirming the status commit resolves from this branch. W7 should run the two cases through the existing concrete artifact gate and record either execution or an exact pre-existing blocker; no orchestration or fixture change is requested
next: after integration and W7 classification, continue E3 with an undominated cached graph topology—prefer a repeated child plus independent outside alias, or cache reuse across an effect/exception boundary—rather than adding scalar cache cases
```
