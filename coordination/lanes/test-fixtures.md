# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: waiting
base: f37af09e685364f62e87083bcf284174d2f3d7df on main
functional-head: a6543da1f90712075947b0afff1bd883002f834f, admit cached recursive heap persistence and child copy-on-write against native Lean
contract-base: f37af09e685364f62e87083bcf284174d2f3d7df on main; consumes the accepted nullary-cache interpreter semantics, semantic Wasm cache publication, String append external, real-V8 surface, indexed final-LCNF capture ownership, and W6 bit-exact float scalar field proof stack; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S12/E3 cached recursive heap persistence: call one nullary cached constructor twice; retain the first owner and its String child; optionally append to the child between calls; then return the first owner, observed child, and second cached owner. The skipped/taken pair jointly observes cache miss plus cache hit, recursive persistence of String and large-Nat children, and child copy-on-write versus path exclusion. Exact 37/46-transition LCNF paths, cache administrative yields, and zero/one String.Internal.append execution are pinned
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; coordination/lanes/test-fixtures.md
contracts: none changed. The slice adds source corpus cases and sorted coverage floors/domains only. It neither repairs nor approximates cache publication, ownership, external, concrete-runtime, proof, generation, or artifact behavior
checks: PASS Lean Beam refresh/save on f37af09e with zero diagnostics and Corpus source hash f2dab1a2e0b49d71; PASS focused native/LCNF/V8 triangle with 6/6 equal comparisons, exact 37/46-transition paths, and 4/4 products opened under strace (29 trace paths); PASS git diff --check; PASS complete quiescent make check including 7/7 tooling unit tests, 125 harness tests, 704/704 source native/LCNF cases, 9/9 direct machines, 704/704 native/LCNF/V8 triangles, 713 unique cases, 1,417 tier cases, 2,121/2,121 equal comparisons, 7,685 interpreter steps, 178/178 tag floors, 259/259 semantic domains, 1,408/1,408 V8 products opened under strace (1,434 trace paths), 187 bug cards, and 25 mailbox tests; PASS make talos-check (3,148 jobs); findings 0. A simultaneous W7 artifact run and fixture refresh initially raced on _build/validation-v8 and produced identical semantic run identities with different strace hashes; after both writers quiesced, the complete command and immediate coverage-index verification pass
bug-cards: FIR-BUG-impure-none-cached-heap-persistence (existing fixed discrepancy; strengthened with this source-native/V8 regression); FIR-BUG-wasm-none-validation-product-cold-publication (confirmed W7 artifact publication/gate race; unresolved); no semantic discrepancy
blockers: none for S12/E3 semantics or concrete execution. W7 confirmed both new products execute and the concrete inventory remains 642 executed plus the unchanged 62 initial-ByteArray blockers. Final linked/accepted status waits on W7 resolving or dispositioning FIR-BUG-wasm-none-validation-product-cold-publication and passing the complete artifact gate once without a warm retry
handoff: functional fixture a6543da1 and tracked semantic handoff 4733a08e are already on local main. Integration should not replay them. Consume this refreshed status after W7 returns a clean artifact-gate handoff; only the integration owner updates the board and final acceptance record
next: wait for W7 artifact-gate closure, then continue E3 with an undominated cached graph topology—prefer a repeated child plus independent outside alias, or cache reuse across an effect/exception boundary—rather than adding scalar cache cases
```
