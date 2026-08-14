# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: dbe40b79caaec4c4a7cbf22ae62e6f5ec415e8a8 on main
functional-head: 13a8998f, accept Array nested-alias manifests and admit repeated-child Array/ByteArray copy-on-write fidelity
contract-base: dbe40b79caaec4c4a7cbf22ae62e6f5ec415e8a8 on main; consumes the accepted object-field typing admission plus protocol-v3 Array/nested-alias, generic Array, ByteArray, semantic Wasm, and real-V8 surfaces; changes no shared protocol, interpreter, proof, runtime, generation, or artifact contract
clean-at-update: true
slice: S11/A-E1 repeated-child Array copy-on-write: materialize one outside ByteArray alias in both slots of a generic Array, retain the original across Array.set!, mutate the outside child through ByteArray.set!, return all three observations, and pin the exact 24-transition LCNF/external path; also fix the generic Python manifest mirror for nested aliases below Array schemas
files: Fir/Validation/Corpus.lean; scripts/validation_harness.py; scripts/test_validate_interpreters.py; bugs/FIR-BUG-validation-none-array-nested-alias-manifest.md; bugs/FIR-BUG-impure-none-array-mkempty-validation-external.md; bugs/FIR-BUG-impure-none-array-getinternal-validation-external.md; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none changed. The Python harness now accepts the Array branch already defined by protocol v3 and checked by Lean; no wire shape or alias rule changed. LCNF/Wasm implementations for Array.mkEmpty and Array.getInternalBorrowed remain shared follow-ups and were not added or approximated locally
checks: PASS Lean Beam update/sync/save with zero diagnostics and Corpus checkpoint ac4a6393fdcc747b; PASS focused native/LCNF/V8 triangle with 3/3 equal comparisons, exact 24-transition LCNF path, and 2/2 products opened under strace; PASS git diff --check; PASS complete make check including 125 harness tests, 702/702 source native/LCNF cases, 9/9 direct machines, 702/702 native/LCNF/V8 triangles, 711 unique cases, 1,413 tier cases, 2,115/2,115 equal comparisons, 7,602 interpreter steps, 162/162 tag floors, 253/253 semantic domains, 1,404/1,404 V8 products opened under strace, 185 bug cards, and 25 mailbox tests; PASS make talos-setup then make talos-check (3,148 jobs); findings 0
bug-cards: FIR-BUG-validation-none-array-nested-alias-manifest (fixed with regression); FIR-BUG-impure-none-array-mkempty-validation-external (candidate, unresolved); FIR-BUG-impure-none-array-getinternal-validation-external (candidate, unresolved)
blockers: none for S11. Source Array literal and proof-backed borrowed-read coverage remain parked behind their two exact validation-external cards
handoff: integration may fast-forward the complete three-commit S11 stack after rerunning required checks. W7 should classify the new initial-ByteArray case in its concrete-product blocker inventory without changing the fixture's semantic admission
next: hand the two exact external gaps to integration/W7, then select the next undominated memory slice; prefer persistent/cached heap ownership or a unique-versus-shared container path that adds allocation/release signal rather than another scalar or one-shot closure case
```
