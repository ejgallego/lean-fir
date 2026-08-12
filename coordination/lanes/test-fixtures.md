# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 66aeb6d166d44f1fbfcd750bc67bdf8f71b31e7b on main
functional-head: 84ef07e95c0edd7668f41cce5948cbd0ff4a8869
contract-base: 499eff34fb852c2b2468cd13e6a95084708b01d4 on main; consumes the linked closure-application, aggregate, erased-field, and ByteArray runtime surfaces; does not consume or duplicate active proof, W6, W7, error, exception, or source-stream contracts
clean-at-update: true
slice: S9/E2 dictionary ownership: compare consuming a two-method runtime class dictionary before captured ByteArray mutation with retaining it across mutation and invoking the observer sibling afterward
files: Fir/Validation/Corpus.lean; bugs/FIR-BUG-impure-none-dictionary-specialization-capture.md; validation-plans/semantic-fidelity-roadmap.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; docs/validation.md; coordination/lanes/test-fixtures.md
contracts: none; fixture-only; the generated-specialization capture discrepancy is carded rather than accommodated, and active proof/Wasm/error contracts remain fenced
checks: PASS Lean Beam update/sync/save Fir/Validation/Corpus.lean at version 6 with zero diagnostics and source hash 16b8be783ff61f5c; PASS lake build fir-native-oracle Fir.Validation; PASS focused native/LCNF pair 4/4; PASS focused native/LCNF/V8 triangle 6/6 with 4/4 unique products opened under strace; PASS git diff --check; PASS complete make check including 122 harness tests, 661/661 source native/LCNF cases, 9/9 direct machines, 661/661 native/LCNF/V8 triangles, 1,322 native-oracle witnesses, 1,992/1,992 indexed comparisons, 7,176 interpreter steps, 160/160 tag floors, and 253/253 semantic domains; findings 0; PASS all 1,322 V8 products opened under strace; PASS 146 bug cards and exactly one registered trusted axiom
bug-cards: FIR-BUG-impure-none-dictionary-specialization-capture (candidate compiler discrepancy; unresolved implicit-class generated-specialization capture; no workaround in shared code)
blockers: none
handoff: integration may fast-forward functional head 84ef07e9 plus this ready mailbox; no shared contract changed
next: after acceptance, keep S9 as the dictionary sibling-lifetime baseline; continue E2 only with a polymorphic runtime-shape pair whose final execution signature is not dominated by S9 or scalar ABI coverage
```
