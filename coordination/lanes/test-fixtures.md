# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 8bcd73260d7cf18d2915e2aaee0a333ed6072c8c on main
functional-head: 55c10089c847ace966fe14b69e10e3aa3f7328c7
contract-base: 8bcd73260d7cf18d2915e2aaee0a333ed6072c8c on main; consumes the linked scalar-closure admission, released CLOSURE-PROJECTION-KIND-REFINEMENT contract at 625d4883, and accepted generic Flat prerequisite
clean-at-update: true
slice: Admit all 32 scalar closures, the mixed one-use/two-use ownership pair, and the outside-alias ByteArray read/mutate pair to the native/LCNF/real-V8 triangle; retain exact LCNF traces, add ownership-specific V8 coverage domains, and schedule tail-call ownership in the memory-fidelity roadmap
files: Fir/Validation/Corpus.lean; docs/validation.md; validation-plans/coverage-index.json; validation-plans/memory-fidelity-roadmap.md; bugs/FIR-BUG-validation-none-nested-boxed-scalar-result.md
contracts: none; consumes linked shared contracts and changes only fixture selection, exact trace requirements, coverage policy, validation documentation, and discrepancy records
checks: PASS after rebase onto 8bcd7326 and after the roadmap update: Lean Beam 0.2.0-beta refresh/sync Fir/Validation/Corpus.lean with zero diagnostics and save-ready; PASS git diff --check; PASS make check (122 harness tests, 646 unique cases, 637/637 native-LCNF cases, 9/9 direct-machine cases, 637/637 native-LCNF-V8 cases, 1920/1920 aggregate comparisons equal, 5900 machine steps, 73/73 tag floors, 183/183 semantic domains, findings 0); earlier focused evidence on the same fixture stack remains PASS for the 30-case generic scalar closure triangle (90/90 comparisons), two-case Boolean closure triangle (6/6), mixed closure triangle (6/6), and outside-alias ByteArray triangle (6/6), all with findings 0; expected downstream FAIL node integration/talos/artifact/check-concrete-validation-products.mjs _build/validation-closure-scalar-generic at current concrete-host.mjs exact-kind assertion `concrete closure capture kind mismatch`
bug-cards: FIR-BUG-validation-none-nested-boxed-scalar-result candidate; existing FIR-BUG-wasm-none-closure-projection-kind-refinement is fixed at the W6 concrete contract but its W7 JavaScript consumer has not consumed the released refinement
blockers: none for fixture landing or the native/LCNF/real-V8 claim; W7 concrete-product acceptance still needs concrete-host.mjs to accept actualKind.refines(expectedKind), read at the actual descriptor kind, and return the unchanged physical word; the four ByteArray-bearing fixtures also require W7 to extend the explicit concrete blocker inventory, and the outside-alias pair additionally lacks concrete ByteArray.get!/ByteArray.set! registrations
handoff: W6 integration owner may land functional head 55c10089c847ace966fe14b69e10e3aa3f7328c7 plus this clean ready mailbox commit as a fixture-only stack based directly on 8bcd7326 after its current proof lease; the stack changes no W6/proof/shared-contract file, native Lean remains the oracle, and every source fixture runs in real V8
next: W7 consumes the released closure-projection refinement in its JavaScript concrete host and extends the explicit ByteArray blocker inventory after rebasing on this fixture stack; lane 4 then adds zero/three closure uses and unique-versus-shared final application, capture alias topology, and the queued tail-call ownership pair without expanding the scalar-value matrix
```
