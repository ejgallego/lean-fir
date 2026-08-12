# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: f996628c736546c85a87795fc6d95c694baf0a48 on main
functional-head: f996628c736546c85a87795fc6d95c694baf0a48
contract-base: f996628c736546c85a87795fc6d95c694baf0a48 on main; consumes the linked closure-application ownership and existing `recordByteArray` effect protocol; does not consume or duplicate the active argument-alias, IO-entry, exception, or source-stream contracts
clean-at-update: true
slice: S6 nonlocal ownership boundary: compare final versus retained use of one captured ByteArray around the existing ordered `recordByteArray` effect, then observe the updated result or reread the preserved capture after the effect
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned fixture/coverage/evidence files only after the candidate survives the dominance probe
contracts: none; fixture-only consumer of linked closure ownership and effect projection; the argument-alias and IO/error contracts remain untouched
checks: PASS branch/worktree and clean-base audit at f996628c; implementation and native/LCNF/V8 acceptance pending
bug-cards: none
blockers: none for the first fixture-only pair; the separately queued argument-alias taken/skipped pair remains contract-blocked
handoff: active on validation/closure-ownership-fixtures; no integration handoff yet
next: implement the two provisional cases, use Lean Beam and a focused native/LCNF run to obtain complete signatures, reject them if dominated, otherwise pin their exact effect and ownership evidence before V8 promotion
```
