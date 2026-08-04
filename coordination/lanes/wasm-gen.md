# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: fb43f4dd50751c193b4437c772ae0dfdebc28a98
functional-head: 4404aba07aa90fb96dc43b5ca056ca38a32fd4bc
contract-base: fb43f4dd50751c193b4437c772ae0dfdebc28a98 on main
clean-at-update: true
slice: Consume SCALAR-CLOSURE-ABI-ADMISSION after its standalone shared-lowering repair, then establish generation readiness for the 30 fixed-width generic closure entries and two Boolean closure entries without changing their fixtures
files: none while waiting; W7 will change only Fir/Wasm/Emit or W7 artifact coverage if a post-validation generation gap remains after the shared repair
contracts: consumes SCALAR-CLOSURE-ABI-ADMISSION; proposes no W7 contract change
checks: PASS integration exact-base git diff --check and make check at fb43f4dd (122 harness tests, 633 native/LCNF, 9 direct-machine, 601 native/LCNF/V8, 1844/1844 comparisons equal, findings 0); PASS diagnostic final-LCNF probes identify rejection before emission at erased-to-tobject generic _boxed PAP compatibility and imprecise tobject-to-tagged UInt8 box capture; no W7 functional delta to check
bug-cards: FIR-BUG-validation-none-mixed-closure-facade-export fixed; FIR-BUG-wasm-none-generic-scalar-closure-admission active
blockers: W6/shared lowering must land a standalone sound repair for erased generic _boxed PAP compatibility and precise always-tagged UInt8 boxing, with its lowering/proof cone green
handoff: none; W7 is intentionally waiting at the shared-contract boundary
next: after the W6 repair lands on main, rebase this branch, compile all 32 entries through compileValidationInvocation, run focused Node/V8 admission, and publish generation-ready results for test-fixtures to remove the fences
```
