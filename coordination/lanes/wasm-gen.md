# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 229640de2cc2e9779d730a529772e3871a3dd70a
functional-head: 56d183620ef64572647e8a48ca79d6f12e62794e
contract-base: 229640de2cc2e9779d730a529772e3871a3dd70a on main
clean-at-update: true
slice: Executable closure-application ownership adapter and exclusive/shared/persistent regression, rebased onto the landed contract and proof stack
files: scripts/wasm_semantic_host.mjs; scripts/test_wasm_validation_externals.mjs; integration/talos/artifact/test-semantic-host.mjs; bugs/FIR-BUG-wasm-none-closure-application-ownership.md
contracts: consumes released CLOSURE-APPLICATION-OWNERSHIP and EXTERNAL-WAITING-RUNTIME exactly; changes no shared contract
checks: PASS git diff --check; PASS node scripts/test_wasm_validation_externals.mjs; PASS node integration/talos/artifact/test-semantic-host.mjs; PASS make check (122 validator tests, 633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 comparisons equal, findings 0); PASS make talos-setup and make talos-check (3125/3125 jobs); PASS bash integration/talos/artifact/check.sh including deterministic rebuilds, zero-function-import text/styled prettyM, browser adapter, semantic host, concrete/native-oracle paths, and packaged release
bug-cards: FIR-BUG-wasm-none-closure-application-ownership fixed
blockers: none
handoff: integrate functional head 56d183620ef64572647e8a48ca79d6f12e62794e plus this ready mailbox commit; package prettyM-current-releases/56d183620ef6-18387878afbd3b7b has 104788-byte prettyM.wasm digest e7ccd1ac678900e0f6583a0d2251b0ef4d43de0b388d18033bbc86344eed4af7
next: integration fast-forwards this green W7 slice and updates coordination/BOARD.md; test-fixtures may then admit the 32 scalar-closure cases
```
