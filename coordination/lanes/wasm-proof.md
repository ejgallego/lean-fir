# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 9594e9ce on main
functional-head: 7e2e8004
contract-base: 9594e9ce; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, positive return-path, and structured bind-frame slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Proved the compiler-derived structured direct-call path through argument-prefix execution and actual Wasm call entry. ConstructorArgsReady.finitePath gives the exact generated localGet/erased-zero path. ConcreteStructuredCodeFocus.advance_directCall_stage inverts production adaptation and reaches a call-ready relation without a target-execution certificate. ConcreteStructuredDirectCallReadyFocus.advance_enter matches one source dispatcher step with StructuredWasmStep.enterCall and establishes a generated callee code focus plus the exact saved source bind and Wasm call frames. The relation deliberately retains caller invariants separately for transport across callee effects.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: lean-beam target diagnostics 0 errors and 0 warnings after dependency refresh; lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm (3111 jobs) passed; lake env lean FirTalos/ConcreteStructuredSimulation.lean passed; rg sorry/admit clean; git diff --check passed; make check passed (642 unique cases, 1844/1844 comparisons equal, 124 bug cards); make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3133 jobs)
bug-cards: none
blockers: none
handoff: ready for integration from wasm/talos-runtime; functional head 7e2e8004 over base 9594e9ce
next: Transport the saved caller state/local/frame relation across callee allocation and effects, then convert a related callee yield into the accepted ConcreteStructuredBindFrameFocus for return unwinding.
```
