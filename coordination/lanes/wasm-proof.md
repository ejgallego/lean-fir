# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: d8ac1b47ebe0ce2ef4d6efc10a2924eb2772e2fb
functional-head: d8ac1b47ebe0ce2ef4d6efc10a2924eb2772e2fb
contract-base: d8ac1b47ebe0ce2ef4d6efc10a2924eb2772e2fb
clean-at-update: true
slice: Add a reusable observable finite-prefix simulation composition boundary, embed the ranked W6 theorem into it, and expose honest backward-pass precomposition before introducing the sumTo admission fixture.
files: integration/talos/FirTalos/Correctness/WeakSimulation.lean; integration/talos/FirTalos/ConcreteTraceSimulation.lean; coordination/lanes/wasm-proof.md
contracts: additive W6 proof-facing composition surface only; the existing ranked concrete theorem, source semantics, pass semantics, ABI, runtime/layout, lowering, and emitted code remain unchanged
checks: not-run
bug-cards: none
blockers: none
handoff: none
next: Prove the generic composition laws, then use sumTo to drive static final-LCNF admission and one backward pass edge without program-specific execution enumeration.
```
