# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 480c15e7 on main
functional-head: none yet
contract-base: 480c15e7 on main; static closure-candidate resolution and recursive whole-export correctness are linked/accepted
clean-at-update: true
slice: Derive the uniform static closure-candidate adapter environment directly from the supported lowering, numeric adaptation, and host-resolution pipeline, then remove that environment from the public whole-export theorem's caller-supplied premises
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; this mailbox
contracts: No shared semantic, ABI, concrete-layout, resident-helper, or artifact change is planned; this packages existing compiler output into the proof-facing static resolver internally
checks: pending
bug-cards: none
blockers: none
handoff: not ready
next: prove candidate adaptation and host alignment composition, lift it over the compiler's exact flatMap enumeration, and discharge the public resolver argument from ConcreteSupportedFunction
```
