# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: aa3940b6 on main
functional-head: ac81f18d (previous accepted slice; no W6.7d functional commit yet)
contract-base: aa3940b6; consumes the accepted effective-declaration-result contract and current W7 resident-runtime stack; the object-carrier/provenance descriptor contract has not landed and does not block independent structured terminal adequacy
clean-at-update: true
slice: Begin W6.7d structured terminal adequacy: define the reachable frame-stack/arity invariant and prove that every finite canonical generated-entry-to-halted structured-machine path collapses to the exact Talos Wasm.run result, without accepting target execution evidence at the public compiler boundary.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/Correctness/ and integration/talos/FirTalos/
contracts: none; this slice proves adequacy for the accepted structured machine and symbolic Wasm surface
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: State and prove reachable-frame/arity preservation, then derive canonical-entry-to-halted structured terminal adequacy and validate its dependency cone. Rebase and adapt after the object-carrier/provenance descriptor contract lands.
```
