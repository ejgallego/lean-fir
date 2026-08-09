# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 871619fb26983c7644cbcf2f49ca18a46d27ece5 on main
functional-head: d907ef42ac5b74e2b7b8fa23d2290425e272bdd7
contract-base: 6061b90c on main; the proof-owned hereditary finite-evaluation judgment now retains the compiler-derived returned-local ABI and its refinement to the enclosing declaration result, while all shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, and closure-table contracts remain unchanged
clean-at-update: true
slice: Index hereditary finite evaluation by the enclosing declaration result ABI; prove the terminal ABI refinement; establish structural exact-result target correctness for every finite hereditary code spine under explicit generated-operation laws; preserve arbitrary caller budget slack; and package the result as the cache-aware declaration theorem with exact ABI and entry-to-exit transports
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only hereditary judgment and compiler-correctness theorem surface; the result ABI is derived from production getLocal and declaration classification, not supplied by target execution; no semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, or interpreter contract changed
checks: PASS Lean Beam update/sync/save for FirTalos/ConcreteReuseCapacityCacheCorrectness.lean (zero errors; 10 pre-existing/style warnings); PASS focused lake build FirTalos.ConcreteReuseCapacityCacheCorrectness (3103 jobs); PASS make talos-setup (Talos a01d01c778b794dd00956748a067b6793c2c9f9b); PASS git diff --check; PASS make check (122 interpreter-validator tests; 642 unique validation cases; 1844/1844 comparisons equal; zero findings; 109 bug cards and trusted assumptions valid); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: accepted on main at 871619fb; the W6 worktree is rebased exactly to that integration checkpoint
next: discharge the direct-call operation law structurally from the nested callee induction hypothesis, prove DirectHereditaryGeneratedDeclarationInduction from DirectHereditaryGeneratedOperationLaws, and replace the compatibility DirectInternalCallDeclarationInduction in the root theorem
```
