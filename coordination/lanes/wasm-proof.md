# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: caa2f345 on main
functional-head: 28b380a1
contract-base: 6061b90c on main; the ownership-aware hereditary closure source boundary builds on the unchanged shared interpreter, symbolic Wasm, adapter, concrete-runtime, cache, closure-application, and closure-table contracts
clean-at-update: true
slice: Add a source-only hereditary admission for one exactly saturated closure call whose nested callee derivation starts at the runtime produced by semantic takeClosureApplication; derive the exact caller-visible source execution through let staging, ownership consumption, callee execution under the caller frame, and continuation resumption; prove generated parameter classification preserves declaration arity and expose the new boundary in the contract module
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; this mailbox
contracts: proof-only source admission and compiler-correctness theorem surface; the payload contains source resolution, the semantic ownership-consumption equation, and a finite callee derivation from the post-consumption runtime, but no target candidate, matcher/address witness, or target execution; no shared semantic Wasm ABI, lowering, validator, adapter, concrete-runtime, cache, closure-table, closure-application, or interpreter contract changed
checks: PASS Lean Beam save of ConcreteReuseCapacityCacheCorrectness (zero errors; eleven pre-existing/style warnings) and refresh/save of ConcreteCompilerCorrectnessContract (zero errors); PASS focused lake build FirTalos.ConcreteReuseCapacityCacheCorrectness FirTalos.ConcreteCompilerCorrectnessContract (3104 jobs); PASS git diff --check; PASS make check (642 unique validation cases; 1844/1844 comparisons equal; zero findings; 111 bug cards and trusted assumptions valid); PASS make talos-check (3125 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration; branch contains functional commit 28b380a1 after main and is clean at this mailbox update
next: prove the target selected-candidate path across the ownership-changing matcher/projection prefix, then thread that law into the generalized hereditary evaluator and public compiler-correctness theorem without admitting target execution certificates
```
