# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: fb43f4dd50751c193b4437c772ae0dfdebc28a98
functional-head: cf1ed73f7d4c46787ab53641bce549f9a80756d4
contract-base: fb43f4dd50751c193b4437c772ae0dfdebc28a98
clean-at-update: true
slice: Structurally admit compiler-generated erased facade arguments in partial applications and prove precise UInt8 tagged boxing through the general concrete compiler simulation
files: Fir/Wasm/Lower.lean; Fir/Wasm/WellFormed.lean; W6-owned integration/talos/FirTalos concrete runtime, compiler correctness, closure dispatch, cache/call compatibility proofs, and contract fixture; W6 theorem roadmap; scalar-closure admission bug card
contracts: no shared semantic contract changed or duplicated; the W6-owned production lowering/admission surface now computes one effective declaration-parameter row used consistently by locals, partial applications, closure dispatch, supported lowering, and proofs; W7 is expected to rebase before consuming it
checks: PASS Lean Beam sync/save Fir/Wasm/Lower.lean and FirTalos/ConcreteRuntime.lean; PASS Lean Beam sync/save FirTalos/ConcreteReuseCapacityCacheCorrectness.lean and sync FirTalos/ConcreteClosureDispatch.lean plus FirTalos/ConcreteReuseCapacityCallCorrectness.lean; PASS lake build FirTalos.ConcreteReuseCapacityCacheCorrectness; PASS full unfenced 32-case wasm-generation-pending scalar-closure validation (96/96 comparisons, findings 0); PASS git diff --check; PASS make check (633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 aggregate comparisons equal, findings 0); PASS make talos-setup; PASS make talos-check (3125/3125 jobs)
bug-cards: FIR-BUG-wasm-none-generic-scalar-closure-admission fixed
blockers: none
handoff: cf1ed73f7d4c46787ab53641bce549f9a80756d4 is a clean, green W6 functional head based directly on fb43f4dd50751c193b4437c772ae0dfdebc28a98; local representation/admission facts remain supporting lemmas rather than certificate premises of the public compiler theorem
next: integration owner lands this ready slice; W7 and the test-fixture owner rebase, rerun their acceptance gates, and remove the wasm-generation-pending corpus tag now that all 32 scalar-closure cases are admitted
```
