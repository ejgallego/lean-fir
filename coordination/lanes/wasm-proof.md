# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 81c03c98 on main
functional-head: 1e49bef7 (exact structured execution assembles the selected saturated closure's captures and ordinary arguments)
contract-base: 81c03c98; proof-only extension over the accepted exact saturated-closure dispatch and argument-execution contracts
clean-at-update: true
slice: ClosureCaptureRows.structuredFlatProgram_of_adapted derives flatness for the compiler-generated capture projection code directly from the source-to-target adapter relation, and SaturatedClosureCallResolution.argumentsStructuredFlatProgram combines it with the ordinary argument compiler. ClosureArgumentAssembly.structuredFinitePath turns that proof into exact structured execution. SaturatedClosureCallResolution.argumentsStructuredFinitePath then assembles the selected closure's projected captures and ordinary arguments, proves ConstructorArgumentsRelated for the full callee parameter row and captures ++ semanticArgs, and reaches physicalArgs.reverse ++ tail in exactly targetCode.length steps under arbitrary residual code and frames. The theorem accepts neither target syntax nor target execution certificates.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof construction over accepted contracts
checks: Lean Beam 0.2.0-beta (source 662b514f) update/sync/save document version 19 hash e9083827d5be1a63 (zero local warnings); forced lake env lean FirTalos/ConcreteStructuredSimulation.lean; lake build FirTalos.ConcreteStructuredSimulation (3110 jobs); git diff --check; make check (122 tests, 633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 indexed comparisons); Talos remains at setup a01d01c; make talos-check (3133 jobs); all green
bug-cards: none
blockers: none
handoff: none; the exact saturated argument-execution slice landed on main at 81c03c98 and the lane is active on callee/control composition.
next: Compose the now-exact selected argument execution with generated callee entry, recursive callee simulation, result-local write, and exact unwinding of the recorded conditional labels. Defer heap-valued lazy publication until the entry transport is made facts-aware.
```
