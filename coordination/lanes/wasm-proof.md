# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 92e94f2d on main
functional-head: 625d4883
contract-base: 92e94f2d on main; the ownership-aware hereditary closure source boundary and existing concrete closure descriptor/application contracts
clean-at-update: true
slice: Thread persistent, exclusive-transfer, and shared-retain closure ownership through the executable matcher into the complete cache/capacity frame; derive the selected candidate's actual post-consumption store instead of assuming store identity; repair closure projection so an immutable precise capture descriptor may widen exactly along AbiKind.refines to the generated callee parameter kind; expose resolver-selected closureProj imports and an executable tagged-to-tobject allocation/matcher/projection regression
files: Fir/Wasm/Concrete/OwnershipFrameCorrectness.lean; Fir/Wasm/Concrete/ClosureApplicationCorrectness.lean; Fir/Wasm/Concrete/ClosureRuntime.lean; Fir/Wasm/Concrete/ClosureCorrectness.lean; integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/ConcreteRuntimeExamples.lean; bugs/FIR-BUG-wasm-none-closure-projection-kind-refinement.md; this mailbox
contracts: CLOSURE-PROJECTION-KIND-REFINEMENT accepts exactly actualKind.refines expectedKind at live and post-application capture projection, reads at the immutable descriptor kind, and preserves the physical lane while widening its proof relation; the resident projection helper already performs the same raw slot load, so no W7 implementation change is required
checks: PASS Lean Beam zero-error checkpoints for the changed root concrete modules and FirTalos ConcreteRuntime, ConcreteSupportedExportCorrectness, and ConcreteRuntimeExamples; PASS focused root and Talos dependency builds including FirTalos.ConcreteCompilerCorrectnessContract; PASS git diff --check; PASS make check (633 native/LCNF cases, 1,266/1,266 results, zero findings; direct machine suite 9/9); PASS make talos-check (3,125 jobs)
bug-cards: FIR-BUG-wasm-none-closure-projection-kind-refinement fixed with executable allocation/matcher/projection regression
blockers: none
handoff: ready for fast-forward integration; branch contains ownership functional head 9ef99067 followed by projection-contract functional head 625d4883 and is clean at this mailbox update
next: define and preserve the program-indexed closure heap ABI invariant stating that every live closure descriptor refines its target declaration's fixed parameter prefix; use it to derive generated capture assembly and enter the selected callee from selected.nextStore
```
