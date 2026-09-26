import RetainedDeclarations
import FirTalos.ConcreteArrayExternal
import FirTalos.TrustAuditCore

open Lean Lean.Compiler Fir.LeanIR.Impure Fir.Wasm.Concrete FirTalos.Concrete
open Lean.Elab.Command FirTalos.Correctness

namespace RetainedInitializer

/-! This module consumes the checked captured program, not a copied initializer.
The theorem is source execution plus saved-caller publication safety. It is
not yet a target execution theorem: Array external admission, resident linking
and suspended-stack closure remain separate obligations. -/

def name : Name := `Zip.Spec.DeflateStoredCorrect.deflateStoredPure._closed_0

def mkEmptyEvent (runtime : RuntimeState) : ExternalEvent := {
  name := `Array.mkEmpty, args := #[.erased, .object (.tagged 5)],
  result := .object (.heap runtime.nextLocation) }

def pushEvent (runtime : RuntimeState) : ExternalEvent := {
  name := `Array.push,
  args := #[.erased, .object (.heap runtime.nextLocation), .object (.tagged 0)],
  result := .object (.heap runtime.nextLocation) }

def resultRuntime (runtime : RuntimeState) : RuntimeState :=
  (semanticArrayResult { runtime with
      trace := (runtime.trace.push (mkEmptyEvent runtime)).push (pushEvent runtime) }
    #[.object (.tagged 0)] 5).setGlobal name (.object (.heap runtime.nextLocation))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem reaches_published
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none) :
    ∃ final,
      run 12 externals (initialState RetainedRC2.program name #[] runtime) =
        .outOfFuel final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = [] := by
  have boxed (state : RuntimeState) :
      box state (.const `UInt8 []) (.scalar (.uint8 0)) =
        .ok (state, .object (.tagged 0)) := by
    exact semanticBox_tagged_eq state (.uint8 0) rfl (by decide)
  have pushed := contract.pushFreshTagged
    { runtime with trace := runtime.trace.push (mkEmptyEvent runtime) }
    (pushDecl.params.map (·.type)) pushDecl.type 5 0 (by decide)
  simp only [pushDecl, mkEmptyEvent, semanticArrayResult, arrayExternalResponse] at pushed
  simp [runProgram, initialState, run, executeStep, coreStep, invokeDecl,
    RetainedRC2.initializer.findDecl, mkEmptyDecl.findDecl, pushDecl.findDecl,
    RetainedRC2.initializer, mkEmptyDecl, pushDecl, bindParams, evalLetValue,
    evalArgs, evalArg, lookupValue, lookup, Fir.LeanIR.Impure.bind, literal, pushBindFrame,
    MachineState.withValue, resumeExternal, observe, cold, name,
    Pure.pure, Bind.bind, Except.pure, Except.bind, maxTaggedPayload,
    contract.mkEmpty, boxed, arrayExternalResponse, semanticArrayResult, pushed,
    resultRuntime, mkEmptyEvent, pushEvent, ReturnedObservation] at *
  simp only [pushed]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem evaluates_and_preservesCaller
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {bindings : List (FVarId × Fir.Wasm.AbiKind)} {env : Env}
    {locals : Wasm.Locals} {savedHeap heap : MemoryState}
    {savedWitness witness : RefinementWitness}
    (saved : ReuseCapacityFactsRel facts bindings env locals savedHeap savedWitness)
    (transport : WitnessTransport savedWitness witness)
    (related : LiveHeapRel heap witness runtime) :
    ∃ final,
      ExecSteps externals 12 (initialState RetainedRC2.program name #[] runtime) final ∧
      final.runtime = resultRuntime runtime ∧
      executeStep externals final = .done
        (ReturnedObservation final.runtime (.object (.heap runtime.nextLocation))) ∧
      ReuseTokenOrdinaryTransport facts env runtime final.runtime := by
  obtain ⟨final, execution, runtimeEq, control, frames⟩ :=
    reaches_published externals contract runtime cold
  refine ⟨final, execSteps_of_run_outOfFuel execution, runtimeEq, ?_, ?_⟩
  · simp [executeStep, coreStep, control, frames, observe, ReturnedObservation]
  · rw [runtimeEq]
    exact freshEmptyArray_pushTagged_publication saved transport related 5 0 name

/-- The external contract has an executable witness, so the body theorem is
not relying on an uninhabited per-program assumption. -/
theorem executable_example :
    ∃ final,
      run 12 freshArrayExternals (initialState RetainedRC2.program name #[] {}) =
        .outOfFuel final ∧
      final.runtime = resultRuntime {} ∧
      final.control = .yielded (.object (.heap 0)) ∧ final.frames = [] :=
  reaches_published freshArrayExternals freshArrayExternals_contract {} rfl

/-- The result describes the actual singleton contents, not just an address
or an external-event trace. Publication marks the Array persistent. -/
theorem example_result_contents :
    findCell? (resultRuntime {}).heap 0 =
      some { object := .array #[.object (.tagged 0)] 5, rc := 0, persistent := true } := by rfl

end RetainedInitializer

-- Existing boxing-policy debt, inherited through semanticBox_tagged_eq.
-- No native evaluation is introduced by the capture or these new proofs.
run_cmd do
  let expected := FirTalos.TrustAudit.standardAxioms ++ #[
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_9",
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_10",
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_11",
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_12",
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_13",
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_14",
    "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_15"]
  for endpoint in #[`RetainedInitializer.reaches_published,
      `RetainedInitializer.evaluates_and_preservesCaller,
      `RetainedInitializer.executable_example] do
    FirTalos.TrustAudit.check endpoint expected
  FirTalos.TrustAudit.check `RetainedInitializer.example_result_contents #["propext"]
