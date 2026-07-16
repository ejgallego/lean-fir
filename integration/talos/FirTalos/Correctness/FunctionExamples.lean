import FirTalos.Correctness.Function
import Fir.Wasm.Examples

namespace FirTalos.Correctness

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples

deriving instance DecidableEq for AbiKind
deriving instance DecidableEq for Wasm.Locals

private def literalBodyCheck : Wasm.Program → Bool
  | [.call callIndex, .localSet resultIndex, .localGet returnIndex, .ret] =>
      callIndex == 0 && resultIndex == 0 && returnIndex == 0
  | _ => false

private theorem literalBody_eq_of_check {body : Wasm.Program}
    (checked : literalBodyCheck body = true) :
    body = [.call 0, .localSet 0, .localGet 0, .ret] := by
  unfold literalBodyCheck at checked
  split at checked <;> simp_all

private def literalOperationsCheck : List HostOperation → Bool
  | [.naturalLiteral value kind] => value == 42 && kind == .tobject
  | _ => false

private theorem literalOperations_eq_of_check {operations : List HostOperation}
    (checked : literalOperationsCheck operations = true) :
    operations = [.naturalLiteral 42 .tobject] := by
  unfold literalOperationsCheck at checked
  split at checked <;> simp_all

/-- The checked symbolic module produced from W3's natural-literal program. -/
def abiLiteralSourceModule : Fir.Wasm.Module :=
  match Fir.Wasm.lowerSupported abiLiteralProgram with
  | .ok source => source
  | .error _ => default

theorem abiLiteralSourceModule_lowered :
    Fir.Wasm.lowerSupported abiLiteralProgram = .ok abiLiteralSourceModule := by
  have success : (Fir.Wasm.lowerSupported abiLiteralProgram).isOk = true := by
    native_decide
  cases lowered : Fir.Wasm.lowerSupported abiLiteralProgram with
  | error error =>
      rw [lowered] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok source => simp [abiLiteralSourceModule, lowered]

/-- The only symbolic function in the checked W3 literal module. -/
def abiLiteralSourceFunction : Fir.Wasm.Function :=
  match abiLiteralSourceModule.functions[0]? with
  | some function => function
  | none => default

theorem abiLiteralSourceFunction_found :
    abiLiteralSourceModule.functions[0]? = some abiLiteralSourceFunction := by
  have present : abiLiteralSourceModule.functions[0]?.isSome = true := by
    native_decide
  cases found : abiLiteralSourceModule.functions[0]? with
  | none => simp [found] at present
  | some function => simp [abiLiteralSourceFunction, found]

/-- The exact source declaration and compiler context of the W3 fixture. -/
def abiLiteralDecl : Lean.Compiler.LCNF.LetDecl .impure :=
  letDecl x tobjectType (.lit (.nat 42))

def abiLiteralCode : Lean.Compiler.LCNF.Code .impure :=
  .let abiLiteralDecl (.return x)

def abiLiteralContext : Fir.Wasm.Context :=
  { program := abiLiteralProgram, localKinds := [(x, .tobject)] }

private def emptyAdaptedModule : AdaptedModule :=
  { wasmModule := default, sourceMap := default }

/-- The executable Talos module produced by adapting the checked W3 fixture. -/
def abiLiteralAdaptedModule : AdaptedModule :=
  match adapt abiLiteralSourceModule with
  | .ok target => target
  | .error _ => emptyAdaptedModule

theorem abiLiteralAdaptedModule_adapted :
    adapt abiLiteralSourceModule = .ok abiLiteralAdaptedModule := by
  have success : (adapt abiLiteralSourceModule).isOk = true := by
    native_decide
  cases adapted : adapt abiLiteralSourceModule with
  | error error =>
      rw [adapted] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok target => simp [abiLiteralAdaptedModule, adapted]

/-- Concrete whole-module layout evidence for the W3 literal fixture. -/
theorem abiLiteralAdaptedModule_layout :
    ∃ functions,
      abiLiteralSourceModule.functions.toList.mapM
          (function abiLiteralSourceModule) = .ok functions ∧
        abiLiteralAdaptedModule.wasmModule = {
          funcs := functions
          imports := abiLiteralSourceModule.imports.toList.map importDecl
          exports := abiLiteralSourceModule.exports.toList.filterMap fun name =>
            (abiLiteralSourceModule.functions.findIdx? (·.name == name)).map
              fun index =>
                { name := name.toString
                  funcIdx := abiLiteralSourceModule.imports.size + index : Wasm.Export } } :=
  adapt_preserves_module_layout abiLiteralAdaptedModule_adapted

/-- The concrete semantic hosts resolved for the same W3 fixture. -/
def abiLiteralResolvedHosts : ResolvedHosts :=
  match resolveHosts abiLiteralSourceModule with
  | .ok resolved => resolved
  | .error _ => { operations := [] }

theorem abiLiteralResolvedHosts_resolved :
    resolveHosts abiLiteralSourceModule = .ok abiLiteralResolvedHosts := by
  have success : (resolveHosts abiLiteralSourceModule).isOk = true := by
    native_decide
  cases resolved : resolveHosts abiLiteralSourceModule with
  | error error =>
      rw [resolved] at success
      change false = true at success
      exact Bool.noConfusion success
  | ok hosts => simp [abiLiteralResolvedHosts, resolved]

/-- W3's literal program resolves `main` to the first defined function. -/
theorem abiLiteralMain_exported :
    abiLiteralAdaptedModule.wasmModule.findExport "main" = some 1 := by
  native_decide

/-- Its only defined function occupies unified index one, after one host import. -/
def abiLiteralMainFunction : Wasm.Function :=
  match abiLiteralAdaptedModule.wasmModule.funcs[
      1 - abiLiteralAdaptedModule.wasmModule.imports.length]? with
  | some function => function
  | none => default

theorem abiLiteralMain_found :
    abiLiteralAdaptedModule.wasmModule.funcs[
        1 - abiLiteralAdaptedModule.wasmModule.imports.length]? =
      some abiLiteralMainFunction := by
  have present :
      (abiLiteralAdaptedModule.wasmModule.funcs[
        1 - abiLiteralAdaptedModule.wasmModule.imports.length]?).isSome = true := by
    native_decide
  cases found : abiLiteralAdaptedModule.wasmModule.funcs[
      1 - abiLiteralAdaptedModule.wasmModule.imports.length]? with
  | none => simp [found] at present
  | some function => simp [abiLiteralMainFunction, found]

theorem abiLiteralMain_notImport :
    abiLiteralAdaptedModule.wasmModule.imports[1]? = none := by
  native_decide

theorem abiLiteralMain_resultCount :
    abiLiteralMainFunction.results.length = 1 := by
  native_decide

theorem abiLiteralMain_body :
    abiLiteralMainFunction.body =
      [.call 0, .localSet 0, .localGet 0, .ret] := by
  apply literalBody_eq_of_check
  native_decide

/-- The single concrete runtime import used by the literal host call. -/
def abiLiteralImport : Wasm.ImportDecl :=
  abiLiteralAdaptedModule.wasmModule.imports[0]!

theorem abiLiteralImport_found :
    abiLiteralAdaptedModule.wasmModule.imports[0]? = some abiLiteralImport := by
  native_decide

theorem abiLiteralHostsMatch :
    HostsMatch abiLiteralResolvedHosts abiLiteralSourceModule := by
  unfold HostsMatch
  native_decide

theorem abiLiteralHostsSatisfy :
    abiLiteralResolvedHosts.env.Satisfies abiLiteralAdaptedModule.wasmModule
      abiLiteralResolvedHosts.spec :=
  resolvedHosts_satisfy_adapted abiLiteralAdaptedModule_adapted abiLiteralHostsMatch

theorem abiLiteralResolvedHosts_operations :
    abiLiteralResolvedHosts.operations = [.naturalLiteral 42 .tobject] := by
  apply literalOperations_eq_of_check
  native_decide

/-- Handle state after encoding the tagged literal into the initially empty table. -/
def abiLiteralAfterHandles : HandleTable :=
  { entries := [(1, .object (.tagged (UInt64.ofNat 42)))], next := 2 }

/-- Generated locals after storing that handle into the fixture's only slot. -/
def abiLiteralUpdatedLocals : Wasm.Locals :=
  { locals := [.i32 1] }

theorem abiLiteralInitialState_related :
    StateRelated abiLiteralSourceFunction {} []
      (abiLiteralAdaptedModule.wasmModule.initialStore (α := RuntimeHost))
      (abiLiteralMainFunction.toLocals []) := by
  unfold StateRelated
  refine ⟨rfl, rfl, rfl, handleTableInvariant_empty, ?_⟩
  intro fvar value found
  simp [lookup] at found

theorem abiLiteralEncoded :
    (abiLiteralAdaptedModule.wasmModule.initialStore (α := RuntimeHost)).host.handles.encode
      .tobject (.object (.tagged (UInt64.ofNat 42))) =
      .ok (abiLiteralAfterHandles, 1) := by
  rfl

theorem abiLiteralLocalSet :
    (abiLiteralMainFunction.toLocals []).set? 0 (.i32 1) =
      some abiLiteralUpdatedLocals := by
  native_decide

/-- The local W4 proof for the real W3 literal body and concrete initial state. -/
theorem abiLiteralMain_codeWP :
    CodeWP abiLiteralContext abiLiteralSourceModule abiLiteralSourceFunction []
      abiLiteralAdaptedModule.wasmModule abiLiteralResolvedHosts.env
      {} [] abiLiteralCode abiLiteralMainFunction.body
      (abiLiteralAdaptedModule.wasmModule.initialStore (α := RuntimeHost))
      (abiLiteralMainFunction.toLocals []) []
      (ReturnPost {} (.object (.tagged (UInt64.ofNat 42))) .tobject []) := by
  rw [abiLiteralMain_body]
  apply codeWP_naturalLiteral_return
    (spec := abiLiteralResolvedHosts.spec) (id := 0) (imp := abiLiteralImport)
    (decl := abiLiteralDecl) (resultIndex := 0) (value := 42)
    (after := abiLiteralAfterHandles) (handle := 1)
    (updated := abiLiteralUpdatedLocals)
  · rfl
  · have tobjectNotObject :
        (LCNF.ImpureType.tobject == LCNF.ImpureType.object) = false := by
      native_decide
    have tobjectNotTagged :
        (LCNF.ImpureType.tobject == LCNF.ImpureType.tagged) = false := by
      native_decide
    have tobjectSelf :
        (LCNF.ImpureType.tobject == LCNF.ImpureType.tobject) = true := by
      native_decide
    simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind,
      Fir.Wasm.checkedAbiKind, Fir.Wasm.abiKind, Fir.Wasm.abiKind?,
      abiLiteralDecl, letDecl, tobjectType,
      AbiKind.acceptsLiteral, Fir.Wasm.compileLiteral,
      tobjectNotObject, tobjectNotTagged, tobjectSelf]
    rfl
  · simp [Fir.Wasm.getLocal, Fir.Wasm.findLocalKind?, abiLiteralContext,
      abiLiteralDecl, letDecl]
  · native_decide
  · native_decide
  · native_decide
  · exact abiLiteralInitialState_related
  · exact abiLiteralImport_found
  · exact abiLiteralHostsSatisfy
  · native_decide
  · simp [ResolvedHosts.spec, abiLiteralResolvedHosts_operations]
  · native_decide
  · native_decide
  · simpa [literal, maxTaggedPayload] using abiLiteralEncoded
  · exact abiLiteralLocalSet

/-- The concrete W3 result observation is accepted by the comparison policy. -/
theorem abiLiteralObservation_related :
    compareObservations
        (ReturnedObservation {} (.object (.tagged (UInt64.ofNat 42))))
        (.returned (.object (.tagged (UInt64.ofNat 42))) {}) =
      .related
        (ReturnedObservation {} (.object (.tagged (UInt64.ofNat 42))))
        (.returned (.object (.tagged (UInt64.ofNat 42))) {}) := by
  simpa [ReturnedObservation] using compareObservations_returned_empty_tagged_42

/--
Representative W3 instantiation of the exported-function bridge. All lowering,
adaptation, host-resolution, export-index, signature, and observation-policy
facts are discharged for `abiLiteralProgram`; the remaining premise is exactly
its local `CodeWP` body proof.
-/
theorem abiLiteralMain_export_correct_of_codeWP
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {code : Lean.Compiler.LCNF.Code .impure}
    (correct :
      CodeWP context abiLiteralSourceModule sourceFunction []
        abiLiteralAdaptedModule.wasmModule abiLiteralResolvedHosts.env
        {} [] code abiLiteralMainFunction.body
        (abiLiteralAdaptedModule.wasmModule.initialStore (α := RuntimeHost))
        (abiLiteralMainFunction.toLocals []) []
        (ReturnPost {} (.object (.tagged (UInt64.ofNat 42))) .tobject [])) :
    ExportTerminatesWith abiLiteralResolvedHosts.env
      abiLiteralAdaptedModule.wasmModule "main"
      (abiLiteralAdaptedModule.wasmModule.initialStore (α := RuntimeHost)) []
      (RelatedPost #[.tobject]
        (ReturnedObservation {} (.object (.tagged (UInt64.ofNat 42))))) := by
  apply CodeWP.toExportTerminatesWithRelated_of_return
    abiLiteralMain_exported abiLiteralMain_notImport abiLiteralMain_found rfl
    abiLiteralMain_resultCount abiLiteralObservation_related
  simpa using correct

/--
End-to-end W3/W4 theorem for the generated natural-literal fixture: invoking
the actual adapted `main` export terminates and returns an observation related
to source evaluation of `abiLiteralProgram`.
-/
theorem abiLiteralMain_export_correct :
    ExportTerminatesWith abiLiteralResolvedHosts.env
      abiLiteralAdaptedModule.wasmModule "main"
      (abiLiteralAdaptedModule.wasmModule.initialStore (α := RuntimeHost)) []
      (RelatedPost #[.tobject]
        (ReturnedObservation {} (.object (.tagged (UInt64.ofNat 42))))) :=
  abiLiteralMain_export_correct_of_codeWP abiLiteralMain_codeWP

end FirTalos.Correctness
