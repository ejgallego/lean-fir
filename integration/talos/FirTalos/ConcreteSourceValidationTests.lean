import FirTalos.ConcreteSourceValidation
import FirTalos.Adapter
import Fir.Wasm.Examples

/-!
Executable specification-sensitivity checks, not proof witnesses. Keep fixture
imports out of the reusable validation and supported-export modules.

The dictionary fixture deliberately admits production lowering after losing
local closure provenance. A successful validator must not be confused with
the stronger `WasmSupported` gate used by the proof interface.
-/

open Fir.Wasm

#guard validateSupported dictionaryPureUnderApplyProgram matches .ok ()
#guard lowerSupported dictionaryPureUnderApplyProgram matches .ok _
#guard !closureFlowSafeProgram dictionaryPureUnderApplyProgram
#guard !supportedProgram dictionaryPureUnderApplyProgram

/- Lowering retains duplicate names. Symbolic validation, reached by adaptation,
rejects them even when the collision crosses the external/internal partition. -/
private def duplicateInternalNamesProgram : Fir.LeanIR.ImpureProgram :=
  { scalarIdProgram with decls := scalarIdProgram.decls ++ scalarIdProgram.decls }

private def mixedDuplicateNamesProgram : Fir.LeanIR.ImpureProgram :=
  { scalarIdProgram with decls := scalarIdProgram.decls ++
      scalarIdProgram.decls.map fun decl =>
        { decl with value := .extern { entries := [] } } }

#guard match lowerSupported duplicateInternalNamesProgram with
  | .ok source =>
      (validateModule source matches .error (.duplicateFunction `scalarId)) &&
      (FirTalos.adapt source matches .error (.invalidModule (.duplicateFunction `scalarId)))
  | .error _ => false

#guard match lowerSupported mixedDuplicateNamesProgram with
  | .ok source =>
      (validateModule source matches .error (.duplicateDeclaration `scalarId)) &&
      (FirTalos.adapt source matches .error (.invalidModule (.duplicateDeclaration `scalarId)))
  | .error _ => false
