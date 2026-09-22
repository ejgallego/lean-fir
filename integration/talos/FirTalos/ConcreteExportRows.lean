import FirTalos.ConcreteReuseCapacityCacheCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm

/-- Production lowering exports every generated function in function-table
order. This is a source-module equation, independent of target execution or
the string rendering of declaration names. -/
theorem lower_exports_eq_functionNames
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source) :
    source.exports = source.functions.map (·.name) := by
  have functionsEq := LoweredInternalDeclaration.functions_of_lower lowered
  change program.decls.filterMapM
      (Fir.Wasm.lowerDeclWithClosureCandidates program
        (Fir.Wasm.cachedDeclarationNames program) none) =
      .ok source.functions at functionsEq
  unfold Fir.Wasm.lower Fir.Wasm.lowerWithClosureTargetFilter at lowered
  simp only [Option.map, functionsEq, Bind.bind, Except.bind] at lowered
  by_cases operations :
      (Fir.Wasm.collectRuntimeOps source.functions).all
        Fir.Wasm.RuntimeOp.abiWellFormed = true
  · simp only [operations, ↓reduceIte] at lowered
    split at lowered
    · contradiction
    · simp only [pure, Except.pure, Except.ok.injEq] at lowered
      exact (congrArg Fir.Wasm.Module.exports lowered).symm
  · simp [operations] at lowered

section Generated

variable
    {program : Fir.LeanIR.ImpureProgram} {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context} {code : LCNF.Code .impure}
    {source : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      code source sourceFunction target)

/-- The generated declaration occupies its own source export row, with its
exact source name rather than a caller-supplied export identifier. -/
theorem ConcreteGeneratedInternalDeclaration.sourceExport_at
    (lowered : Fir.Wasm.lower program = .ok source) :
    source.exports[row.sourceFunctionIndex]? = some declaration.name := by
  rw [lower_exports_eq_functionNames lowered]
  simp [Array.getElem?_map, row.sourceFunctionFound, row.sourceFunctionName]

include row in
/-- Every production-generated internal declaration is a symbolic export. -/
theorem ConcreteGeneratedInternalDeclaration.sourceExport_mem
    (lowered : Fir.Wasm.lower program = .ok source) :
    declaration.name ∈ source.exports :=
  Array.mem_of_getElem? (row.sourceExport_at lowered)

/-- The adapter's executable function-name lookup recovers the exact generated
row. Name uniqueness excludes an external import with the same declaration
name; the retained call-index equation then determines the numeric row. -/
theorem ConcreteGeneratedInternalDeclaration.sourceFunctionIndex_of_lower
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lower program = .ok source) :
    source.functions.findIdx? (·.name == declaration.name) =
      some row.sourceFunctionIndex := by
  have noImport := LoweredInternalDeclaration.findImportTarget?_eq_none
    namesUnique lowered row.declarationFound row.declarationBody
  have called := row.callIndexEq
  simp only [callIndex?, noImport,
    findFunctionTarget?, row.targetFunctionIndex_eq] at called
  cases selected : source.functions.findIdx? (·.name == declaration.name) with
  | none => simp [selected] at called
  | some index =>
      have same : index = row.sourceFunctionIndex := by
        simpa [selected] using called
      simp [same]

end Generated

end FirTalos.Concrete
