import FirTalos.ConcreteReuseCapacityCacheCorrectness

namespace FirTalos.Concrete

open Lean Fir.Wasm FirTalos.Correctness

/-- Recover the actual local-collection/refinement run behind an arbitrary
generated declaration row. Name uniqueness identifies the same emitted
function; no additional local-layout certificate is required. -/
theorem ConcreteGeneratedInternalDeclaration.loweredLocals
    {program : Fir.LeanIR.ImpureProgram} {declaration : Lean.Compiler.LCNF.Decl .impure}
    {context : Context} {code : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (row : ConcreteGeneratedInternalDeclaration program declaration context code
      sourceModule sourceFunction target)
    (namesUnique : program.NamesUnique)
    (lowered : lowerSupported program = .ok sourceModule) :
    ∃ actual : LoweredInternalDeclaration program (cachedDeclarationNames program)
        declaration code sourceFunction,
      context.localKinds = actual.context.localKinds := by
  have ordinary := LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered
  obtain ⟨index, function, found, ⟨actual⟩⟩ :=
    LoweredInternalDeclaration.exists_of_lower ordinary row.declarationFound row.declarationBody
  have unique := LoweredInternalDeclaration.functionNamesNodup namesUnique ordinary
  have selectedName : (sourceModule.functions.toList.map (·.name))[row.sourceFunctionIndex]? =
      some declaration.name := by
    rw [List.getElem?_map]
    have selected : sourceModule.functions.toList[row.sourceFunctionIndex]? =
        some sourceFunction := by simpa using row.sourceFunctionFound
    simp [selected, row.sourceFunctionName]
  have actualName : (sourceModule.functions.toList.map (·.name))[index]? =
      some declaration.name := by
    rw [List.getElem?_map]
    have selected : sourceModule.functions.toList[index]? = some function := by simpa using found
    simp [selected, actual.sourceFunctionName]
  have bounds := (Array.getElem?_eq_some_iff.mp row.sourceFunctionFound).1
  have indexEq : row.sourceFunctionIndex = index := by
    apply (List.getElem?_inj (by simpa using bounds) unique).mp
    rw [selectedName, actualName]
  have functionEq : sourceFunction = function := by
    apply Option.some.inj
    rw [← row.sourceFunctionFound, indexEq, found]
  subst function
  exact ⟨actual, row.localKindsExact.trans actual.localKindsExact.symm⟩

end FirTalos.Concrete
