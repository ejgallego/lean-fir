import FirTalos.ConcreteRuntimeAlignment
import FirTalos.ConcreteReuseCapacityCacheCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open FirTalos.Correctness

/-- Lowering retains an external declaration's original source types alongside
its computed ABI. Physical lane compatibility does not replace this metadata. -/
theorem externalImport_metadata
    {declaration : LCNF.Decl .impure} {imp : Fir.Wasm.Import}
    (imported : Fir.Wasm.externalImport declaration = .ok imp) :
    imp.key = .external declaration.name ∧
      imp.externalTypes? = some {
        params := declaration.params.map (·.type), result := declaration.type } ∧
      ExternalTypes.signature {
        params := declaration.params.map (·.type), result := declaration.type } =
          .ok imp.signature := by
  unfold Fir.Wasm.externalImport at imported
  cases signature : ExternalTypes.signature {
      params := declaration.params.map (·.type), result := declaration.type } <;>
    simp [signature, Bind.bind, Except.bind, pure, Except.pure] at imported
  subst imp
  exact ⟨rfl, rfl, rfl⟩

/-- Production lowering and concrete resolution agree on every external call's
original declaration metadata, singleton result and executable host contract.
The import is proved to exist before numeric lookup, so a named internal
function cannot be substituted through the adapter's fallback path. -/
theorem concreteExternalCallsAligned_ofPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module} {target : AdaptedModule} {hosts : ResolvedHosts}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok source)
    (adapted : adapt source = .ok target)
    (resolved : resolveHosts source = .ok hosts) :
    ConcreteExternalCallsAligned program source target hosts := by
  intro name declaration index found external called
  obtain ⟨imp, imported, selected⟩ :=
    LoweredInternalDeclaration.externalImport_at_of_callIndex namesUnique
      (LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered)
      found external called
  obtain ⟨key, metadata, signature⟩ := externalImport_metadata imported
  have declarationName : declaration.name = name := by
    have matching := (Array.find?_eq_some_iff_getElem.mp found).1
    simpa [Fir.LeanIR.Program.findDecl?] using matching
  have externalKey : imp.key = .external name := by
    simpa [declarationName] using key
  obtain ⟨types, resultKind, host, typesSelected, resultSelected, paramsSize,
      hostSelected, hostFunction⟩ :=
    resolveHosts_external_at resolved selected externalKey
  have typesEq : types = {
      params := declaration.params.map (·.type), result := declaration.type } :=
    Option.some.inj (typesSelected.symm.trans metadata)
  let operation : ExternalOperation := {
    name
    paramTypes := types.params
    resultType := types.result
    signature := imp.signature }
  have operationMatches : ExternalOperationMatchesDeclaration operation declaration := {
    name := declarationName.symm
    paramTypes := congrArg ExternalTypes.params typesEq
    resultType := congrArg ExternalTypes.result typesEq
    paramTypesSize := paramsSize
    signature }
  have targetFound := adaptedImport_at adapted selected
  refine ⟨operation, resultKind, importDecl imp, rfl, operationMatches,
    resultSelected, targetFound, ?_, ?_, ?_, ?_⟩
  · exact List.getElem?_eq_some_iff.mp targetFound |>.1
  · simp only [ResolvedHosts.spec, List.getElem?_map, hostSelected,
      Option.map_some, Option.some.injEq]
    unfold FirTalos.Concrete.ResolvedHost.contract
    rw [hostFunction]
    rfl
  · simp [importDecl, operation]
  · simp [importDecl, resultSelected]

end FirTalos.Concrete
