import FirTalos.ConcreteStructuredSimulation

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- A staged call's represented arguments decode at the declaration's parameter
kinds. Directional refinement, not physical-lane compatibility, justifies the
widening; the source values and physical arguments are unchanged. -/
theorem ConcreteStructuredExternalCallControl.decodeRequest
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {externals : ExternalImpl} {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env} {sourceValue : Value}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {site : ExternalCallShape context externals sourceRuntime sourceEnv decl
      nextRuntime sourceValue}
    {operation : ExternalOperation} {resolvedResultKind : AbiKind}
    {targetImport : Wasm.ImportDecl} {labels : LabelContext}
    {continuation : Lean.Compiler.LCNF.Code .impure} {callerJoins : JoinEnv}
    {sourceFrames : List Frame} {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals} {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program} {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    {callIndex resultIndex : Nat} {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredExternalCallControl program context
      sourceModule sourceFunction targetModule hosts externals site operation
      resolvedResultKind targetImport labels continuation callerJoins
      sourceFrames targetStore callerLocals callerRemainder targetRest
      targetFrames witness physicalArgs callIndex resultIndex source target) :
    ∃ concreteArgs : List LaneValue,
      decodePhysicalLanes 0 operation.signature.params.toList physicalArgs =
        .ok concreteArgs ∧
      ConcreteExternalRequestRel witness
        (concreteExternalRequest operation resolvedResultKind concreteArgs.toArray)
        (operation.request site.semanticArgs) := by
  obtain ⟨concreteArgs, decoded, concreteLength, semanticLength, concreteRelated⟩ :=
    (related.argumentsRelated.ofKindsRefine site.argumentsRefine).decodePhysicalLanes 0
  refine ⟨concreteArgs, ?_, ?_⟩
  · simpa [related.parameterSignature] using decoded
  · refine {
      name := rfl
      paramTypes := rfl
      resultType := rfl
      paramTypesSize := related.operationMatches.paramTypesSize
      paramKindsSize := ?_
      argsSize := ?_
      arguments := ?_ }
    · change operation.signature.params.size = site.semanticArgs.size
      rw [related.parameterSignature]
      simpa using semanticLength.symm
    · change concreteArgs.toArray.size = site.semanticArgs.size
      simpa using concreteLength.trans semanticLength.symm
    · intro index kind lane semantic kindAt laneAt semanticAt
      change operation.signature.params[index]? = some kind at kindAt
      change concreteArgs.toArray[index]? = some lane at laneAt
      change site.semanticArgs[index]? = some semantic at semanticAt
      exact concreteRelated index kind lane semantic
        (by rw [related.parameterSignature] at kindAt; simpa using kindAt)
        (by simpa using laneAt) (by simpa using semanticAt)

end FirTalos.Concrete
