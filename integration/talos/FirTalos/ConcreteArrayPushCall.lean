import FirTalos.ConcreteArrayPushExternalEvidence
import FirTalos.ConcreteExternalCallRequest

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- The parameter relation reconstructs the exact represented Array receiver
and tagged element, including the physical argument order. -/
theorem ConstructorArgumentsRelated.arrayPushOperands
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    {location : Location} {payload : UInt64}
    (related : ConstructorArgumentsRelated witness [.erased, .object, .tobject]
      physicalArgs [.erased, .object (.heap location), .object (.tagged payload)]) :
    ∃ address word,
      physicalArgs = [physicalOfLane (.word32 Word32.zero),
        physicalOfLane (.word32 address), physicalOfLane (.word32 word)] ∧
      witness.locations.lookup? location = some address ∧
      ValueRel witness .tobject (.word32 word) (.object (.tagged payload)) := by
  cases related with
  | cons erased rest =>
    cases rest with
    | cons receiver rest =>
      cases rest with
      | cons element rest =>
        cases rest
        cases erased <;> rename_i erased <;> cases erased
        cases receiver <;> rename_i receiver <;> cases receiver
        rename_i mapped
        cases mapped with
        | mapped found =>
          cases element <;> rename_i element <;> cases element
          exact ⟨_, _, rfl, found, .tobject ‹_›⟩

/-- Fresh non-full Array push through the existing imported-call and bind
machine rules. Operand addresses are reconstructed, not client premises. -/
theorem ConcreteStructuredExternalCallControl.advance_pushFreshTagged_bind
    {program : Fir.LeanIR.ImpureProgram} {context : Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {externals : ExternalImpl} {nextRuntime : RuntimeState}
    {sourceEnv : Env} {sourceValue : Value} {entry : RuntimeState}
    {capacity : Nat} {payload : UInt64}
    {decl : Compiler.LCNF.LetDecl .impure}
    {site : ExternalCallShape context externals (semanticArrayResult entry #[] capacity)
      sourceEnv decl nextRuntime sourceValue}
    {operation : ExternalOperation} {resolvedResultKind : AbiKind}
    {targetImport : Wasm.ImportDecl} {labels : LabelContext}
    {continuation : Compiler.LCNF.Code .impure} {callerJoins : JoinEnv}
    {sourceFrames : List Frame} {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals} {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program} {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    {callIndex resultIndex remainingBytes : Nat} {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredExternalCallControl program context sourceModule
      sourceFunction targetModule hosts externals site operation resolvedResultKind
      targetImport labels continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames witness physicalArgs callIndex resultIndex
      source target)
    (named : site.name = `Array.push)
    (parameters : site.parameterKinds = #[.erased, .object, .tobject])
    (arguments : site.semanticArgs =
      #[.erased, .object (.heap entry.nextLocation), .object (.tagged payload)])
    (resultKind : site.resultKind = .object)
    (contract : FreshArrayExternalContract externals) (spare : 0 < capacity)
    (handler : ∀ address word concreteArgs,
      physicalArgs = [physicalOfLane (.word32 Word32.zero),
        physicalOfLane (.word32 address), physicalOfLane (.word32 word)] →
      decodePhysicalLanes 0 operation.signature.params.toList physicalArgs =
        .ok concreteArgs →
      witness.locations.lookup? entry.nextLocation = some address →
      ValueRel witness .tobject (.word32 word) (.object (.tagged payload)) →
      ArrayPushInPlaceHandlerAt targetStore.host.externals
        (concreteExternalRequest operation .object concreteArgs.toArray)
        targetStore.host.runtime address word)
    (budget : targetStore.host.runtime.heap.AddressSpaceBudget remainingBytes) :
    ∃ nextStore physicalResult sourceAfter targetAfter updated resumedLocals,
      ExecSteps externals 2 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target targetAfter ∧
      callerLocals.set? resultIndex physicalResult = some updated ∧
      resumedLocals = { updated with values := callerRemainder } ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        nextStore resumedLocals targetRest witness sourceAfter targetAfter ∧
      nextStore.host.runtime.heap.AddressSpaceBudget remainingBytes ∧
      sourceAfter.joins = callerJoins ∧ sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = targetFrames := by
  have resolved : resolvedResultKind = .object := by
    have h := congrArg (fun results : Array AbiKind => results[0]?) related.resultSignature
    simpa [related.parameterSignature, resultKind] using h.symm
  obtain ⟨concreteArgs, decoded, requestRelated⟩ := related.decodeRequest
  have parameterRelated := related.argumentsRelated.ofKindsRefine site.argumentsRefine
  rw [parameters, arguments] at parameterRelated
  obtain ⟨address, word, physicalEq, mapped, tagged⟩ := parameterRelated.arrayPushOperands
  obtain ⟨nextStore, physicalResult, evidence, _cursor, residual⟩ :=
    pushFreshTaggedExternalCallEvidence operation (related.operationName.trans named)
      targetStore physicalArgs concreteArgs witness entry externals contract capacity
      spare payload word tagged address remainingBytes decoded related.callerStateRelated.1
      mapped (by simpa [resolved, arguments] using requestRelated)
      (handler address word concreteArgs physicalEq decoded mapped tagged) budget
  have requestEq : operation.request site.semanticArgs =
      declarationExternalRequest site.declaration site.semanticArgs := by
    have declarationName : site.name = site.declaration.name :=
      related.operationName.symm.trans related.operationMatches.name
    simp [ExternalOperation.request, declarationExternalRequest, related.operationName,
      declarationName, related.operationMatches.paramTypes, related.operationMatches.resultType]
  have called := contract.pushFreshTagged entry operation.paramTypes operation.resultType
    capacity payload spare
  have responseEq : site.response = arrayExternalResponse
      (semanticArrayResult entry #[.object (.tagged payload)] capacity)
      (.object (.heap entry.nextLocation)) := by
    apply Except.ok.inj
    rw [← site.semanticCalled, ← requestEq]
    simpa [ExternalOperation.request, related.operationName, named, arguments] using called
  have runtimeEq : nextRuntime = semanticArrayResult { entry with trace := entry.trace.push {
        name := `Array.push,
        args := #[.erased, .object (.heap entry.nextLocation), .object (.tagged payload)],
        result := .object (.heap entry.nextLocation) } }
        #[.object (.tagged payload)] capacity := by
    rw [site.nextRuntimeEq, responseEq, ← requestEq]
    simp [semanticExternalRuntimeAfter, arrayExternalResponse, semanticArrayResult,
      semanticExternalEvent, ExternalOperation.request, related.operationName, named, arguments]
  have valueEq : sourceValue = .object (.heap entry.nextLocation) := by
    rw [site.sourceValueEq, responseEq]; rfl
  have evidence' : ConcreteExternalCallEvidence operation resolvedResultKind targetStore
      physicalArgs (semanticArrayResult entry #[] capacity) nextRuntime sourceValue witness
      nextStore witness physicalResult := by
    simpa [resolved, runtimeEq, valueEq] using evidence
  obtain ⟨sourceMid, targetMid, sourceCall, targetCall, bound⟩ := related.advance_call evidence'
  obtain ⟨sourceAfter, targetAfter, updated, resumedLocals, sourceBind, targetBind,
      set, resumed, focus, joins, frames, targetFrames⟩ :=
    bound.advance (externals := externals)
      (module := targetModule.wasmModule) (hostEnv := hosts.env)
  exact ⟨nextStore, physicalResult, sourceAfter, targetAfter, updated, resumedLocals,
    .step sourceCall (.step sourceBind (.refl _)), targetCall.trans targetBind,
    set, resumed, focus, residual, joins, frames, targetFrames⟩

end FirTalos.Concrete
