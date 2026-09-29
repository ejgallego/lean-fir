import FirTalos.ConcreteArrayExternalEvidence
import FirTalos.ConcreteExternalCallRequest
import FirTalos.ConcreteRegionExternal

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Execute empty-Array allocation and the generated destination bind. Allocation,
request decoding, witness extension and both execution paths are conclusions.
The installed handler law and finite headroom remain deployment premises. -/
theorem ConcreteStructuredRegionExternalCall.advance_emptyArray_bind
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
    {callIndex resultIndex capacity remainingBytes : Nat} {source : MachineState}
    {target : StructuredWasmState Host}
    {entryRuntime : RuntimeState} {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} {facts : ReuseCapacityFacts}
    (ready : ConcreteStructuredRegionExternalCall program context
      sourceModule sourceFunction targetModule hosts externals
      entryRuntime entryStore entryWitness facts remainingBytes site operation
      resolvedResultKind targetImport labels continuation callerJoins
      sourceFrames targetStore callerLocals callerRemainder targetRest
      targetFrames witness physicalArgs callIndex resultIndex source target)
    (resultKind : site.resultKind = .object)
    (response : site.response = semanticEmptyArrayResponse sourceRuntime capacity)
    (handler : ∀ concreteArgs,
      decodePhysicalLanes 0 operation.signature.params.toList physicalArgs =
        .ok concreteArgs →
      EmptyArrayHandlerAt targetStore.host.externals
        (concreteExternalRequest operation .object concreteArgs.toArray)
        targetStore.host.runtime capacity)
    (fits : residentArrayAllocationBytes capacity ≤ remainingBytes) :
    ∃ nextStore nextWitness physicalResult sourceAfter targetAfter updated resumedLocals,
      ExecSteps externals 2 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2
        target targetAfter ∧
      callerLocals.set? resultIndex physicalResult = some updated ∧
      resumedLocals = { updated with values := callerRemainder } ∧
      ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals labels
        entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts decl.fvarId)
        (remainingBytes - residentArrayAllocationBytes capacity)
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        nextStore resumedLocals targetRest nextWitness sourceAfter targetAfter ∧
      sourceAfter.joins = callerJoins ∧ sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = targetFrames ∧
      nextStore.host.externals = targetStore.host.externals ∧
      RuntimeStepTransports sourceRuntime nextRuntime targetStore nextStore witness nextWitness := by
  have related := ready.control
  have resolved : resolvedResultKind = .object := by
    have h := congrArg (fun results : Array AbiKind => results[0]?)
      related.resultSignature
    simpa [related.parameterSignature, resultKind] using h.symm
  obtain ⟨concreteArgs, decoded, requestRelated⟩ := related.decodeRequest
  have declarationName : site.name = site.declaration.name :=
    related.operationName.symm.trans related.operationMatches.name
  have requestEq : operation.request site.semanticArgs =
      declarationExternalRequest site.declaration site.semanticArgs := by
    simp [ExternalOperation.request, declarationExternalRequest,
      related.operationName, declarationName, related.operationMatches.paramTypes,
      related.operationMatches.resultType]
  have called : externals.call (operation.request site.semanticArgs) sourceRuntime =
      .ok (semanticEmptyArrayResponse sourceRuntime capacity) := by
    rw [requestEq, ← response]
    exact site.semanticCalled
  obtain ⟨nextStore, nextWitness, physicalResult, evidence, residual⟩ :=
    emptyArrayExternalCallEvidence_of_budget operation targetStore physicalArgs
      concreteArgs site.semanticArgs witness sourceRuntime externals capacity
      remainingBytes decoded related.callerStateRelated.1
      (by simpa [resolved] using requestRelated) (handler concreteArgs decoded)
      called ready.scope.budgetedPureExternal.1.2 fits
  have evidence' : ConcreteExternalCallEvidence operation resolvedResultKind
      targetStore physicalArgs sourceRuntime nextRuntime sourceValue witness
      nextStore nextWitness physicalResult := by
    simpa [resolved, site.nextRuntimeEq, site.sourceValueEq, response, ← requestEq,
      semanticEmptyArrayResponse, arrayExternalResponse] using evidence
  obtain ⟨sourceMid, targetMid, sourceCall, targetCall, bound⟩ :=
    ready.advance_call (cost := residentArrayAllocationBytes capacity) evidence' residual (by
      intro closed
      have allocated := closed.alloc (object := .array #[] capacity)
        (persistent := false) rfl (by simp [HeapObject.ownedValues])
      simpa [site.nextRuntimeEq, response, semanticEmptyArrayResponse,
        arrayExternalResponse, semanticExternalRuntimeAfter, semanticArrayResult,
        semanticArrayCell] using allocated)
  obtain ⟨sourceAfter, targetAfter, updated, resumedLocals, sourceBind, targetBind,
      set, resumed, focus, joins, frames, targetFrames⟩ :=
    bound.advance (externals := externals)
      (module := targetModule.wasmModule) (hostEnv := hosts.env)
  exact ⟨nextStore, nextWitness, physicalResult, sourceAfter, targetAfter, updated,
    resumedLocals, .step sourceCall (.step sourceBind (.refl _)),
    targetCall.trans targetBind, set, resumed, focus, joins, frames,
    targetFrames, evidence.externalsPreserved, evidence'.transports⟩

end FirTalos.Concrete
