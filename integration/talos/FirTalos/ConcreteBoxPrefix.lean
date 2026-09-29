import FirTalos.ConcreteRegionCode

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- UInt8 boxing is a heap-neutral local transition. The represented operand
and both local indices come from the current compiler/frame relation; no
allocation-success or target-execution premise is required. -/
theorem ConcreteStructuredRegionCodeCore.advance_boxUInt8
    {program : Fir.LeanIR.ImpureProgram} {context : Context}
    {rootCode : Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context rootCode sourceModule
      sourceFunction targetModule hosts)
    {externals : ExternalImpl} {labels : LabelContext}
    {runtime : RuntimeState} {env : Env} {decl : Compiler.LCNF.LetDecl .impure}
    {continuation : Compiler.LCNF.Code .impure} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {code : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    {scalarId : FVarId} {value : UInt8}
    {entryRuntime : RuntimeState} {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    (valueEq : decl.value = .box Compiler.LCNF.ImpureType.uint8 scalarId)
    (valueKind : letValueKind decl = .ok .tagged)
    (scalarCompiled : getLocal context scalarId = .ok (.localGet scalarId, .uint8))
    (annotationKind : checkedAbiKind Compiler.LCNF.ImpureType.uint8 = .ok .uint8)
    (resultCompiled : getLocal context decl.fvarId = .ok (.localGet decl.fvarId, .tagged))
    (sourceLookup : lookup env scalarId = some (.scalar (.uint8 value)))
    (active : ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals
      labels entryRuntime entryStore entryWitness facts bytes runtime env
      (.let decl continuation) store locals code witness source target) :
    ∃ sourceAfter targetAfter resumedLocals rest,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3
        target targetAfter ∧
      ConcreteStructuredRegionCodeCore context sourceModule sourceFunction externals labels
        entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts decl.fvarId) bytes
        runtime (bind env decl.fvarId (.object (.tagged (UInt64.ofNat value.toNat))))
        continuation store resumedLocals rest witness sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  have related := active.focus
  let scalar : BoxedScalar := .uint8 value
  have payloadEq : scalar.payload.toNat = value.toNat := by
    simp [scalar, BoxedScalar.payload]
  have small : scalar.payload.toNat ≤ maxImmediatePayload := by
    have bound := value.toNat_lt_size
    simp [UInt8.size] at bound
    simp [payloadEq, maxImmediatePayload]; omega
  have sourceSmall : scalar.payload.toNat ≤ maxTaggedPayload := by
    simp [maxImmediatePayload, maxTaggedPayload] at *; omega
  let word := Word32.encodeImmediate scalar.payload.toNat small
  let physical := Wasm.Value.i32 (UInt32.ofNat word.value)
  have semanticStep := semanticBox_tagged_eq runtime scalar (by rfl) sourceSmall
  have boxed : boxScalar store.host.runtime.heap scalar =
      .ok (store.host.runtime.heap, word) := by
    rw [boxScalar_of_tagged _ _ (by rfl) sourceSmall,
      encodeTagged_immediate _ _ small]
  obtain ⟨valueCode, targetValue, rest, resultIndex, compiled, adapted, resultFound,
      continuationAdapted, codeEq⟩ := CodeAdaptedWithSuffix.let_eq related.adapted
  have expected := compileLetValue_box valueEq valueKind scalarCompiled annotationKind
  rw [expected] at compiled
  cases Except.ok.inj compiled
  obtain ⟨indices, callIndex, scalarFound, callFound, targetValueEq⟩ :=
    instructions_localGets_call_eq (fvarIds := [scalarId])
      (operation := .box .uint8 .tagged) adapted
  cases scalarFound with
  | cons scalarFound noMore =>
    cases noMore
    rename_i scalarIndex
    subst targetValue
    obtain ⟨index, found, scalarKindAt⟩ := spec.localsAligned scalarCompiled
    rw [scalarFound] at found
    cases Option.some.inj found
    obtain ⟨physicalScalar, scalarLocal, scalarRelated⟩ :=
      related.stateRelated.resolve sourceLookup scalarFound scalarKindAt
    have physicalEq : physicalScalar = physicalOfLane scalar.lane := by
      obtain ⟨actual, kindEq, semanticEq, physicalEq⟩ :=
        PhysicalValueRel.boxedScalar_of_kind (kind := .uint8) scalarRelated
      cases actual <;> simp [BoxedScalar.kind] at kindEq
      simp [BoxedScalar.semanticValue] at semanticEq
      subst_vars
      rfl
    subst physicalScalar
    obtain ⟨index, found, resultKindAt⟩ := spec.localsAligned resultCompiled
    rw [resultFound] at found
    cases Option.some.inj found
    obtain ⟨updated, set, nextAligned⟩ := related.frameAligned.set?
      (nextRuntime := runtime) (nextEnv := bind env decl.fvarId (.object (.tagged scalar.payload)))
      (nextStore := store) (nextWitness := witness) (physical := physical) resultFound
    have valueRelated : PhysicalValueRel witness .tagged physical
        (.object (.tagged scalar.payload)) := .word32 (.tagged (.immediate _ small))
    have nextState := related.stateRelated.bindPhysical resultFound resultKindAt valueRelated set
    rw [related.stateRelated.clearFailure] at nextState
    obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
      spec.boxCall (kind := .uint8) callFound
    have heapEq : replaceHeap store store.host.runtime.heap = store := by
      change clearFailure store = store
      exact related.stateRelated.clearFailure
    have operation : boxStep .uint8 .tobject store [physicalOfLane scalar.lane] =
        .Return [physical] (replaceHeap store store.host.runtime.heap) := by
      change (match decodeBoxedScalar scalar.kind (physicalOfLane scalar.lane) with
        | .ok scalar => match boxScalar store.host.runtime.heap scalar with
          | .ok (heap, word) => Wasm.HostResult.Return [.i32 (UInt32.ofNat word.value)]
              (replaceHeap (clearFailure store) heap)
          | .error failure => trap (clearFailure store) (.runtime failure.toTrap)
        | .error failure => trap (clearFailure store) failure) = _
      rw [decodeBoxedScalar_physicalOfLane]
      change (match boxScalar store.host.runtime.heap scalar with
        | .ok (heap, word) => Wasm.HostResult.Return [.i32 (UInt32.ofNat word.value)]
            (replaceHeap (clearFailure store) heap)
        | .error failure => trap (clearFailure store) (.runtime failure.toTrap)) = _
      rw [boxed]
      rfl
    have step : LetStepSimulates context sourceFunction targetModule.wasmModule hosts.env
        decl [.localGet scalarIndex, .call callIndex] runtime runtime env (.object (.tagged scalar.payload))
        store store locals updated resultIndex witness witness := by
      refine ⟨?_, related.stateRelated, nextState, ?_⟩
      · simp only [SourceLetResult, evalLetValue, valueEq]
        have lookupEq : lookupValue env scalarId = .ok scalar.semanticValue := by
          simp [lookupValue, sourceLookup, scalar, BoxedScalar.semanticValue]
        rw [lookupEq]
        change ((fun result : RuntimeState × Value => (result.1, LetAction.value result.2)) <$>
          box runtime scalar.kind.semanticType scalar.semanticValue) = _
        rw [semanticStep]
        rfl
      · intro rest Q tail continued
        have continued' := continued
        rw [← heapEq] at continued'
        exact wp_box_let tail scalarLocal imported spec.hostsSatisfy inBounds
          contracted params results operation set continued'
    have flat : StructuredWasmFlatProgram targetModule.wasmModule
        ([.localGet scalarIndex, .call callIndex] ++ [.localSet resultIndex]) :=
      .cons (.atomic (by trivial)) (.cons (.importedCall imported)
        (.cons (.atomic (by trivial)) .nil))
    obtain ⟨sourceAfter, targetAfter, sourceStep, path, focus, joins, frames,
        targetFrames⟩ := related.advance_flatLet codeEq continuationAdapted flat step nextAligned
    refine ⟨sourceAfter, targetAfter, { updated with values := locals.values }, rest,
      sourceStep, path, ?_, joins, frames, targetFrames⟩
    simpa [scalar, BoxedScalar.payload] using active.afterLocalBind focus resultFound set

end FirTalos.Concrete
