import RetainedDeclarations
import FirTalos.ConcreteArrayExternal
import FirTalos.ConcreteStructuredSimulation
import FirTalos.ConcreteRetainedTransports
import FirTalos.ConcreteRetainedPublication
import FirTalos.ConcretePublicationScope
import FirTalos.ConcretePublicationExecution
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

def publicationInput (runtime : RuntimeState) : RuntimeState :=
  semanticArrayResult { runtime with
      trace := (runtime.trace.push (mkEmptyEvent runtime)).push (pushEvent runtime) }
    #[.object (.tagged 0)] 5

def resultRuntime (runtime : RuntimeState) : RuntimeState :=
  (publicationInput runtime).setGlobal name (.object (.heap runtime.nextLocation))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem reaches_published_withFrames
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    (frames : List Frame) :
    ∃ final,
      run 12 externals { initialState RetainedRC2.program name #[] runtime with frames } =
        .outOfFuel final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = frames ∧ final.program = RetainedRC2.program := by
  have boxed (state : RuntimeState) :
      box state (.const `UInt8 []) (.scalar (.uint8 0)) =
        .ok (state, .object (.tagged 0)) := by
    exact semanticBox_tagged_eq state (.uint8 0) rfl (by decide)
  have pushed := contract.pushFreshTagged
    { runtime with trace := runtime.trace.push (mkEmptyEvent runtime) }
    (pushDecl.params.map (·.type)) pushDecl.type 5 0 (by decide)
  simp only [pushDecl, mkEmptyEvent, semanticArrayResult, arrayExternalResponse] at pushed
  simp [initialState, run, executeStep, coreStep, invokeDecl,
    RetainedRC2.initializer.findDecl, mkEmptyDecl.findDecl, pushDecl.findDecl,
    RetainedRC2.initializer, mkEmptyDecl, pushDecl, bindParams, evalLetValue,
    evalArgs, evalArg, lookupValue, lookup, Fir.LeanIR.Impure.bind, literal, pushBindFrame,
    MachineState.withValue, resumeExternal, observe, cold, name,
    Pure.pure, Bind.bind, Except.pure, Except.bind, maxTaggedPayload,
    contract.mkEmpty, boxed, arrayExternalResponse, semanticArrayResult,
    resultRuntime, publicationInput, mkEmptyEvent, pushEvent] at *
  simp only [pushed]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem reaches_publicationInput_withFrames
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    (frames : List Frame) :
    ∃ final,
      run 11 externals { initialState RetainedRC2.program name #[] runtime with frames } =
        .outOfFuel final ∧
      final.runtime = publicationInput runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = .cache name :: frames ∧ final.program = RetainedRC2.program := by
  have boxed (state : RuntimeState) :
      box state (.const `UInt8 []) (.scalar (.uint8 0)) =
        .ok (state, .object (.tagged 0)) := by
    exact semanticBox_tagged_eq state (.uint8 0) rfl (by decide)
  have pushed := contract.pushFreshTagged
    { runtime with trace := runtime.trace.push (mkEmptyEvent runtime) }
    (pushDecl.params.map (·.type)) pushDecl.type 5 0 (by decide)
  simp only [pushDecl, mkEmptyEvent, semanticArrayResult, arrayExternalResponse] at pushed
  simp [initialState, run, executeStep, coreStep, invokeDecl,
    RetainedRC2.initializer.findDecl, mkEmptyDecl.findDecl, pushDecl.findDecl,
    RetainedRC2.initializer, mkEmptyDecl, pushDecl, bindParams, evalLetValue,
    evalArgs, evalArg, lookupValue, lookup, Fir.LeanIR.Impure.bind, literal, pushBindFrame,
    MachineState.withValue, resumeExternal, observe, cold, name,
    Pure.pure, Bind.bind, Except.pure, Except.bind, maxTaggedPayload,
    contract.mkEmpty, boxed, arrayExternalResponse, semanticArrayResult,
    resultRuntime, publicationInput, mkEmptyEvent, pushEvent] at *
  simp only [pushed]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem reaches_published
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none) :
    ∃ final,
      run 12 externals (initialState RetainedRC2.program name #[] runtime) =
        .outOfFuel final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = [] := by
  obtain ⟨final, execution, runtimeEq, control, frames, _⟩ :=
    reaches_published_withFrames externals contract runtime cold []
  exact ⟨final, execution, runtimeEq, control, frames⟩

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

/-- The body supplies one entry-indexed law for every represented historical
caller. Clients no longer need to select a saved fact map for this endpoint. -/
theorem evaluates_and_retainsCallers
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    {heap : MemoryState} {witness : RefinementWitness}
    (related : LiveHeapRel heap witness runtime) :
    ∃ final,
      ExecSteps externals 12 (initialState RetainedRC2.program name #[] runtime) final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = [] ∧
      RetainedCallerTransport witness runtime final.runtime := by
  obtain ⟨final, execution, runtimeEq, control, frames⟩ :=
    reaches_published externals contract runtime cold
  refine ⟨final, execSteps_of_run_outOfFuel execution, runtimeEq, control, frames, ?_⟩
  rw [runtimeEq]
  exact RetainedCallerTransport.freshArrayPublication related 5 0 name

/-- Connect the checked body's source result to executable concrete cache
publication and the cumulative resource transport. No graph closure or
caller-specific publication certificate is supplied: the checked final heap
shape and entry representation establish freshness. The concrete callee prefix
is still explicit in `history` and `currentRelated`; this is not its execution
proof or central lazy-miss admission. -/
theorem executes_and_publishesCache
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    {entryStore store : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {kind : Fir.Wasm.AbiKind}
    {physical : Wasm.Value} {slot : ConcreteGlobalSlot}
    (history : RetainedCodeEntryTransports runtime (publicationInput runtime)
      entryStore store entryWitness witness)
    (entryRelated : LiveHeapRel entryStore.host.runtime.heap entryWitness runtime)
    (currentRelated : ConcreteRuntimeRel store.host.runtime witness (publicationInput runtime))
    (valueRelated : PhysicalValueRel witness kind physical
      (.object (.heap runtime.nextLocation)))
    (found : store.host.runtime.globals.find? name = some slot)
    (kindEq : slot.kind = kind)
    (descriptorsEq : store.host.closureDescriptors = witness.closureDescriptors)
    (cacheIndex : Nat) :
    ∃ before final runtimeAfter,
      ExecSteps externals 11 (initialState RetainedRC2.program name #[] runtime) before ∧
      before.runtime = publicationInput runtime ∧
      executeStep externals before = .next final ∧
      ExecSteps externals 12 (initialState RetainedRC2.program name #[] runtime) final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = [] ∧
      cacheSetStep name kind store [physical] =
        .Return [physical] (replaceRuntime store runtimeAfter) ∧
      let nextStore := writeWasmGlobal
        (writeWasmGlobal (replaceRuntime store runtimeAfter)
          (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)
      ConcreteRuntimeRel nextStore.host.runtime witness final.runtime ∧
      RetainedCodeEntryTransports runtime final.runtime entryStore nextStore entryWitness witness := by
  have closed : HeapRegionClosed runtime.nextLocation (publicationInput runtime).heap := by
    apply (HeapRegionClosed.of_liveHeapRel entryRelated).alloc
      (object := .array #[.object (.tagged 0)] 5) (persistent := false)
      (after := semanticArrayResult runtime #[.object (.tagged 0)] 5) rfl
    simp [HeapObject.ownedValues]
  obtain ⟨runtimeAfter, operation, runtimeRelated, transported⟩ :=
    history.publishFreshCache entryRelated currentRelated valueRelated found
      kindEq descriptorsEq closed (Nat.le_refl _) cacheIndex
  obtain ⟨before, execution, runtimeEq, control, frames, _⟩ :=
    reaches_publicationInput_withFrames externals contract runtime cold []
  let final : MachineState := { before with
    runtime := resultRuntime runtime
    control := .yielded (.object (.heap runtime.nextLocation))
    frames := [] }
  have sourceStep : executeStep externals before = .next final := by
    simp [executeStep, coreStep, control, frames, runtimeEq, final, resultRuntime]
  have sourcePrefix := execSteps_of_run_outOfFuel execution
  refine ⟨before, final, runtimeAfter, sourcePrefix, runtimeEq, sourceStep,
    execSteps_trans_exact sourcePrefix (.step sourceStep (.refl _)),
    rfl, rfl, rfl, operation, ?_, ?_⟩
  · exact runtimeRelated
  · exact transported

/-- The checked initializer's publication step restores the caller's full
entry-relative resource scope. The source run supplies graph construction;
the scopes supply cache layout, host contracts and saved caller resources.
The target callee prefix and destination bind remain separate obligations. -/
theorem executes_and_restoresCallerScope
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    {callerContext calleeContext : Fir.Wasm.Context} {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {callerEntryRuntime : RuntimeState} {callerEntryStore entryStore store : Wasm.Store Host}
    {callerEntryWitness entryWitness witness : RefinementWitness}
    {callerFacts calleeFacts : Fir.Wasm.ReuseCapacityFacts} {callerBytes remainingBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals : Wasm.Locals}
    {kind : Fir.Wasm.AbiKind} {physical : Wasm.Value} {cacheIndex : Nat}
    (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
      callerFunction externals callerEntryRuntime callerEntryStore callerEntryWitness
      callerFacts callerBytes runtime callerEnv entryStore callerLocals entryWitness)
    (currentScope : ConcreteStructuredResourceScope calleeContext sourceModule
      calleeFunction externals runtime entryStore entryWitness calleeFacts remainingBytes
      (publicationInput runtime) calleeEnv store calleeLocals witness)
    (programEq : calleeContext.program = callerContext.program)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some name)
    (signature : (sourceModule.callSignature? (.declaration name)).bind
      (·.results[0]?) = some kind)
    (valueRelated : PhysicalValueRel witness kind physical
      (.object (.heap runtime.nextLocation))) :
    ∃ before final runtimeAfter,
      ExecSteps externals 11 (initialState RetainedRC2.program name #[] runtime) before ∧
      before.runtime = publicationInput runtime ∧
      executeStep externals before = .next final ∧
      ExecSteps externals 12 (initialState RetainedRC2.program name #[] runtime) final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = [] ∧
      cacheSetStep name kind store [physical] =
        .Return [physical] (replaceRuntime store runtimeAfter) ∧
      ConcreteStructuredResourceScope callerContext sourceModule callerFunction externals
        callerEntryRuntime callerEntryStore callerEntryWitness callerFacts remainingBytes
        final.runtime callerEnv
        (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
          (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)) callerLocals witness := by
  obtain ⟨slot, found, kindEq⟩ := currentScope.1.1.2.1.hostSlot initializerFound signature
  obtain ⟨before, final, runtimeAfter, sourcePrefix, beforeEq, step, execution, finalEq,
      control, frames, operation, related, history⟩ :=
    executes_and_publishesCache externals contract runtime cold currentScope.transports
      callerScope.stateRelated.1.heap currentScope.stateRelated.1 valueRelated found kindEq
      currentScope.1.1.1.2 cacheIndex
  refine ⟨before, final, runtimeAfter, sourcePrefix, beforeEq, step, execution, finalEq,
    control, frames, operation, ?_⟩
  rw [finalEq] at related history ⊢
  exact callerScope.afterCachePublication currentScope programEq initializerFound signature
    valueRelated operation related history

/-- The checked source publication paired with the generated Wasm publication
suffix and full caller-scope restoration. The supported caller belongs to the
same checked program. Neither a target path nor global-lane existence is a
premise. Target initializer execution and destination binding are not covered. -/
theorem executes_publicationSuffix
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    {callerContext calleeContext : Fir.Wasm.Context} {sourceModule : Fir.Wasm.Module}
    {callerCode : LCNF.Code .impure} {callerFunction calleeFunction : Fir.Wasm.Function}
    {target : FirTalos.AdaptedModule} {hosts : ResolvedHosts}
    {callerEntryRuntime : RuntimeState} {callerEntryStore entryStore store : Wasm.Store Host}
    {callerEntryWitness entryWitness witness : RefinementWitness}
    {callerFacts calleeFacts : Fir.Wasm.ReuseCapacityFacts} {callerBytes remainingBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals : Wasm.Locals}
    {kind : Fir.Wasm.AbiKind} {physical : Wasm.Value} {cacheIndex cacheSetId resultIndex : Nat}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    (spec : ConcreteSupportedFunction RetainedRC2.program callerContext callerCode
      sourceModule callerFunction target hosts)
    (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
      callerFunction externals callerEntryRuntime callerEntryStore callerEntryWitness
      callerFacts callerBytes runtime callerEnv entryStore callerLocals entryWitness)
    (currentScope : ConcreteStructuredResourceScope calleeContext sourceModule
      calleeFunction externals runtime entryStore entryWitness calleeFacts remainingBytes
      (publicationInput runtime) calleeEnv store calleeLocals witness)
    (programEq : calleeContext.program = callerContext.program)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some name)
    (signature : (sourceModule.callSignature? (.declaration name)).bind
      (·.results[0]?) = some kind)
    (cacheSetCall : FirTalos.callIndex? sourceModule (.runtime (.cacheSet name kind)) =
      some cacheSetId)
    (valueRelated : PhysicalValueRel witness kind physical
      (.object (.heap runtime.nextLocation))) :
    ∃ before final runtimeAfter,
      ExecSteps externals 11 (initialState RetainedRC2.program name #[] runtime) before ∧
      before.runtime = publicationInput runtime ∧
      executeStep externals before = .next final ∧
      ExecSteps externals 12 (initialState RetainedRC2.program name #[] runtime) final ∧
      final.runtime = resultRuntime runtime ∧
      final.control = .yielded (.object (.heap runtime.nextLocation)) ∧
      final.frames = [] ∧
      let nextStore := writeWasmGlobal
        (writeWasmGlobal (replaceRuntime store runtimeAfter) (2 * cacheIndex + 1) physical)
        (2 * cacheIndex) (.i32 1)
      FinitePath (StructuredWasmStep target.wasmModule hosts.env) 7
        ⟨store, .returning (physical :: calleeLocals.values),
          .call 1 callerLocals.values callerLocals
            [.call cacheSetId, .globalSet (2 * cacheIndex + 1),
              .const 1, .globalSet (2 * cacheIndex)] ::
          .label 0 callerLocals.values
            ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames⟩
        ⟨nextStore, .running { callerLocals with values := physical :: callerLocals.values }
          (.localSet resultIndex :: rest), frames⟩ ∧
      ConcreteStructuredResourceScope callerContext sourceModule callerFunction externals
        callerEntryRuntime callerEntryStore callerEntryWitness callerFacts remainingBytes
        final.runtime callerEnv nextStore callerLocals witness := by
  obtain ⟨before, final, runtimeAfter, sourcePrefix, beforeEq, step, execution,
      finalEq, control, sourceFrames, operation, restored⟩ :=
    executes_and_restoresCallerScope externals contract runtime cold callerScope
      currentScope programEq initializerFound signature valueRelated
  exact ⟨before, final, runtimeAfter, sourcePrefix, beforeEq, step, execution,
    finalEq, control, sourceFrames,
    currentScope.1.1.2.1.publicationFinitePath_of_compiler spec initializerFound
      signature cacheSetCall operation, restored⟩

/-- The caller state after binding the published result. The initializer's
temporary environment and join environment are not retained. -/
noncomputable def resumedCaller (runtime : RuntimeState) (env : Env) (result : FVarId)
    (continuation : LCNF.Code .impure) (joins : JoinEnv) (frames : List Frame) :
    MachineState :=
  { program := RetainedRC2.program, runtime := resultRuntime runtime,
    control := .code continuation,
    env := bind env result (.object (.heap runtime.nextLocation)), joins, frames }

/-- The actual cold initializer executes under a waiting caller and binds its
result. No body-execution, graph-separation or ordinary-binding premise is
supplied; the remaining external and representation premises are explicit. -/
theorem resumesCaller
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (cold : findGlobal? runtime.globals name = none)
    (env : Env) (result : FVarId) (continuation : LCNF.Code .impure)
    (joins : JoinEnv) (frames : List Frame)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {bindings : List (FVarId × Fir.Wasm.AbiKind)}
    {locals : Wasm.Locals} {savedHeap heap : MemoryState}
    {savedWitness witness : RefinementWitness}
    (saved : ReuseCapacityFactsRel facts bindings env locals savedHeap savedWitness)
    (transport : WitnessTransport savedWitness witness)
    (related : LiveHeapRel heap witness runtime) :
    ExecSteps externals 13
      { initialState RetainedRC2.program name #[] runtime with
        frames := .bind result continuation env joins :: frames }
      (resumedCaller runtime env result continuation joins frames) ∧
    ReuseTokenOrdinaryBindTransport facts result runtime (resultRuntime runtime)
      env (.object (.heap runtime.nextLocation)) := by
  obtain ⟨final, execution, runtimeEq, control, stack, program⟩ :=
    reaches_published_withFrames externals contract runtime cold
      (.bind result continuation env joins :: frames)
  have pop : executeStep externals final =
      .next (resumedCaller runtime env result continuation joins frames) := by
    simp only [executeStep, coreStep, control, stack]
    cases final
    simp_all [resumedCaller]
  exact ⟨execSteps_trans_exact
    (execSteps_of_run_outOfFuel execution) (.step pop (.refl _)),
    (freshEmptyArray_pushTagged_publication saved transport related 5 0 name).eraseBind⟩

/-- Connect execution of the checked body to the existing concrete caller-pop
consumer. The target is already at its return boundary: target callee execution,
its final frame and representation transports are still independent premises.
The source prefix and ordinary-binding premise are derived here. -/
theorem return_pop_preservesCaller
    {context calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction calleeFunction : Fir.Wasm.Function}
    {labels : FirTalos.LabelContext} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {outerRuntime runtime : RuntimeState}
    {outerStore callStore targetStore : Wasm.Store Host}
    {outerWitness callWitness witness : RefinementWitness}
    {callerEnv calleeEnv : Env} {result : FVarId}
    {continuation : LCNF.Code .impure} {callerJoins : JoinEnv}
    {sourceFrames : List Frame} {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program} {targetFrames : List StructuredWasmFrame}
    {kind callerFunctionResult : Fir.Wasm.AbiKind} {physical : Wasm.Value}
    {resultIndex : Nat} {source : MachineState} {target : StructuredWasmState Host}
    {tailResult : Option Fir.Wasm.AbiKind}
    {facts calleeFacts : Fir.Wasm.ReuseCapacityFacts} {callerBytes resultBytes : Nat}
    (contract : FreshArrayExternalContract externals)
    (cold : findGlobal? runtime.globals name = none)
    (checked : context.program = RetainedRC2.program)
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels (resultRuntime runtime) callerEnv
      (.object (.heap runtime.nextLocation)) result continuation callerJoins
      sourceFrames targetStore callerLocals callerRemainder targetRest
      targetFrames returnedTail witness kind physical resultIndex source target)
    (callerScope : ConcreteStructuredResourceScope context sourceModule
      sourceFunction externals outerRuntime outerStore outerWitness facts
      callerBytes runtime callerEnv callStore callerLocals callWitness)
    (callee : ConcreteReuseCapacityCacheAbiFrame calleeContext sourceModule
      calleeFunction externals calleeFacts resultBytes (resultRuntime runtime)
      calleeEnv targetStore calleeLocals witness)
    (witnessTransport : WitnessTransport callWitness witness)
    (capacityTransport : HeaderCapacityTransport callStore.host.runtime.heap
      targetStore.host.runtime.heap callWitness)
    (programEq : calleeContext.program = context.program)
    (tail : ConcreteStructuredSuspendedResourceStack externals context.program
      outerRuntime outerStore outerWitness callerFunctionResult tailResult
      sourceFrames targetFrames) :
    ∃ targetAfter resumedLocals,
      ExecSteps externals 13
        { initialState RetainedRC2.program name #[] runtime with
          frames := .bind result continuation callerEnv callerJoins :: sourceFrames }
        (resumedCaller runtime callerEnv result continuation callerJoins sourceFrames) ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredStackRel
        (resumedCaller runtime callerEnv result continuation callerJoins sourceFrames)
        targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        (resultRuntime runtime) (bind callerEnv result (.object (.heap runtime.nextLocation)))
        continuation targetStore resumedLocals targetRest witness
        (resumedCaller runtime callerEnv result continuation callerJoins sourceFrames)
        targetAfter ∧
      ConcreteReuseCapacityCacheAbiFrame context sourceModule sourceFunction
        externals (Fir.Wasm.eraseReuseCapacityFact facts result) resultBytes
        (resultRuntime runtime) (bind callerEnv result (.object (.heap runtime.nextLocation)))
        targetStore resumedLocals witness ∧
      targetAfter.frames = targetFrames := by
  have saved := callerScope.1.1.stateRelated
  obtain ⟨sourceSteps, ordinary⟩ := resumesCaller externals contract runtime cold
    callerEnv result continuation callerJoins sourceFrames saved.2
    (WitnessTransport.refl callWitness) saved.1.1.heap
  obtain ⟨sourceAfter, targetAfter, resumedLocals, _sourceStep, path,
      stack, focus, restored, joinsEq, framesEq, targetFramesEq⟩ :=
    related.advance_popRetainedCache (module := module) (hostEnv := hostEnv)
      callerScope callee witnessTransport capacityTransport ordinary programEq tail
  have afterEq : sourceAfter =
      resumedCaller runtime callerEnv result continuation callerJoins sourceFrames := by
    have program := focus.sourceProgramEq.trans checked
    have control := focus.sourceControlEq
    have env := focus.sourceEnvEq
    have state := focus.sourceRuntimeEq
    cases sourceAfter
    simp_all only [resumedCaller]
  subst sourceAfter
  exact ⟨targetAfter, resumedLocals, sourceSteps, path, stack, focus, restored,
    targetFramesEq⟩

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

/-- Fresh publication violates the old all-location condition: the absent
entry cell vacuously counts as ordinary there. This does not refute preservation
of represented caller tokens, which cannot point to that fresh location. -/
theorem example_not_blanketOrdinary :
    ¬ OrdinaryPersistenceTransport {} (resultRuntime {}) := by
  intro ordinary
  have impossible := ordinary 0
    { object := .array #[.object (.tagged 0)] 5, rc := 0, persistent := true }
    example_result_contents (by intro cell found; cases found)
  cases impossible

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
  for endpoint in #[`RetainedInitializer.reaches_published_withFrames,
      `RetainedInitializer.reaches_publicationInput_withFrames,
      `RetainedInitializer.reaches_published,
      `RetainedInitializer.evaluates_and_preservesCaller,
      `RetainedInitializer.evaluates_and_retainsCallers,
      `RetainedInitializer.resumesCaller,
      `RetainedInitializer.return_pop_preservesCaller,
      `RetainedInitializer.executable_example] do
    FirTalos.TrustAudit.check endpoint expected
  -- Concrete cache publication additionally consumes the already audited
  -- byte-assembly theorem; source-only consumers above do not inherit it.
  FirTalos.TrustAudit.check `RetainedInitializer.executes_and_publishesCache
    (expected ++ #["_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
  FirTalos.TrustAudit.check `RetainedInitializer.executes_and_restoresCallerScope
    (expected ++ #["_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
  FirTalos.TrustAudit.check `RetainedInitializer.executes_publicationSuffix
    (expected ++ #["_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
  FirTalos.TrustAudit.check `RetainedInitializer.example_result_contents #["propext"]
  FirTalos.TrustAudit.check `RetainedInitializer.example_not_blanketOrdinary #["propext"]
