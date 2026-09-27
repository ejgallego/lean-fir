import FirTalos.ConcretePublicationExecution

/-! Fresh cache publication followed by the compiler-selected destination bind.
The conclusion is the ordinary code core, including its suspended resource
stack and original caller entry, not just a heap or local-value assertion. -/

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Two source steps (publication and binding) match the eight generated target
steps. The post-publication bind focus and resource stack are constructed here;
clients supply neither them nor an execution path. -/
theorem ConcreteStructuredResourceScope.publishFreshCache_bind
    {program : Fir.LeanIR.ImpureProgram} {callerContext calleeContext : Fir.Wasm.Context}
    {callerCode : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts} {externals : ExternalImpl}
    {callerEntryRuntime activeEntryRuntime current : RuntimeState}
    {callerEntryStore activeEntryStore store : Wasm.Store Host}
    {callerEntryWitness activeEntryWitness witness : RefinementWitness}
    {callerFacts calleeFacts : ReuseCapacityFacts} {callerBytes remainingBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals : Wasm.Locals}
    {declaration : Name} {kind functionResult : AbiKind} {physical : Wasm.Value}
    {root : Location} {cacheIndex cacheSetId resultIndex : Nat}
    {result : FVarId} {continuation : Lean.Compiler.LCNF.Code .impure}
    {labels : LabelContext} {callerJoins : JoinEnv} {sourceFrames : List Frame}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    {callerExpectedResult : Option AbiKind} {source : MachineState}
    (spec : ConcreteSupportedFunction program callerContext callerCode sourceModule
      callerFunction targetModule hosts)
    (callerScope : ConcreteStructuredResourceScope callerContext sourceModule
      callerFunction externals callerEntryRuntime callerEntryStore callerEntryWitness
      callerFacts callerBytes activeEntryRuntime callerEnv activeEntryStore callerLocals
      activeEntryWitness)
    (currentScope : ConcreteStructuredResourceScope calleeContext sourceModule
      calleeFunction externals activeEntryRuntime activeEntryStore activeEntryWitness
      calleeFacts remainingBytes current calleeEnv store calleeLocals witness)
    (programEq : calleeContext.program = callerContext.program)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some declaration)
    (signature : (sourceModule.callSignature? (.declaration declaration)).bind
      (·.results[0]?) = some kind)
    (cacheSetCall : callIndex? sourceModule (.runtime (.cacheSet declaration kind)) =
      some cacheSetId)
    (valueRelated : PhysicalValueRel witness kind physical (.object (.heap root)))
    (closed : HeapRegionClosed activeEntryRuntime.nextLocation current.heap)
    (rootBound : activeEntryRuntime.nextLocation ≤ root)
    (sourceProgram : source.program = callerContext.program)
    (sourceControl : source.control = .yielded (.object (.heap root)))
    (sourceRuntime : source.runtime = current)
    (sourceStack : source.frames =
      .cache declaration :: .bind result continuation callerEnv callerJoins :: sourceFrames)
    (adapted : CodeAdaptedWithSuffix callerContext sourceModule callerFunction labels
      continuation rest)
    (resultFound : findFVar? (functionBindings callerFunction) result = some resultIndex)
    (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd = some kind)
    (tail : ConcreteStructuredSuspendedResourceStack externals program
      callerEntryRuntime callerEntryStore callerEntryWitness functionResult callerExpectedResult
      sourceFrames frames) :
    ∃ runtimeAfter sourceAfter targetAfter resumedLocals,
      ExecSteps externals 2 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 8
        ⟨store, .returning (physical :: calleeLocals.values),
          .call 1 callerLocals.values callerLocals
            [.call cacheSetId, .globalSet (2 * cacheIndex + 1),
              .const 1, .globalSet (2 * cacheIndex)] ::
          .label 0 callerLocals.values
            ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames⟩
        targetAfter ∧
      ConcreteStructuredCodeCoreRel program callerContext sourceModule callerFunction
        externals labels callerEntryRuntime callerEntryStore callerEntryWitness
        functionResult callerExpectedResult (eraseReuseCapacityFact callerFacts result)
        remainingBytes (current.setGlobal declaration (.object (.heap root)))
        (bind callerEnv result (.object (.heap root))) continuation
        (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
          (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1))
        resumedLocals rest witness sourceAfter targetAfter ∧
      sourceAfter.joins = callerJoins ∧ sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = frames := by
  obtain ⟨runtimeAfter, operation, restored⟩ :=
    callerScope.publishFreshCache currentScope programEq initializerFound signature
      valueRelated closed rootBound
  let nextRuntime := current.setGlobal declaration (.object (.heap root))
  let nextStore := writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
    (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1)
  let published : MachineState := { source with
    runtime := nextRuntime
    frames := .bind result continuation callerEnv callerJoins :: sourceFrames }
  let targetPublished : StructuredWasmState Host := ⟨nextStore,
    .running { callerLocals with values := physical :: callerLocals.values }
      (.localSet resultIndex :: rest), frames⟩
  have publishStep : executeStep externals source = .next published := by
    simp [executeStep, coreStep, sourceControl, sourceStack, sourceRuntime,
      published, nextRuntime]
  have publicationPath := currentScope.1.1.2.1.publicationFinitePath_of_compiler
    (callerLocals := callerLocals) (calleeLocals := calleeLocals)
    (resultIndex := resultIndex) (rest := rest) (frames := frames)
    spec initializerFound signature cacheSetCall operation
  have bindFocus : ConcreteStructuredExternalBindFocus callerContext sourceModule
      callerFunction labels nextRuntime callerEnv (.object (.heap root)) result
      continuation callerJoins sourceFrames nextStore callerLocals callerLocals.values
      rest frames witness kind physical resultIndex published targetPublished := {
    sourceProgramEq := sourceProgram
    sourceControlEq := sourceControl
    sourceRuntimeEq := rfl
    sourceFramesEq := rfl
    targetStoreEq := rfl
    targetControlEq := rfl
    targetFramesEq := rfl
    continuationAdapted := adapted
    stateRelated := restored.stateRelated
    frameAligned := restored.frameAligned
    resultFound := resultFound
    kindAt := kindAt
    valueRelated := valueRelated }
  have bindCore : ConcreteStructuredExternalBindCoreRel program callerContext sourceModule
      callerFunction externals labels callerEntryRuntime callerEntryStore callerEntryWitness
      functionResult callerExpectedResult callerFacts remainingBytes nextRuntime callerEnv
      (.object (.heap root)) result continuation callerJoins sourceFrames nextStore
      callerLocals callerLocals.values rest frames witness kind physical resultIndex
      published targetPublished := ⟨bindFocus, restored, tail⟩
  let sourceAfter : MachineState := { published with
    control := .code continuation
    env := bind callerEnv result (.object (.heap root)), joins := callerJoins
    frames := sourceFrames }
  have bindStep : executeStep externals published = .next sourceAfter := by
    simp [executeStep, coreStep, published, sourceAfter, sourceControl]
  obtain ⟨targetAfter, resumedLocals, bindPath, codeCore, sourceFramesEq, targetFramesEq⟩ :=
    bindCore.advance_of_step (targetModule := targetModule) (hosts := hosts) bindStep
  exact ⟨runtimeAfter, sourceAfter, targetAfter, resumedLocals,
    .step publishStep (.step bindStep (.refl _)),
    publicationPath.trans bindPath, codeCore, rfl, sourceFramesEq, targetFramesEq⟩

end FirTalos.Concrete
