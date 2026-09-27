import FirTalos.ConcreteStructuredSimulation

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Stage an actual lazy-call let without assuming its source transition.
Production compilation/adaptation supplies the cache, call and destination
indices and target suffix; the target itself stutters during this source step. -/
theorem ConcreteStructuredCodeFocus.stageLazyCall
    {context : Context} {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} {runtime : RuntimeState} {env : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {continuation : Lean.Compiler.LCNF.Code .impure}
    {declaration : Name} {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {kind : AbiKind} {store : Wasm.Store Host} {locals : Wasm.Locals}
    {code : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host} {externals : ExternalImpl}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
      runtime env (.let decl continuation) store locals code witness source target)
    (call : LazyCacheCallSupported context decl declaration sourceDeclaration kind)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (aligned : LocalLayoutAligned context sourceFunction) :
    ∃ sourceAfter cacheIndex declarationId cacheSetId resultIndex rest,
      executeStep externals source = .next sourceAfter ∧
      ConcreteStructuredLazyCallReadyFocus context sourceModule sourceFunction labels
        call generated runtime env continuation source.joins source.frames store locals rest
        target.frames witness cacheIndex declarationId cacheSetId resultIndex sourceAfter target := by
  have valueEq : decl.value = .fap declaration #[] := by cases call; assumption
  let staged : MachineState := {
    source with
      control := .invokeName declaration #[]
      frames := .bind decl.fvarId continuation source.env source.joins :: source.frames }
  have sourceStep : executeStep externals source = .next staged := by
    simp [executeStep, coreStep, related.sourceControlEq, evalLetValue, valueEq,
      evalArgs, Bind.bind, Except.bind, pure, Except.pure, pushBindFrame, staged]
  obtain ⟨cacheIndex, declarationId, cacheSetId, resultIndex, rest, _, ready⟩ :=
    related.advance_lazy_stage (module := default) (hostEnv := default)
      call generated aligned sourceStep
  exact ⟨staged, cacheIndex, declarationId, cacheSetId, resultIndex, rest, sourceStep, ready⟩

/-- A generated internal row inherits the pipeline facts from any supported
caller, not only an exported function. This is static compiler evidence. -/
def ConcreteGeneratedInternalDeclaration.fromSupportedFunction
    {program : Fir.LeanIR.ImpureProgram} {callerContext context : Context}
    {callerCode code : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {callerFunction sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    (row : ConcreteGeneratedInternalDeclaration program declaration context code
      sourceModule sourceFunction target)
    (spec : ConcreteSupportedFunction program callerContext callerCode sourceModule
      callerFunction target hosts) :
    ConcreteSupportedFunction program context code sourceModule sourceFunction target hosts := {
  spec with
  contextProgram := row.contextProgram
  localKindsExact := row.localKindsExact
  sourceFunctionIndex := row.sourceFunctionIndex
  sourceFunctionFound := row.sourceFunctionFound
  sourceResultKind := row.sourceResultKind
  sourceResultAt := row.sourceResultAt
  sourceDeclaration := declaration
  sourceDeclarationFound := row.declarationFound
  sourceDeclarationBody := row.declarationBody
  sourceFunctionName := row.sourceFunctionName
  sourceResultSelected := row.sourceResultSelected
  localsAligned := row.localsAligned
  targetFunctionIndex := row.targetFunctionIndex
  targetFunction := row.targetFunction
  notImport := row.notImport
  targetFunctionFound := row.targetFunctionFound
  targetBody := row.targetBody
  targetBodyEq := row.targetBodyEq
  bodyAdapted := row.bodyAdapted
  singleResult := row.singleResult }

/-- Enter a compiler-selected nullary initializer on a cache miss. This proves
execution and the initial callee resource frame for every result kind, including
heap objects. It deliberately does not construct the restricted general lazy
suspended-stack relation: a heap-result client must prove publication separately.
The source step, target path and installed continuations are conclusions. -/
theorem ConcreteStructuredLazyCallReadyFocus.enterBody
    {program : Fir.LeanIR.ImpureProgram} {context calleeContext : Context}
    {sourceModule : Fir.Wasm.Module} {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts} {externals : ExternalImpl}
    {labels : LabelContext} {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {declaration : Name} {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {call : LazyCacheCallSupported context decl declaration sourceDeclaration resultKind}
    {generated : LazyCacheGeneratedEnvironment context sourceModule}
    {entryRuntime runtime : RuntimeState} {entryStore store : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    {callerEnv : Env} {continuation calleeCode : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv} {sourceFrames : List Frame} {callerLocals : Wasm.Locals}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    {cacheIndex declarationId cacheSetId resultIndex : Nat}
    {source : MachineState} {target : StructuredWasmState Host}
    (ready : ConcreteStructuredLazyCallReadyFocus context sourceModule callerFunction labels
      call generated runtime callerEnv continuation callerJoins sourceFrames store
      callerLocals rest frames witness cacheIndex declarationId cacheSetId resultIndex source target)
    (scope : ConcreteStructuredResourceScope context sourceModule callerFunction externals
      entryRuntime entryStore entryWitness facts bytes runtime callerEnv store callerLocals witness)
    (contextProgram : context.program = program)
    (row : ConcreteGeneratedInternalDeclaration program sourceDeclaration calleeContext
      calleeCode sourceModule calleeFunction targetModule)
    (empty : findGlobal? runtime.globals declaration = none) :
    ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target targetAfter ∧
      ConcreteStructuredCodeFocus calleeContext sourceModule calleeFunction [] runtime []
        calleeCode store (row.targetFunction.toLocals []) row.targetFunction.body witness
        sourceAfter targetAfter ∧
      ConcreteReuseCapacityCacheAbiFrame calleeContext sourceModule calleeFunction externals
        [] bytes runtime [] store (row.targetFunction.toLocals []) witness ∧
      sourceAfter.joins = [] ∧
      sourceAfter.frames = .cache declaration ::
        .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames ∧
      targetAfter.frames =
        .call 1 callerLocals.values callerLocals
          [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1,
            .globalSet (2 * cacheIndex)] ::
        .label 0 callerLocals.values
          ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames := by
  rcases call with ⟨_, _, targetEq, _, _, paramsEq, _⟩
  have parametersEmpty : sourceDeclaration.params = #[] := Array.isEmpty_iff.mp paramsEq
  have declarationNameEq : sourceDeclaration.name = declaration := by
    have selected := (Array.find?_eq_some_iff_getElem.mp targetEq).1
    simpa [Fir.LeanIR.Program.findDecl?] using selected
  have declarationIdEq : declarationId = row.targetFunctionIndex :=
    Option.some.inj (ready.declarationCall.symm.trans (by
      simpa [declarationNameEq] using row.callIndexEq))
  subst declarationId
  let sourceAfter : MachineState := {
    program := context.program, control := .code calleeCode, env := [], joins := []
    frames := .cache declaration :: .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames
    runtime := runtime }
  have sourceStep : executeStep externals source = .next sourceAfter := by
    rcases source with ⟨p, c, e, j, f, r⟩
    have hp := ready.sourceProgramEq
    have hc := ready.sourceControlEq
    have he := ready.sourceEnvEq
    have hj := ready.sourceJoinsEq
    have hf := ready.sourceFramesEq
    have hr := ready.sourceRuntimeEq
    change p = context.program at hp
    change c = .invokeName declaration #[] at hc
    change e = callerEnv at he
    change j = callerJoins at hj
    change f = _ at hf
    change r = runtime at hr
    subst p c e j f r
    simp [sourceAfter, executeStep, coreStep, invokeDecl, empty, targetEq,
      parametersEmpty, row.declarationBody, bindParams]
  have flagEmpty : store.globals.globals[2 * cacheIndex]? = some (.i32 0) :=
    scope.1.1.2.1.emptySlot ready.initializerFound ready.signature empty
  let targetAfter : StructuredWasmState Host := {
    store := store
    control := .running (row.targetFunction.toLocals []) row.targetFunction.body
    frames := .call 1 callerLocals.values callerLocals
      [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1,
        .globalSet (2 * cacheIndex)] ::
      .label 0 callerLocals.values
        ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames }
  have targetPath :
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target targetAfter := by
    rcases target with ⟨s, c, f⟩
    have hs := ready.targetStoreEq
    have hc := ready.targetControlEq
    have hf := ready.targetFramesEq
    change s = store at hs
    change c = _ at hc
    change f = frames at hf
    subst s c f
    simpa [targetAfter] using structuredWasmLazyMissPrefixFinitePath
      (module := targetModule.wasmModule) (hostEnv := hosts.env)
      (store := store) (locals := callerLocals)
      (flagIndex := 2 * cacheIndex) (valueIndex := 2 * cacheIndex + 1)
      (resultIndex := resultIndex) (declarationId := row.targetFunctionIndex)
      (cacheSetId := cacheSetId) (function := row.targetFunction)
      (rest := rest) (frames := frames) callerLocals.values flagEmpty row.notImport
      row.targetFunctionFound (row.targetParameterCount_nullary parametersEmpty).symm
      row.singleResult
  have frame := scope.1.1.generatedNullaryCalleeEntryAtCost row parametersEmpty (Nat.le_refl bytes)
  have abi : ClosureAllocationsAbiAligned calleeContext.program witness := by
    rw [row.contextProgram, ← contextProgram]
    exact scope.2
  have focus : ConcreteStructuredCodeFocus calleeContext sourceModule calleeFunction []
      runtime [] calleeCode store (row.targetFunction.toLocals []) row.targetFunction.body
      witness sourceAfter targetAfter := {
    sourceProgramEq := contextProgram.trans row.contextProgram.symm
    sourceControlEq := rfl, sourceEnvEq := rfl, sourceRuntimeEq := rfl
    targetStoreEq := rfl, targetControlEq := rfl
    adapted := by rw [row.targetBodyEq]; exact CodeAdapted.withSuffix row.bodyAdapted
    stateRelated := frame.1.1.1.1.1
    frameAligned := frame.1.1.1.2.2.1 }
  exact ⟨sourceAfter, targetAfter, sourceStep, targetPath, focus, ⟨frame, abi⟩, rfl, rfl, rfl⟩

end FirTalos.Concrete
