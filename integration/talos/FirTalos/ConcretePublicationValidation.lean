import FirTalos.ConcretePublicationBind
import FirTalos.ConcreteValidatedLet
import FirTalos.ConcreteRootedDispatch

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Rejoin the rooted global relation at the publication/bind boundary.
Static continuation validation, saved frame agreement and root identity come
from the original caller. The current initializer supplies its resource scope
and fresh-region construction evidence, not a future execution invariant.
The pre-publication heap-return state is not yet a general global constructor. -/
theorem ConcreteStructuredValidatedCodeOutcome.publishFreshCacheAtRoot
    {program : Fir.LeanIR.ImpureProgram} {callerContext calleeContext : Context}
    {callerCode : Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts} {externals : ExternalImpl}
    {callerEntryRuntime activeEntryRuntime current : RuntimeState}
    {callerEntryStore activeEntryStore store : Wasm.Store Host}
    {callerEntryWitness activeEntryWitness witness : RefinementWitness}
    {callerFacts calleeFacts : ReuseCapacityFacts} {callerBytes remainingBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals : Wasm.Locals}
    {declaration : Name} {kind functionResult rootResult : AbiKind} {physical : Wasm.Value}
    {root : Location} {cacheIndex cacheSetId resultIndex : Nat}
    {decl : Compiler.LCNF.LetDecl .impure} {continuation : Compiler.LCNF.Code .impure}
    {labels : LabelContext} {callerJoins : JoinEnv} {callerTargetCode rest : Wasm.Program}
    {callerExpectedResult : Option AbiKind} {callerSource source : MachineState}
    {callerTarget : StructuredWasmState Host}
    {spec : ConcreteSupportedFunction program callerContext callerCode sourceModule
      callerFunction targetModule hosts}
    (saved : ConcreteStructuredValidatedCodeOutcome program callerContext callerCode
      sourceModule callerFunction targetModule hosts spec externals labels
      callerEntryRuntime callerEntryStore callerEntryWitness functionResult callerExpectedResult
      callerFacts callerBytes activeEntryRuntime callerEnv (.let decl continuation)
      activeEntryStore callerLocals callerTargetCode activeEntryWitness callerSource callerTarget)
    (activeResult : spec.sourceResultKind = functionResult)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      saved.agrees saved.frames.validation)
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
    (sourceStack : source.frames = .cache declaration ::
      .bind decl.fvarId continuation callerEnv callerJoins :: callerSource.frames)
    (adapted : CodeAdaptedWithSuffix callerContext sourceModule callerFunction labels
      continuation rest)
    (resultFound : findFVar? (functionBindings callerFunction) decl.fvarId = some resultIndex)
    (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd = some kind) :
    ∃ runtimeAfter published targetPublished,
      executeStep externals source = .next published ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 7
        ⟨store, .returning (physical :: calleeLocals.values),
          .call 1 callerLocals.values callerLocals
            [.call cacheSetId, .globalSet (2 * cacheIndex + 1),
              .const 1, .globalSet (2 * cacheIndex)] ::
          .label 0 callerLocals.values
            ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) ::
          callerTarget.frames⟩ targetPublished ∧
      ∃ next : ConcreteStructuredValidatedExternalBindOutcome program callerContext callerCode
        sourceModule callerFunction targetModule hosts spec externals labels
        callerEntryRuntime callerEntryStore callerEntryWitness functionResult callerExpectedResult
        callerFacts remainingBytes (current.setGlobal declaration (.object (.heap root)))
        callerEnv (.object (.heap root)) decl.fvarId continuation callerJoins callerSource.frames
        (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
          (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1))
        callerLocals callerLocals.values rest callerTarget.frames witness kind physical resultIndex
        published targetPublished,
      ConcreteStructuredValidationAgreesAtRoot rootResult next.agrees next.frames.validation ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule targetModule
        hosts externals rootResult witness published targetPublished ∧
      HeapRegionClosed activeEntryRuntime.nextLocation published.runtime.heap := by
  obtain ⟨runtimeAfter, published, targetPublished, step, path, core, region⟩ :=
    saved.core.core.resources.current.publishFreshCache_step spec currentScope programEq
      initializerFound signature cacheSetCall valueRelated closed rootBound sourceProgram
      sourceControl sourceRuntime sourceStack adapted resultFound kindAt
      saved.core.core.resources.suspended
  let next : ConcreteStructuredValidatedExternalBindOutcome program callerContext callerCode
      sourceModule callerFunction targetModule hosts spec externals labels
      callerEntryRuntime callerEntryStore callerEntryWitness functionResult callerExpectedResult
      callerFacts remainingBytes (current.setGlobal declaration (.object (.heap root)))
      callerEnv (.object (.heap root)) decl.fvarId continuation callerJoins callerSource.frames
      (writeWasmGlobal (writeWasmGlobal (replaceRuntime store runtimeAfter)
        (2 * cacheIndex + 1) physical) (2 * cacheIndex) (.i32 1))
      callerLocals callerLocals.values rest callerTarget.frames witness kind physical resultIndex
      published targetPublished := {
    activeResult := activeResult
    contextCaches := saved.contextCaches
    core := core
    continuationValidation := saved.core.validation.afterLet
    frames := saved.frames
    agrees := saved.agrees
    validationAgrees := saved.validationAgrees }
  have nextRooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      next.agrees next.frames.validation := rooted
  exact ⟨runtimeAfter, published, targetPublished, step, path, next, nextRooted,
    .externalBind next nextRooted, region⟩

end FirTalos.Concrete
