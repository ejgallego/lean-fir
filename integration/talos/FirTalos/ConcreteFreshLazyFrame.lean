import FirTalos.ConcretePublicationValidation
import FirTalos.ConcreteRegionEntry

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-! The suspended caller of a fresh heap-valued initializer. This is current
compiler/frame evidence, not a promise about every future callee result.
Construction and result freshness belong to the active callee relation. -/

section Caller

variable {program : Fir.LeanIR.ImpureProgram} {context : Context}
  {functionCode : Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
  {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
  {hosts : ResolvedHosts} {externals : ExternalImpl}
  {spec : ConcreteSupportedFunction program context functionCode sourceModule
    sourceFunction targetModule hosts}
  {labels : LabelContext} {entryRuntime runtime : RuntimeState}
  {entryStore store : Wasm.Store Host} {entryWitness witness : RefinementWitness}
  {functionResult rootResult : AbiKind} {expected : Option AbiKind}
  {facts : ReuseCapacityFacts} {bytes : Nat} {env : Env} {locals : Wasm.Locals}
  {decl : Compiler.LCNF.LetDecl .impure} {continuation : Compiler.LCNF.Code .impure}
  {code : Wasm.Program} {source : MachineState} {target : StructuredWasmState Host}

/-- The saved validated caller and exact generated publication continuation.
The initializer's entry is `runtime/store/witness`, while the saved caller keeps
its potentially older `entryRuntime/entryStore/entryWitness` unchanged. -/
structure ConcreteStructuredFreshLazyFrame
    (saved : ConcreteStructuredValidatedCodeOutcome program context functionCode
      sourceModule sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult expected facts bytes runtime env
      (.let decl continuation) store locals code witness source target)
    (rootResult : AbiKind) (declaration : Name) (kind : AbiKind)
    (cacheIndex cacheSetId resultIndex : Nat) (rest : Wasm.Program) : Prop where
  activeResult : spec.sourceResultKind = functionResult
  rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
    saved.agrees saved.frames.validation
  initializerFound : sourceModule.initializers[cacheIndex]? = some declaration
  signature : (sourceModule.callSignature? (.declaration declaration)).bind
    (·.results[0]?) = some kind
  cacheSetCall : callIndex? sourceModule (.runtime (.cacheSet declaration kind)) =
    some cacheSetId
  adapted : CodeAdaptedWithSuffix context sourceModule sourceFunction labels continuation rest
  resultFound : findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex
  kindAt : (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind

variable {saved : ConcreteStructuredValidatedCodeOutcome program context functionCode
  sourceModule sourceFunction targetModule hosts spec externals labels entryRuntime
  entryStore entryWitness functionResult expected facts bytes runtime env
  (.let decl continuation) store locals code witness source target}
  {declaration : Name} {kind : AbiKind} {cacheIndex cacheSetId resultIndex : Nat}
  {rest : Wasm.Program}

/-- Stage the compiler-selected lazy call and retain everything needed to restore
its validated caller. This staging rule has no object/tobject exclusion. -/
theorem ConcreteStructuredValidatedCodeOutcome.stageFreshLazyAtRoot
    (saved : ConcreteStructuredValidatedCodeOutcome program context functionCode
      sourceModule sourceFunction targetModule hosts spec externals labels entryRuntime
      entryStore entryWitness functionResult expected facts bytes runtime env
      (.let decl continuation) store locals code witness source target)
    (activeResult : spec.sourceResultKind = functionResult)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      saved.agrees saved.frames.validation)
    {sourceDeclaration : Compiler.LCNF.Decl .impure}
    (call : LazyCacheCallSupported context decl declaration sourceDeclaration kind)
    (generated : LazyCacheGeneratedEnvironment context sourceModule) :
    ∃ staged cacheIndex declarationId cacheSetId resultIndex rest,
      executeStep externals source = .next staged ∧
      ConcreteStructuredLazyCallReadyFocus context sourceModule sourceFunction labels
        call generated runtime env continuation source.joins source.frames store locals rest
        target.frames witness cacheIndex declarationId cacheSetId resultIndex staged target ∧
      ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
        cacheIndex cacheSetId resultIndex rest := by
  obtain ⟨staged, cacheIndex, declarationId, cacheSetId, resultIndex, rest, step, ready⟩ :=
    saved.core.core.focus.stageLazyCall call generated spec.localsAligned
  exact ⟨staged, cacheIndex, declarationId, cacheSetId, resultIndex, rest, step, ready,
    ⟨activeResult, rooted, ready.initializerFound, ready.signature, ready.cacheSetCall,
      ready.continuationAdapted, ready.resultFound, ready.resultKindAt⟩⟩

/-- Active construction with its saved caller attached. Stack equations record
the continuations actually installed at entry, rather than a future restore
operation supplied by a theorem client. -/
structure ConcreteStructuredFreshLazyCode
    (frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest)
    (calleeContext : Context) (calleeFunction : Fir.Wasm.Function)
    (calleeLabels : LabelContext) (current : RuntimeState) (currentStore : Wasm.Store Host)
    (currentWitness : RefinementWitness) (calleeFacts : ReuseCapacityFacts)
    (remainingBytes : Nat) (calleeEnv : Env) (calleeLocals : Wasm.Locals)
    (calleeCode : Compiler.LCNF.Code .impure) (targetCode : Wasm.Program)
    (activeSource : MachineState) (activeTarget : StructuredWasmState Host) : Prop where
  active : ConcreteStructuredRegionCodeCore calleeContext sourceModule calleeFunction externals
    calleeLabels runtime store witness calleeFacts remainingBytes current calleeEnv calleeCode
    currentStore calleeLocals targetCode currentWitness activeSource activeTarget
  programEq : calleeContext.program = context.program
  sourceStack : activeSource.frames = .cache declaration ::
    .bind decl.fvarId continuation env source.joins :: source.frames
  targetStack : activeTarget.frames =
    .call 1 locals.values locals
      [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1,
        .globalSet (2 * cacheIndex)] ::
    .label 0 locals.values ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) ::
    target.frames

/-- Enter a cold initializer with the saved caller attached to the active
construction state. Entry derives the region and concrete stack layout. -/
theorem ConcreteStructuredFreshLazyFrame.enter
    (frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest)
    {sourceDeclaration : Compiler.LCNF.Decl .impure}
    {call : LazyCacheCallSupported context decl declaration sourceDeclaration kind}
    {generated : LazyCacheGeneratedEnvironment context sourceModule}
    {declarationId : Nat} {staged : MachineState}
    (ready : ConcreteStructuredLazyCallReadyFocus context sourceModule sourceFunction labels
      call generated runtime env continuation source.joins source.frames store locals rest
      target.frames witness cacheIndex declarationId cacheSetId resultIndex staged target)
    {calleeContext : Context} {calleeFunction : Fir.Wasm.Function}
    {calleeCode : Compiler.LCNF.Code .impure}
    (row : ConcreteGeneratedInternalDeclaration program sourceDeclaration calleeContext
      calleeCode sourceModule calleeFunction targetModule)
    (empty : findGlobal? runtime.globals declaration = none) :
    ∃ sourceAfter targetAfter,
      executeStep externals staged = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target targetAfter ∧
      ConcreteStructuredFreshLazyCode frame calleeContext calleeFunction [] runtime store witness
        [] bytes [] (row.targetFunction.toLocals []) calleeCode row.targetFunction.body
        sourceAfter targetAfter := by
  obtain ⟨sourceAfter, targetAfter, step, path, active, _, sourceStack, targetStack⟩ :=
    ready.enterRegion saved.core.core.resources.current spec.contextProgram row empty
  exact ⟨sourceAfter, targetAfter, step, path, ⟨active,
    row.contextProgram.trans spec.contextProgram.symm, sourceStack, targetStack⟩⟩

/-- A returned fresh object with the real saved lazy continuations. The root ABI
belongs to the caller frame; `kind` is only the initializer's result ABI. -/
structure ConcreteStructuredFreshLazyReturned
    (frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest)
    (calleeContext : Context) (calleeFunction : Fir.Wasm.Function)
    (current : RuntimeState) (currentStore : Wasm.Store Host)
    (currentWitness : RefinementWitness) (calleeFacts : ReuseCapacityFacts)
    (remainingBytes : Nat) (calleeEnv : Env) (calleeLocals : Wasm.Locals)
    (root : Location) (physical : Wasm.Value)
    (returnedSource : MachineState) (returnedTarget : StructuredWasmState Host) : Prop where
  current : ConcreteStructuredFreshYieldCore calleeContext sourceModule calleeFunction
    externals runtime store witness calleeFacts remainingBytes current calleeEnv currentStore
    calleeLocals currentWitness kind root physical returnedSource returnedTarget
  programEq : calleeContext.program = context.program
  sourceStack : returnedSource.frames = .cache declaration ::
    .bind decl.fvarId continuation env source.joins :: source.frames
  targetStack : returnedTarget.frames =
    .call 1 locals.values locals
      [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1,
        .globalSet (2 * cacheIndex)] ::
    .label 0 locals.values ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) ::
    target.frames

/-- A precise fresh return transports the saved frame unchanged. Matching the
initializer result kind is checked separately from heap freshness: sharing an
i32 carrier alone is not evidence for a precise object representation. -/
theorem ConcreteStructuredFreshLazyCode.advance_return
    {frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest}
    {calleeContext : Context} {calleeFunction : Fir.Wasm.Function}
    {calleeLabels : LabelContext} {current : RuntimeState} {currentStore : Wasm.Store Host}
    {currentWitness : RefinementWitness} {calleeFacts : ReuseCapacityFacts}
    {remainingBytes : Nat} {calleeEnv : Env} {calleeLocals : Wasm.Locals}
    {result : FVarId} {targetCode : Wasm.Program}
    {activeSource : MachineState} {activeTarget : StructuredWasmState Host} {root : Location}
    (related : ConcreteStructuredFreshLazyCode frame calleeContext calleeFunction calleeLabels
      current currentStore currentWitness calleeFacts remainingBytes calleeEnv calleeLocals
      (.return result) targetCode activeSource activeTarget)
    (aligned : LocalLayoutAligned calleeContext calleeFunction)
    (compiled : getLocal calleeContext result = .ok (.localGet result, kind))
    (lookupResult : lookup calleeEnv result = some (.object (.heap root)))
    (fresh : runtime.nextLocation ≤ root) :
    ∃ physical sourceAfter targetAfter,
      executeStep externals activeSource = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2
        activeTarget targetAfter ∧
      ConcreteStructuredFreshLazyReturned frame calleeContext calleeFunction current
        currentStore currentWitness calleeFacts remainingBytes calleeEnv calleeLocals
        root physical sourceAfter targetAfter := by
  obtain ⟨actualKind, physical, sourceAfter, targetAfter, actualCompiled, step, path,
      returned, _, sourceFrames, targetFrames⟩ :=
    related.active.advance_return aligned lookupResult fresh
      (module := targetModule.wasmModule) (hostEnv := hosts.env)
  have kindEq : actualKind = kind := by
    have pairEq := Except.ok.inj (actualCompiled.symm.trans compiled)
    exact congrArg Prod.snd pairEq
  subst actualKind
  exact ⟨physical, sourceAfter, targetAfter, step, path, ⟨returned, related.programEq,
    sourceFrames.trans related.sourceStack, targetFrames.trans related.targetStack⟩⟩

/-- Publication consumes the saved frame and current construction evidence.
No additional caller invariant, numeric-index fact, target path or future
execution is a premise. The successor is the existing rooted global relation. -/
theorem ConcreteStructuredFreshLazyReturned.publish
    {frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest}
    {calleeContext : Context} {calleeFunction : Fir.Wasm.Function}
    {current : RuntimeState} {currentStore : Wasm.Store Host}
    {currentWitness : RefinementWitness} {calleeFacts : ReuseCapacityFacts}
    {remainingBytes : Nat} {calleeEnv : Env} {calleeLocals : Wasm.Locals}
    {root : Location} {physical : Wasm.Value}
    {returnedSource : MachineState} {returnedTarget : StructuredWasmState Host}
    (returned : ConcreteStructuredFreshLazyReturned frame calleeContext calleeFunction
      current currentStore currentWitness calleeFacts remainingBytes calleeEnv calleeLocals
      root physical returnedSource returnedTarget) :
    ∃ published targetPublished,
      executeStep externals returnedSource = .next published ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 7
        returnedTarget targetPublished ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule targetModule
        hosts externals rootResult currentWitness published targetPublished ∧
      HeapRegionClosed runtime.nextLocation published.runtime.heap :=
  returned.current.publishAtRoot saved frame.activeResult frame.rooted returned.programEq
    frame.initializerFound frame.signature frame.cacheSetCall returned.sourceStack
    returned.targetStack frame.adapted frame.resultFound frame.kindAt

end Caller

end FirTalos.Concrete
