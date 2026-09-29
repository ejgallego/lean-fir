import FirTalos.ConcreteFreshLazyFrame
import FirTalos.ConcreteRegionExternal

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-! A fresh initializer's suspended caller survives each external-call phase.
The external destination frame is above the saved lazy stack; it must not be
confused with the lazy caller's own destination frame. Resource and heap-region
preservation are supplied by the existing operation refinements. -/

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
  {saved : ConcreteStructuredValidatedCodeOutcome program context functionCode
    sourceModule sourceFunction targetModule hosts spec externals labels entryRuntime
    entryStore entryWitness functionResult expected facts bytes runtime env
    (.let decl continuation) store locals code witness source target}
  {declaration : Name} {kind : AbiKind} {cacheIndex cacheSetId resultIndex : Nat}
  {rest : Wasm.Program}

/-- The passive part of the lazy frame, indexed by the stacks *below* any
temporary external destination bind. Neither the current heap nor a future
return value is a field of this relation. -/
structure ConcreteStructuredFreshLazySuspension
    (frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest)
    (calleeContext : Context) (sourceFrames : List Frame)
    (targetFrames : List StructuredWasmFrame) : Prop where
  programEq : calleeContext.program = context.program
  sourceStack : sourceFrames = .cache declaration ::
    .bind decl.fvarId continuation env source.joins :: source.frames
  targetStack : targetFrames =
    .call 1 locals.values locals
      [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1,
        .globalSet (2 * cacheIndex)] ::
    .label 0 locals.values ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) ::
    target.frames

variable {frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
  cacheIndex cacheSetId resultIndex rest}
  {calleeContext : Context} {calleeFunction : Fir.Wasm.Function}
  {calleeLabels : LabelContext} {current nextRuntime : RuntimeState}
  {currentStore nextStore : Wasm.Store Host}
  {currentWitness nextWitness : RefinementWitness} {calleeFacts : ReuseCapacityFacts}
  {remainingBytes cost : Nat} {calleeEnv : Env} {calleeLocals : Wasm.Locals}
  {calleeCode : Compiler.LCNF.Code .impure} {targetCode : Wasm.Program}
  {activeSource : MachineState} {activeTarget : StructuredWasmState Host}
  {sourceFrames : List Frame} {targetFrames : List StructuredWasmFrame}

/-- Extract suspension evidence from an active construction state. -/
theorem ConcreteStructuredFreshLazyCode.suspension
    (related : ConcreteStructuredFreshLazyCode frame calleeContext calleeFunction calleeLabels
      current currentStore currentWitness calleeFacts remainingBytes calleeEnv calleeLocals
      calleeCode targetCode activeSource activeTarget) :
    ConcreteStructuredFreshLazySuspension frame calleeContext
      activeSource.frames activeTarget.frames :=
  ⟨related.programEq, related.sourceStack, related.targetStack⟩

/-- Reattach the original caller after a stack-preserving construction step.
Only the operation's current region relation and its actual stack equations
are needed; the caller's validation and root ABI are retained in `frame`. -/
theorem ConcreteStructuredFreshLazySuspension.resume
    (suspended : ConcreteStructuredFreshLazySuspension frame calleeContext
      sourceFrames targetFrames)
    (active : ConcreteStructuredRegionCodeCore calleeContext sourceModule calleeFunction
      externals calleeLabels runtime store witness calleeFacts remainingBytes current calleeEnv
      calleeCode currentStore calleeLocals targetCode currentWitness activeSource activeTarget)
    (sourceStack : activeSource.frames = sourceFrames)
    (targetStack : activeTarget.frames = targetFrames) :
    ConcreteStructuredFreshLazyCode frame calleeContext calleeFunction calleeLabels
      current currentStore currentWitness calleeFacts remainingBytes calleeEnv calleeLocals
      calleeCode targetCode activeSource activeTarget :=
  ⟨active, suspended.programEq, sourceStack.trans suspended.sourceStack,
    targetStack.trans suspended.targetStack⟩

/-- Ready to execute an external operation inside a fresh initializer. The
control relation includes the temporary bind; the suspension indexes its tail. -/
structure ConcreteStructuredFreshLazyExternalCall
    (frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest)
    (calleeContext : Context) (calleeFunction : Fir.Wasm.Function)
    (calleeFacts : ReuseCapacityFacts) (remainingBytes : Nat)
    {current nextRuntime : RuntimeState} {calleeEnv : Env} {value : Value}
    {siteDecl : Compiler.LCNF.LetDecl .impure}
    (site : ExternalCallShape calleeContext externals current calleeEnv siteDecl nextRuntime value)
    (operation : ExternalOperation) (resolvedKind : AbiKind) (imp : Wasm.ImportDecl)
    (calleeLabels : LabelContext) (continuation : Compiler.LCNF.Code .impure)
    (joins : JoinEnv) (sourceFrames : List Frame) (currentStore : Wasm.Store Host)
    (calleeLocals : Wasm.Locals) (remainder : List Wasm.Value) (targetCode : Wasm.Program)
    (targetFrames : List StructuredWasmFrame) (currentWitness : RefinementWitness)
    (args : List Wasm.Value) (callIndex destination : Nat)
    (activeSource : MachineState) (activeTarget : StructuredWasmState Host) : Prop where
  active : ConcreteStructuredRegionExternalCall program calleeContext sourceModule calleeFunction
    targetModule hosts externals runtime store witness calleeFacts remainingBytes site operation
    resolvedKind imp calleeLabels continuation joins sourceFrames currentStore calleeLocals
    remainder targetCode targetFrames currentWitness args callIndex destination activeSource activeTarget
  suspension : ConcreteStructuredFreshLazySuspension frame calleeContext sourceFrames targetFrames

/-- A produced external value awaiting its local bind, above the same saved
lazy caller. This is not yet a returned initializer value. -/
structure ConcreteStructuredFreshLazyExternalBind
    (frame : ConcreteStructuredFreshLazyFrame saved rootResult declaration kind
      cacheIndex cacheSetId resultIndex rest)
    (calleeContext : Context) (calleeFunction : Fir.Wasm.Function)
    (calleeFacts : ReuseCapacityFacts) (remainingBytes : Nat) (calleeLabels : LabelContext)
    (current : RuntimeState) (calleeEnv : Env) (value : Value) (result : FVarId)
    (continuation : Compiler.LCNF.Code .impure) (joins : JoinEnv) (sourceFrames : List Frame)
    (currentStore : Wasm.Store Host) (calleeLocals : Wasm.Locals)
    (remainder : List Wasm.Value) (targetCode : Wasm.Program)
    (targetFrames : List StructuredWasmFrame) (currentWitness : RefinementWitness)
    (resultKind : AbiKind) (physical : Wasm.Value) (destination : Nat)
    (activeSource : MachineState) (activeTarget : StructuredWasmState Host) : Prop where
  active : ConcreteStructuredRegionExternalBind calleeContext sourceModule calleeFunction externals
    runtime store witness calleeFacts remainingBytes calleeLabels current calleeEnv value result
    continuation joins sourceFrames currentStore calleeLocals remainder targetCode targetFrames
    currentWitness resultKind physical destination activeSource activeTarget
  suspension : ConcreteStructuredFreshLazySuspension frame calleeContext sourceFrames targetFrames

/-- Argument staging derives the temporary external frame while retaining the
lazy caller below it. It changes neither the entry cutoff nor the root ABI. -/
theorem ConcreteStructuredFreshLazyCode.stageExternal
    {rootCode : Compiler.LCNF.Code .impure}
    (calleeSpec : ConcreteSupportedFunction program calleeContext rootCode sourceModule
      calleeFunction targetModule hosts)
    {siteDecl : Compiler.LCNF.LetDecl .impure} {value : Value}
    (related : ConcreteStructuredFreshLazyCode frame calleeContext calleeFunction calleeLabels
      current currentStore currentWitness calleeFacts remainingBytes calleeEnv calleeLocals
      (.let siteDecl calleeCode) targetCode activeSource activeTarget)
    (site : ExternalCallShape calleeContext externals current calleeEnv siteDecl nextRuntime value) :
    ∃ args operation resolvedKind imp callIndex destination,
    ∃ targetArguments nextCode : Wasm.Program, ∃ sourceAfter targetAfter,
      executeStep externals activeSource = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetArguments.length activeTarget targetAfter ∧
      ConcreteStructuredFreshLazyExternalCall frame calleeContext calleeFunction calleeFacts
        remainingBytes site operation resolvedKind imp calleeLabels calleeCode activeSource.joins
        activeSource.frames currentStore calleeLocals calleeLocals.values nextCode activeTarget.frames
        currentWitness args callIndex destination sourceAfter targetAfter := by
  obtain ⟨args, operation, resolvedKind, imp, callIndex, destination, targetArguments,
      nextCode, sourceAfter, targetAfter, step, path, ready⟩ :=
    related.active.stageExternal calleeSpec site
  exact ⟨args, operation, resolvedKind, imp, callIndex, destination, targetArguments,
    nextCode, sourceAfter, targetAfter, step, path, ⟨ready, related.suspension⟩⟩

/-- The host step updates the current region/scope, not the saved caller. In
particular, witness extension does not change the initializer's entry witness. -/
theorem ConcreteStructuredFreshLazyExternalCall.advance_call
    {siteDecl : Compiler.LCNF.LetDecl .impure} {value : Value}
    {site : ExternalCallShape calleeContext externals current calleeEnv siteDecl nextRuntime value}
    {operation : ExternalOperation} {resolvedKind : AbiKind} {imp : Wasm.ImportDecl}
    {joins : JoinEnv} {remainder args : List Wasm.Value} {callIndex destination : Nat}
    {physical : Wasm.Value}
    (ready : ConcreteStructuredFreshLazyExternalCall frame calleeContext calleeFunction calleeFacts
      remainingBytes site operation resolvedKind imp calleeLabels calleeCode joins sourceFrames
      currentStore calleeLocals remainder targetCode targetFrames currentWitness args callIndex
      destination activeSource activeTarget)
    (evidence : ConcreteExternalCallEvidence operation resolvedKind currentStore args current
      nextRuntime value currentWitness nextStore nextWitness physical)
    (budget : nextStore.host.runtime.heap.AddressSpaceBudget (remainingBytes - cost))
    (preservesRegion : HeapRegionClosed runtime.nextLocation current.heap →
      HeapRegionClosed runtime.nextLocation nextRuntime.heap) :
    ∃ sourceAfter targetAfter,
      executeStep externals activeSource = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 1 activeTarget targetAfter ∧
      ConcreteStructuredFreshLazyExternalBind frame calleeContext calleeFunction calleeFacts
        (remainingBytes - cost) calleeLabels nextRuntime calleeEnv value siteDecl.fvarId calleeCode
        joins sourceFrames nextStore calleeLocals remainder targetCode targetFrames nextWitness
        site.resultKind physical destination sourceAfter targetAfter := by
  obtain ⟨sourceAfter, targetAfter, step, path, bound⟩ :=
    ready.active.advance_call evidence budget preservesRegion
  exact ⟨sourceAfter, targetAfter, step, path, ⟨bound, ready.suspension⟩⟩

/-- An external result awaiting its local destination cannot be mistaken for
the initializer's return/publication state, even when both values are objects. -/
theorem ConcreteStructuredFreshLazyExternalBind.not_initializerReturnStack
    {value : Value} {result : FVarId} {joins : JoinEnv} {remainder : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value} {destination : Nat}
    (bound : ConcreteStructuredFreshLazyExternalBind frame calleeContext calleeFunction calleeFacts
      remainingBytes calleeLabels current calleeEnv value result calleeCode joins sourceFrames
      currentStore calleeLocals remainder targetCode targetFrames currentWitness resultKind physical
      destination activeSource activeTarget) :
    activeSource.frames ≠ .cache declaration ::
      .bind decl.fvarId continuation env source.joins :: source.frames := by
  rw [bound.active.focus.sourceFramesEq]
  intro impossible
  cases impossible

/-- Consume exactly the external destination bind and resume construction with
the saved caller attached. No new caller invariant or stack equation is asked
of the client, and the original root result kind remains indexed by `frame`. -/
theorem ConcreteStructuredFreshLazyExternalBind.advance
    {value : Value} {result : FVarId} {joins : JoinEnv} {remainder : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value} {destination : Nat}
    (bound : ConcreteStructuredFreshLazyExternalBind frame calleeContext calleeFunction calleeFacts
      remainingBytes calleeLabels current calleeEnv value result calleeCode joins sourceFrames
      currentStore calleeLocals remainder targetCode targetFrames currentWitness resultKind physical
      destination activeSource activeTarget) :
    ∃ sourceAfter targetAfter updated resumedLocals,
      executeStep externals activeSource = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 1 activeTarget targetAfter ∧
      calleeLocals.set? destination physical = some updated ∧
      resumedLocals = { updated with values := remainder } ∧
      ConcreteStructuredFreshLazyCode frame calleeContext calleeFunction calleeLabels
        current currentStore currentWitness (eraseReuseCapacityFact calleeFacts result)
        remainingBytes (bind calleeEnv result value) resumedLocals calleeCode targetCode
        sourceAfter targetAfter ∧
      sourceAfter.joins = joins := by
  obtain ⟨sourceAfter, targetAfter, updated, resumedLocals, step, path, set, resumed,
      active, joins, sourceStack, targetStack⟩ :=
    bound.active.advance (module := targetModule.wasmModule) (hostEnv := hosts.env)
  exact ⟨sourceAfter, targetAfter, updated, resumedLocals, step, path, set, resumed,
    bound.suspension.resume active sourceStack targetStack, joins⟩

end Caller

end FirTalos.Concrete
