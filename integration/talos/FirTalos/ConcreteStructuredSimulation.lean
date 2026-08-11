import FirTalos.ConcreteTraceSimulation
import FirTalos.ConcreteCompilerCorrectness
import FirTalos.ConcreteReuseCapacityCacheCorrectness
import FirTalos.Correctness.StructuredWasmAdequacy

/-!
# Compiler relation for the concrete structured Wasm target

This module begins the W6.7e construction of the compiler-derived ranked weak
simulation.  `ConcreteStructuredCodeFocus` is the local code-state component
of the eventual relation: it records the real two-stage compiler output, the
concrete runtime/local refinement, and the corresponding source and target
control states.  Source and target continuation stacks are deliberately left
outside this component so the same local proof can be lifted through the
frame relation constructed by later slices.

The first transition family is the compiler's genuinely silent case.
Persistent reference-count increments and decrements change only source
control and are erased by lowering.  Their target match is therefore the
reflexive structured path, and the structural source-control rank decreases.
-/

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.Wasm.Concrete
open Fir.LeanIR.Impure
open FirTalos.Correctness

/-- Local compiler relation at a source code node and a running structured
target node.  It fixes the source program, runtime and environment and the
target store, locals and residual program, while leaving both continuation
stacks available to the later frame relation. -/
structure ConcreteStructuredCodeFocus
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : Lean.Compiler.LCNF.Code .impure)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (targetCode : Wasm.Program)
    (witness : RefinementWitness)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = context.program
  sourceControlEq : source.control = .code sourceCode
  sourceEnvEq : source.env = sourceEnv
  sourceRuntimeEq : source.runtime = sourceRuntime
  targetStoreEq : target.store = targetStore
  targetControlEq : target.control = .running targetLocals targetCode
  adapted :
    CodeAdapted context sourceModule sourceFunction labels sourceCode targetCode
  stateRelated :
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness
  frameAligned :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness

/-- The local compiler relation already implies exact world/trace observation
agreement.  Frame correspondence is irrelevant to observations and can be
conjoined later without reproving this fact. -/
theorem ConcreteStructuredCodeFocus.observes
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv sourceCode targetStore targetLocals
      targetCode witness source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.trace

/-- Local compiler relation after a source return has yielded its semantic
value and the generated target has entered explicit return mode.  The
pre-return locals remain available for the later call-frame relation; the
physical result at the head of the returning stack is related at the exact
ABI kind selected by the compiler. -/
structure ConcreteStructuredYieldFocus
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness : RefinementWitness)
    (kind : AbiKind)
    (physical : Wasm.Value)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = context.program
  sourceControlEq : source.control = .yielded sourceValue
  sourceEnvEq : source.env = sourceEnv
  sourceRuntimeEq : source.runtime = sourceRuntime
  targetStoreEq : target.store = targetStore
  targetControlEq :
    target.control = .returning (physical :: targetLocals.values)
  stateRelated :
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness
  frameAligned :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness
  valueRelated : PhysicalValueRel witness kind physical sourceValue

theorem ConcreteStructuredYieldFocus.observes
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredYieldFocus context sourceFunction
      sourceRuntime sourceEnv sourceValue targetStore targetLocals witness kind
      physical source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.trace

/-- A source return is matched by the generated positive target path:
`local.get resultIndex` followed by the structured machine's explicit `ret`
transition.  Successful two-stage adaptation determines the index and ABI
kind, while `StateRelated.resolve` supplies the physical result and its
refinement proof. -/
theorem ConcreteStructuredCodeFocus.advance_return
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {sourceValue : Value}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.return result) targetStore targetLocals
      targetCode witness source target) :
    ∃ kind physical sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
        sourceEnv sourceValue targetStore targetLocals witness kind physical
        sourceAfter targetAfter := by
  obtain ⟨kind, resultIndex, _localCompiled, resultFound, kindAt,
      targetCodeEq⟩ :=
    CodeAdapted.return_eq localsAligned related.adapted
  obtain ⟨physical, targetLookup, valueRelated⟩ :=
    related.stateRelated.resolve sourceLookup resultFound kindAt
  subst targetCode
  let sourceAfter : MachineState :=
    { source with control := .yielded sourceValue }
  let targetAfterGet : StructuredWasmState Host :=
    { target with
      control := .running
        { targetLocals with
          values := physical :: targetLocals.values }
        [.ret] }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .returning (physical :: targetLocals.values) }
  refine ⟨kind, physical, sourceAfter, targetAfter, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = .code (.return result) at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = sourceEnv at envEq
    subst env
    simp [sourceAfter, executeStep, coreStep, lookupValue, sourceLookup]
  · have getStep :
        StructuredWasmStep module hostEnv target targetAfterGet := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      have controlEq := related.targetControlEq
      change control =
        .running targetLocals [.localGet resultIndex, .ret] at controlEq
      subst control
      apply StructuredWasmStep.atomic (fuel := 1)
      · trivial
      · simp only [Wasm.execOne.eq_def, targetLookup]
    have returnStep :
        StructuredWasmStep module hostEnv targetAfterGet targetAfter := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      exact StructuredWasmStep.beginReturn
    exact .cons getStep (.cons returnStep (.refl targetAfter))
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      stateRelated := related.stateRelated
      frameAligned := related.frameAligned
      valueRelated }

/-- Simulation-facing return rule.  The generic advance theorem supplies a
successful source step, so this wrapper recovers the returned binding from
that step and invokes `advance_return`; clients do not provide an extra
source-execution certificate or lookup premise. -/
theorem ConcreteStructuredCodeFocus.advance_return_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.return result) targetStore targetLocals
      targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ sourceValue kind physical targetAfter,
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
        sourceEnv sourceValue targetStore targetLocals witness kind physical
        sourceAfter targetAfter := by
  cases sourceLookup : lookup sourceEnv result with
  | none =>
      rcases source with
        ⟨program, control, env, joins, frames, runtime⟩
      have controlEq := related.sourceControlEq
      change control = .code (.return result) at controlEq
      subst control
      have envEq := related.sourceEnvEq
      change env = sourceEnv at envEq
      subst env
      simp [executeStep, coreStep, lookupValue, sourceLookup, fail] at sourceStep
  | some sourceValue =>
      obtain ⟨kind, physical, computedAfter, targetAfter, computedStep, path,
          focus⟩ :=
        related.advance_return localsAligned sourceLookup
      have afterEq : sourceAfter = computedAfter := by
        rw [sourceStep] at computedStep
        injection computedStep
      subst computedAfter
      exact ⟨sourceValue, kind, physical, targetAfter, path, focus⟩

/-- Changing only the operand stack commutes with a successful checked local
write.  The structured call-frame proof uses this to expose the returned value
as a stack head, execute `local.set`, and restore the caller's saved operand
tail. -/
theorem locals_set?_with_values
    {locals updated : Wasm.Locals}
    {index : Nat}
    {value : Wasm.Value}
    (values : List Wasm.Value)
    (set : locals.set? index value = some updated) :
    ({ locals with values }.set? index value) =
      some { updated with values } := by
  unfold Wasm.Locals.set? at set
  split at set
  · rename_i inParams
    cases set
    simp [Wasm.Locals.set?, inParams]
  · rename_i notInParams
    split at set
    · rename_i inLocals
      cases set
      simp [Wasm.Locals.set?, notInParams, inLocals]
    · contradiction

/-- The compiler-characterized argument prefix has an exact structured-machine
execution: every generated local read or erased zero takes one atomic target
step, the source-order physical arguments are left in Wasm stack order, and
the caller operand tail, store, and continuation frames are preserved. -/
theorem ConstructorArgsReady.finitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {argumentCode : Wasm.Program} {physicalArgs : List Wasm.Value}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    (tail : List Wasm.Value)
    (ready : ConstructorArgsReady locals argumentCode physicalArgs) :
    FinitePath (StructuredWasmStep module hostEnv) argumentCode.length
      ⟨store, .running { locals with values := tail }
        (argumentCode ++ rest), frames⟩
      ⟨store, .running
        { locals with values := physicalArgs.reverse ++ tail } rest, frames⟩ := by
  induction ready generalizing tail with
  | nil =>
      exact .refl _
  | @localGet index physical targetArgs remainingPhysical found ready ih =>
      have foundWithStack :
          ({ locals with values := tail } : Wasm.Locals).get index =
            some physical := by
        simpa [Wasm.Locals.get] using found
      have head :
          StructuredWasmStep module hostEnv
            ⟨store, .running { locals with values := tail }
              (.localGet index :: targetArgs ++ rest), frames⟩
            ⟨store, .running { locals with values := physical :: tail }
              (targetArgs ++ rest), frames⟩ := by
        apply StructuredWasmStep.atomic (fuel := 1)
        · trivial
        · simp only [Wasm.execOne.eq_def, foundWithStack]
      simpa [List.reverse_cons, List.append_assoc] using
        FinitePath.cons head (ih (tail := physical :: tail))
  | @erased targetArgs remainingPhysical ready ih =>
      have head :
          StructuredWasmStep module hostEnv
            ⟨store, .running { locals with values := tail }
              (.const 0 :: targetArgs ++ rest), frames⟩
            ⟨store, .running { locals with values := .i32 0 :: tail }
              (targetArgs ++ rest), frames⟩ := by
        apply StructuredWasmStep.atomic (fuel := 1)
        · trivial
        · simp only [Wasm.execOne.eq_def]
      simpa [List.reverse_cons, List.append_assoc] using
        FinitePath.cons head (ih (tail := .i32 0 :: tail))

/-- Intermediate relation after the source has staged an internal named call
and the generated target has evaluated its argument prefix.  Both machines
are poised to enter the callee.  The relation retains the caller continuation
and local refinement that the call frame must protect, while the generated
callee row and related physical arguments determine the entry state without a
translation certificate or assumed target execution. -/
structure ConcreteStructuredDirectCallReadyFocus
    (callerContext calleeContext : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction calleeFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (physicalArgs : List Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = callerContext.program
  sourceControlEq :
    source.control = .invokeName site.declaration site.semanticArgs
  sourceEnvEq : source.env = callerEnv
  sourceRuntimeEq : source.runtime = sourceRuntime
  sourceJoinsEq : source.joins = callerJoins
  sourceFramesEq :
    source.frames =
      .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames
  targetStoreEq : target.store = targetStore
  targetControlEq :
    target.control = .running
      { callerLocals with
        values := physicalArgs.reverse ++ callerRemainder }
      (.call row.targetFunctionIndex ::
        .localSet resultIndex :: targetRest)
  targetFramesEq : target.frames = targetFrames
  continuationAdapted :
    CodeAdapted callerContext sourceModule callerFunction labels continuation
      targetRest
  callerStateRelated :
    StateRelated callerFunction sourceRuntime callerEnv targetStore callerLocals
      witness
  callerFrameAligned :
    ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv targetStore
      callerLocals witness
  resultFound :
    findFVar? (functionBindings callerFunction) decl.fvarId = some resultIndex
  resultKindAt :
    (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some site.resultKind
  argumentsRelated :
    ConstructorArgumentsRelated witness site.argumentKinds.toList physicalArgs
      site.semanticArgs.toList

theorem ConcreteStructuredDirectCallReadyFocus.observes
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredDirectCallReadyFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.callerStateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.callerStateRelated.1.trace

/-- The first direct-call simulation step is entirely compiler-derived.  The
source stages the named invocation under its bind frame while the target
executes the exact local-read/erased-zero argument prefix recovered from
two-stage adaptation.  Both sides finish poised at their respective call
entry transitions, with the caller continuation relation protected by
`ConcreteStructuredDirectCallReadyFocus`. -/
theorem ConcreteStructuredCodeFocus.advance_directCall_stage
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (localsAligned : LocalLayoutAligned callerContext callerFunction)
    (related : ConcreteStructuredCodeFocus callerContext sourceModule
      callerFunction labels sourceRuntime callerEnv (.let decl continuation)
      targetStore targetLocals targetCode witness source target) :
    ∃ physicalArgs resultIndex,
      ∃ targetArguments targetRest : Wasm.Program,
      ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hostEnv)
        targetArguments.length target targetAfter ∧
      ConcreteStructuredDirectCallReadyFocus callerContext calleeContext
        sourceModule callerFunction calleeFunction targetModule site row labels
        sourceRuntime continuation source.joins source.frames targetStore
        targetLocals targetLocals.values targetRest target.frames witness
        physicalArgs resultIndex sourceAfter targetAfter := by
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
      targetCodeEq⟩ :=
    CodeAdapted.let_eq related.adapted
  have expectedCompiled :
      Fir.Wasm.compileLetValue callerContext decl =
        .ok (site.argumentCode ++
          [.call (.declaration site.declaration)]) := by
    simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind, site.valueEq,
      site.kindEq, site.argumentsCompiled, site.declarationFound,
      site.nonCached, Bind.bind, Except.bind, pure, Except.pure]
  have valueCodeEq :
      valueCode =
        site.argumentCode ++ [.call (.declaration site.declaration)] := by
    rw [expectedCompiled] at valueCompiled
    exact (Except.ok.inj valueCompiled).symm
  subst valueCode
  obtain ⟨targetArguments, functionIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  subst targetValue
  have declarationNameEq :
      site.sourceDeclaration.name = site.declaration := by
    have selected :=
      (Array.find?_eq_some_iff_getElem.mp site.declarationFound).1
    simpa [Fir.LeanIR.Program.findDecl?] using selected
  have exactCallIndex :
      callIndex? sourceModule (.declaration site.declaration) =
        some row.targetFunctionIndex := by
    simpa [declarationNameEq] using row.callIndexEq
  rw [exactCallIndex] at callFound
  have functionIndexEq : row.targetFunctionIndex = functionIndex :=
    Option.some.inj callFound
  subst functionIndex
  obtain ⟨physicalArgs, argumentsReady, _physicalLength,
      argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs localsAligned site.argumentsCompiled
      argumentsAdapted site.argumentsEvaluated related.stateRelated
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    localsAligned site.resultCompiled
  rw [resultFound] at alignedResultFound
  have resultIndexEq : alignedResultIndex = resultIndex :=
    (Option.some.inj alignedResultFound).symm
  subst alignedResultIndex
  have continuationAdapted :
      CodeAdapted callerContext sourceModule callerFunction labels continuation
        targetRest :=
    ⟨restCode, restCompiled, restAdapted⟩
  subst targetCode
  let sourceAfter : MachineState :=
    { source with
      control := .invokeName site.declaration site.semanticArgs
      frames :=
        .bind decl.fvarId continuation source.env source.joins :: source.frames }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running
        { targetLocals with
          values := physicalArgs.reverse ++ targetLocals.values }
        (.call row.targetFunctionIndex ::
          .localSet resultIndex :: targetRest) }
  refine ⟨physicalArgs, resultIndex, targetArguments, targetRest, sourceAfter,
    targetAfter, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = .code (.let decl continuation) at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = callerEnv at envEq
    subst env
    have runtimeEq := related.sourceRuntimeEq
    change runtime = sourceRuntime at runtimeEq
    subst runtime
    simp [sourceAfter, executeStep, coreStep, evalLetValue, site.valueEq,
      site.argumentsEvaluated, pushBindFrame]
  · rcases target with ⟨store, control, frames⟩
    have storeEq := related.targetStoreEq
    change store = targetStore at storeEq
    subst store
    have controlEq := related.targetControlEq
    change control = .running targetLocals
      ((targetArguments ++ [.call row.targetFunctionIndex]) ++
        .localSet resultIndex :: targetRest) at controlEq
    subst control
    simpa [targetAfter, List.append_assoc] using
      (argumentsReady.finitePath
        (module := targetModule.wasmModule) (hostEnv := hostEnv)
        (store := targetStore)
        (rest := .call row.targetFunctionIndex ::
          .localSet resultIndex :: targetRest)
        (frames := frames) targetLocals.values)
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      sourceJoinsEq := by simp [sourceAfter]
      sourceFramesEq := by simp [sourceAfter, related.sourceEnvEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      targetFramesEq := by simp [targetAfter]
      continuationAdapted
      callerStateRelated := related.stateRelated
      callerFrameAligned := related.frameAligned
      resultFound
      resultKindAt
      argumentsRelated }

/-- Production argument compilation preserves the source/ABI row length. -/
theorem ConstructorArgsCompiled.argumentLength
    {context : Fir.Wasm.Context}
    {args : List (Lean.Compiler.LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {kinds : List AbiKind}
    (compiled : ConstructorArgsCompiled context args argumentCode kinds) :
    args.length = kinds.length := by
  induction compiled with
  | nil => rfl
  | erased _ ih => simp [ih]
  | fvar _ _ ih => simp [ih]

/-- The generated callee locals selected by the direct-call argument relation
have exactly the source symbolic parameter/local shape.  This is the local
frame component needed when the structured machine enters the callee. -/
theorem ConcreteGeneratedInternalDeclaration.entryFrameAligned
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {sourceModule : Fir.Wasm.Module}
    {calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    {sourceRuntime : RuntimeState}
    {targetStore : Wasm.Store Host}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    ConcreteLocalFrameAligned calleeFunction sourceRuntime site.calleeEnv
      targetStore (row.targetFunction.toLocals physicalArgs) witness := by
  have classifiedSize := row.parameterKindsSize site.parametersKnown
  have parameterBindings := row.sourceParameterBindings site.parametersKnown
  have sourceParameterSize :
      calleeFunction.params.size = site.parameterKinds.size := by
    have lengths := congrArg List.length parameterBindings
    simp only [Array.length_toList, List.length_map, List.length_zip] at lengths
    rw [← classifiedSize] at lengths
    simpa using lengths
  have parameterRelated :=
    argumentsRelated.ofKindsRefine site.argumentsRefine
  have physicalSize : physicalArgs.length = site.parameterKinds.size := by
    simpa using parameterRelated.physicalLength
  have parameterFrameSize :
      (row.targetFunction.toLocals physicalArgs).params.length =
        calleeFunction.params.size := by
    simpa [Wasm.Function.toLocals] using
      physicalSize.trans sourceParameterSize.symm
  have signature :=
    FirTalos.Correctness.function_preserves_signature row.functionAdapted
  have localFrameSize :
      (row.targetFunction.toLocals physicalArgs).locals.length =
        calleeFunction.locals.size := by
    simp [Wasm.Function.toLocals, signature.2.1]
  exact ⟨parameterFrameSize, localFrameSize⟩

/-- Relation immediately after both machines enter a generated direct callee.
The local code focus is now indexed by the callee's real symbolic and adapted
function rows.  The separate caller fields record exactly the bind/call frame
that must be transported across callee effects before the accepted return
unwinding theorem can be applied. -/
structure ConcreteStructuredDirectCallEntryFocus
    (callerContext calleeContext : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction calleeFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (physicalArgs : List Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  calleeFocus :
    ConcreteStructuredCodeFocus calleeContext sourceModule calleeFunction []
      sourceRuntime site.calleeEnv site.calleeCode targetStore
      (row.targetFunction.toLocals physicalArgs) row.targetFunction.body witness
      source target
  sourceFramesEq :
    source.frames =
      .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames
  targetFramesEq :
    target.frames =
      .call 1 callerRemainder callerLocals
          (.localSet resultIndex :: targetRest) :: targetFrames
  continuationAdapted :
    CodeAdapted callerContext sourceModule callerFunction labels continuation
      targetRest
  callerStateRelated :
    StateRelated callerFunction sourceRuntime callerEnv targetStore callerLocals
      witness
  callerFrameAligned :
    ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv targetStore
      callerLocals witness
  resultFound :
    findFVar? (functionBindings callerFunction) decl.fvarId = some resultIndex
  resultKindAt :
    (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some site.resultKind
  argumentsRelated :
    ConstructorArgumentsRelated witness site.argumentKinds.toList physicalArgs
      site.semanticArgs.toList

theorem ConcreteStructuredDirectCallEntryFocus.observes
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) :=
  related.calleeFocus.observes

/-- The poised source and target call states enter the same generated callee.
The source dispatcher takes one step; the structured target takes its real
`enterCall` step.  The conclusion contains the callee code focus plus the
exact saved caller frames.  In particular, the target call frame retains the
post-argument operand stack prescribed by Wasm, while its semantic/local
invariant is transported without changing the store or witness. -/
theorem ConcreteStructuredDirectCallReadyFocus.advance_enter
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredDirectCallReadyFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ∃ sourceAfter targetAfter storedCallerLocals,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hostEnv) 1 target
        targetAfter ∧
      ConcreteStructuredDirectCallEntryFocus callerContext calleeContext
        sourceModule callerFunction calleeFunction targetModule site row labels
        sourceRuntime continuation callerJoins sourceFrames targetStore
        storedCallerLocals callerRemainder targetRest targetFrames witness
        physicalArgs resultIndex sourceAfter targetAfter := by
  have argumentCompilation :=
    ConstructorArgsCompiled.ofCompileArgs site.argumentsCompiled
  have argumentSize : site.semanticArgs.size = site.args.size := by
    have semanticLength := related.argumentsRelated.semanticLength
    have compiledLength := argumentCompilation.argumentLength
    simpa using semanticLength.trans compiledLength.symm
  have parameterSize :
      site.semanticArgs.size = site.sourceDeclaration.params.size := by
    by_contra different
    have sizeTest :
        (site.sourceDeclaration.params.size == site.semanticArgs.size) =
          false :=
      beq_eq_false_iff_ne.mpr (Ne.symm different)
    have bound := site.parametersBound
    unfold bindParams at bound
    simp [sizeTest] at bound
  have callArgs :
      site.semanticArgs.extract 0 site.sourceDeclaration.params.size =
        site.semanticArgs := by
    simp [← parameterSize]
  have argumentsNonempty : site.semanticArgs.isEmpty = false := by
    simpa [Array.isEmpty, ← argumentSize, ← parameterSize] using site.nonCached
  have parameterCount :
      physicalArgs.reverse.length = row.targetFunction.numParams :=
    row.targetParameterCount site related.argumentsRelated
  have takeParameters :
      (physicalArgs.reverse ++ callerRemainder).take
          row.targetFunction.numParams =
        physicalArgs.reverse := by
    rw [← parameterCount]
    simp
  have dropParameters :
      (physicalArgs.reverse ++ callerRemainder).drop
          row.targetFunction.numParams =
        callerRemainder := by
    rw [← parameterCount]
    simp
  have calleeLocalsRelated :
      EnvLocalsRelated witness (functionBindings calleeFunction)
        site.calleeEnv (row.targetFunction.toLocals physicalArgs) :=
    row.entryEnvLocalsRelatedOfArguments site related.argumentsRelated
  have calleeStateRelated :
      StateRelated calleeFunction sourceRuntime site.calleeEnv targetStore
        (row.targetFunction.toLocals physicalArgs) witness :=
    ⟨related.callerStateRelated.1,
      related.callerStateRelated.2.1, calleeLocalsRelated⟩
  have calleeFrameAligned :
      ConcreteLocalFrameAligned calleeFunction sourceRuntime site.calleeEnv
        targetStore (row.targetFunction.toLocals physicalArgs) witness :=
    row.entryFrameAligned site related.argumentsRelated
  let storedCallerLocals : Wasm.Locals :=
    { callerLocals with
      values := physicalArgs.reverse ++ callerRemainder }
  have storedCallerStateRelated :
      StateRelated callerFunction sourceRuntime callerEnv targetStore
        storedCallerLocals witness := by
    simpa [storedCallerLocals, StateRelated, EnvLocalsRelated,
      Wasm.Locals.get] using related.callerStateRelated
  have storedCallerFrameAligned :
      ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv
        targetStore storedCallerLocals witness := by
    simpa [storedCallerLocals, ConcreteLocalFrameAligned] using
      related.callerFrameAligned
  let sourceAfter : MachineState :=
    { source with
      control := .code site.calleeCode
      env := site.calleeEnv
      joins := [] }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running (row.targetFunction.toLocals physicalArgs)
        row.targetFunction.body
      frames :=
        .call 1 callerRemainder storedCallerLocals
            (.localSet resultIndex :: targetRest) :: targetFrames }
  refine ⟨sourceAfter, targetAfter, storedCallerLocals, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have programEq := related.sourceProgramEq
    change program = callerContext.program at programEq
    subst program
    have controlEq := related.sourceControlEq
    change control = .invokeName site.declaration site.semanticArgs at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = callerEnv at envEq
    subst env
    have runtimeEq := related.sourceRuntimeEq
    change runtime = sourceRuntime at runtimeEq
    subst runtime
    have joinsEq := related.sourceJoinsEq
    change joins = callerJoins at joinsEq
    subst joins
    have framesEq := related.sourceFramesEq
    change frames = _ at framesEq
    subst frames
    simp [sourceAfter, executeStep, coreStep, invokeDecl,
      site.declarationFound, argumentsNonempty, parameterSize, callArgs,
      site.parametersBound, site.bodyEq]
  · have entered :
        StructuredWasmStep targetModule.wasmModule hostEnv target
          targetAfter := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      have controlEq := related.targetControlEq
      change control = .running storedCallerLocals
        (.call row.targetFunctionIndex ::
          .localSet resultIndex :: targetRest) at controlEq
      subst control
      have framesEq := related.targetFramesEq
      change frames = targetFrames at framesEq
      subst frames
      simpa only [targetAfter, storedCallerLocals, takeParameters,
        dropParameters, row.singleResult, List.reverse_reverse] using
        (StructuredWasmStep.enterCall
          (module := targetModule.wasmModule) (env := hostEnv)
          (id := row.targetFunctionIndex) (function := row.targetFunction)
          (store := targetStore) (locals := storedCallerLocals)
          (rest := .localSet resultIndex :: targetRest)
          (frames := targetFrames) row.notImport row.targetFunctionFound)
    exact .single entered
  · refine {
      calleeFocus := ?_
      sourceFramesEq := by simp [sourceAfter, related.sourceFramesEq]
      targetFramesEq := by simp [targetAfter]
      continuationAdapted := related.continuationAdapted
      callerStateRelated := storedCallerStateRelated
      callerFrameAligned := storedCallerFrameAligned
      resultFound := related.resultFound
      resultKindAt := related.resultKindAt
      argumentsRelated := related.argumentsRelated }
    exact {
      sourceProgramEq := by
        calc
          sourceAfter.program = callerContext.program := by
            simp [sourceAfter, related.sourceProgramEq]
          _ = calleeContext.program := row.contextProgram.symm
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      adapted := row.bodyAdapted
      stateRelated := calleeStateRelated
      frameAligned := calleeFrameAligned }

/-- Entry-to-current runtime transports preserve a suspended caller's local
relation.  The current callee relation supplies the evolved runtime and clear
failure channel; the accumulated witness transport reinterprets every saved
caller local at the current witness without changing either the source
environment or the physical local frame. -/
theorem ReuseCapacityCodeEntryTransports.savedStateRelated
    {entryRuntime currentRuntime : RuntimeState}
    {entryStore currentStore : Wasm.Store Host}
    {entryWitness currentWitness : RefinementWitness}
    {entryFunction currentFunction : Fir.Wasm.Function}
    {entryEnv currentEnv : Env}
    {entryLocals currentLocals : Wasm.Locals}
    (transports :
      ReuseCapacityCodeEntryTransports entryRuntime currentRuntime entryStore
        currentStore entryWitness currentWitness)
    (entryRelated :
      StateRelated entryFunction entryRuntime entryEnv entryStore entryLocals
        entryWitness)
    (currentRelated :
      StateRelated currentFunction currentRuntime currentEnv currentStore
        currentLocals currentWitness) :
    StateRelated entryFunction currentRuntime entryEnv currentStore entryLocals
      currentWitness := by
  exact ⟨currentRelated.1, currentRelated.2.1,
    EnvLocalsRelated.witnessTransport transports.witness entryRelated.2.2⟩

/-- Strengthen a structured direct-call entry with the canonical hereditary
cache frame used by the existing W6 operation-family induction.  The callee
starts with empty reuse facts and reflexive entry transports; its runtime,
budget, handler, cache, ownership, and immutable-table invariants come from
the caller frame through the generated declaration row. -/
theorem
    ConcreteStructuredDirectCallEntryFocus.calleeEntryRelativeCacheFrame
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {entryRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {entryWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {entrySource : MachineState}
    {entryTarget : StructuredWasmState Host}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    (entry : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels entryRuntime continuation callerJoins sourceFrames
      entryStore callerLocals callerRemainder targetRest targetFrames
      entryWitness physicalArgs resultIndex entrySource entryTarget)
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes entryRuntime callerEnv entryStore callerLocals
        entryWitness) :
    ReuseCapacityEntryRelativeFrame
      (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals)
      entryRuntime entryStore entryWitness [] remainingBytes entryRuntime
      site.calleeEnv entryStore (row.targetFunction.toLocals physicalArgs)
      entryWitness := by
  exact
    ⟨callerFrame.generatedDirectCalleeEntry site row entry.argumentsRelated,
      ReuseCapacityCodeEntryTransports.refl entryRuntime entryStore
        entryWitness⟩

/-- One saved source bind frame corresponds to the generated call frame whose
caller residual program stores the single returned value and continues with
the adapted source continuation.  Target-only label/loop frames may surround
this constructor later; they are not falsely identified with source frames. -/
structure ConcreteStructuredBindFrameFocus
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (callerEnv : Env)
    (sourceValue : Value)
    (result : Lean.FVarId)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (returnedTail : List Wasm.Value)
    (witness : RefinementWitness)
    (kind : AbiKind)
    (physical : Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = context.program
  sourceControlEq : source.control = .yielded sourceValue
  sourceRuntimeEq : source.runtime = sourceRuntime
  sourceFramesEq :
    source.frames = .bind result continuation callerEnv callerJoins ::
      sourceFrames
  targetStoreEq : target.store = targetStore
  targetControlEq :
    target.control = .returning (physical :: returnedTail)
  targetFramesEq :
    target.frames =
      .call 1 callerRemainder callerLocals
          (.localSet resultIndex :: targetRest) :: targetFrames
  continuationAdapted :
    CodeAdapted context sourceModule sourceFunction labels continuation
      targetRest
  stateRelated :
    StateRelated sourceFunction sourceRuntime callerEnv targetStore callerLocals
      witness
  frameAligned :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime callerEnv targetStore
      callerLocals witness
  resultFound :
    findFVar? (functionBindings sourceFunction) result = some resultIndex
  kindAt :
    (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind
  valueRelated : PhysicalValueRel witness kind physical sourceValue

theorem ConcreteStructuredBindFrameFocus.observes
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels sourceRuntime callerEnv sourceValue result
      continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail witness kind physical
      resultIndex source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.trace

/-- Close the hereditary direct-call scope at a related callee yield.

The callee's current state relation and the accumulated entry transports
reconstruct the saved caller relation at the evolved store and witness.  The
explicit frame equalities state that nested administrative work has unwound
back to this call boundary.  The result is exactly the previously accepted
bind-frame focus, ready for `ConcreteStructuredBindFrameFocus.advance`; no
pre-call store equality or target-execution certificate is assumed. -/
theorem ConcreteStructuredDirectCallEntryFocus.bindFrame_of_yield
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {entryRuntime currentRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryStore currentStore : Wasm.Store Host}
    {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {entryWitness currentWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {entrySource : MachineState}
    {entryTarget : StructuredWasmState Host}
    {currentEnv : Env}
    {sourceValue : Value}
    {actualKind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (entry : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels entryRuntime continuation callerJoins sourceFrames
      entryStore callerLocals callerRemainder targetRest targetFrames
      entryWitness physicalArgs resultIndex entrySource entryTarget)
    (yielded : ConcreteStructuredYieldFocus calleeContext calleeFunction
      currentRuntime currentEnv sourceValue currentStore calleeLocals
      currentWitness actualKind physical source target)
    (transports :
      ReuseCapacityCodeEntryTransports entryRuntime currentRuntime entryStore
        currentStore entryWitness currentWitness)
    (sourceFramesEq :
      source.frames =
        .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames)
    (targetFramesEq :
      target.frames =
        .call 1 callerRemainder callerLocals
            (.localSet resultIndex :: targetRest) :: targetFrames)
    (resultRefines : actualKind.refines site.resultKind = true) :
    ConcreteStructuredBindFrameFocus callerContext sourceModule callerFunction
      labels currentRuntime callerEnv sourceValue decl.fvarId continuation
      callerJoins sourceFrames currentStore callerLocals callerRemainder
      targetRest targetFrames calleeLocals.values currentWitness site.resultKind
      physical resultIndex source target := by
  have callerStateRelated :
      StateRelated callerFunction currentRuntime callerEnv currentStore
        callerLocals currentWitness :=
    transports.savedStateRelated entry.callerStateRelated yielded.stateRelated
  have callerFrameAligned :
      ConcreteLocalFrameAligned callerFunction currentRuntime callerEnv
        currentStore callerLocals currentWitness := by
    simpa [ConcreteLocalFrameAligned] using entry.callerFrameAligned
  exact {
    sourceProgramEq := yielded.sourceProgramEq.trans row.contextProgram
    sourceControlEq := yielded.sourceControlEq
    sourceRuntimeEq := yielded.sourceRuntimeEq
    sourceFramesEq
    targetStoreEq := yielded.targetStoreEq
    targetControlEq := yielded.targetControlEq
    targetFramesEq
    continuationAdapted := entry.continuationAdapted
    stateRelated := callerStateRelated
    frameAligned := callerFrameAligned
    resultFound := entry.resultFound
    kindAt := entry.resultKindAt
    valueRelated := yielded.valueRelated.ofRefines resultRefines }

/-- Entry-relative cache-frame specialization of `bindFrame_of_yield`.

This is the direct composition point with the established hereditary runtime
proof: its final frame already contains the accumulated entry transports, so
clients need not unpack or restate witness/capacity/ownership transport when
closing a structured call. -/
theorem
    ConcreteStructuredDirectCallEntryFocus.bindFrame_of_yield_cacheFrame
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {entryRuntime currentRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryStore currentStore : Wasm.Store Host}
    {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {entryWitness currentWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {entrySource : MachineState}
    {entryTarget : StructuredWasmState Host}
    {currentEnv : Env}
    {sourceValue : Value}
    {actualKind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    {resultFacts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    (entry : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels entryRuntime continuation callerJoins sourceFrames
      entryStore callerLocals callerRemainder targetRest targetFrames
      entryWitness physicalArgs resultIndex entrySource entryTarget)
    (yielded : ConcreteStructuredYieldFocus calleeContext calleeFunction
      currentRuntime currentEnv sourceValue currentStore calleeLocals
      currentWitness actualKind physical source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals)
        entryRuntime entryStore entryWitness resultFacts remainingBytes
        currentRuntime currentEnv currentStore calleeLocals currentWitness)
    (sourceFramesEq :
      source.frames =
        .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames)
    (targetFramesEq :
      target.frames =
        .call 1 callerRemainder callerLocals
            (.localSet resultIndex :: targetRest) :: targetFrames)
    (resultRefines : actualKind.refines site.resultKind = true) :
    ConcreteStructuredBindFrameFocus callerContext sourceModule callerFunction
      labels currentRuntime callerEnv sourceValue decl.fvarId continuation
      callerJoins sourceFrames currentStore callerLocals callerRemainder
      targetRest targetFrames calleeLocals.values currentWitness site.resultKind
      physical resultIndex source target :=
  entry.bindFrame_of_yield yielded invariant.2 sourceFramesEq targetFramesEq
    resultRefines

/-- Resuming a related bind/call frame takes one source administrative step
and exactly two structured target steps: unwind the call frame, then store the
returned physical value.  The resulting source code and target residual code
re-enter `ConcreteStructuredCodeFocus` with the semantic result bound in the
caller environment. -/
theorem ConcreteStructuredBindFrameFocus.advance
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels sourceRuntime callerEnv sourceValue result
      continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail witness kind physical
      resultIndex source target) :
    ∃ sourceAfter targetAfter resumedLocals,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime (bind callerEnv result sourceValue) continuation
        targetStore resumedLocals targetRest witness sourceAfter targetAfter := by
  obtain ⟨updated, targetSet, updatedAligned⟩ :=
    related.frameAligned.set?
      (nextRuntime := sourceRuntime)
      (nextEnv := bind callerEnv result sourceValue)
      (nextStore := targetStore)
      (nextWitness := witness)
      related.resultFound
  let resumedLocals : Wasm.Locals :=
    { updated with values := callerRemainder }
  have updatedRelated :
      StateRelated sourceFunction sourceRuntime
        (bind callerEnv result sourceValue) targetStore resumedLocals witness := by
    have bound := related.stateRelated.bindPhysical related.resultFound
      related.kindAt related.valueRelated targetSet
    rw [related.stateRelated.clearFailure] at bound
    simpa [resumedLocals, StateRelated, EnvLocalsRelated, Wasm.Locals.get]
      using bound
  have resumedAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime
        (bind callerEnv result sourceValue) targetStore resumedLocals witness := by
    simpa [resumedLocals, ConcreteLocalFrameAligned] using updatedAligned
  let sourceAfter : MachineState :=
    { source with
      control := .code continuation
      env := bind callerEnv result sourceValue
      joins := callerJoins
      frames := sourceFrames }
  let targetAfterCall : StructuredWasmState Host :=
    { target with
      control := .running
        { callerLocals with
          values := physical :: callerRemainder }
        (.localSet resultIndex :: targetRest)
      frames := targetFrames }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running resumedLocals targetRest
      frames := targetFrames }
  refine ⟨sourceAfter, targetAfter, resumedLocals, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = .yielded sourceValue at controlEq
    subst control
    have framesEq := related.sourceFramesEq
    change frames = _ at framesEq
    subst frames
    simp [sourceAfter, executeStep, coreStep]
  · have unwindStep :
        StructuredWasmStep module hostEnv target targetAfterCall := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      have controlEq := related.targetControlEq
      change control = .returning (physical :: returnedTail) at controlEq
      subst control
      have framesEq := related.targetFramesEq
      change frames = _ at framesEq
      subst frames
      exact StructuredWasmStep.returnCall
    have stackSet :
        ({ callerLocals with
            values := physical :: callerRemainder }.set? resultIndex physical) =
          some { updated with values := physical :: callerRemainder } :=
      locals_set?_with_values (physical :: callerRemainder) targetSet
    have storeStep :
        StructuredWasmStep module hostEnv targetAfterCall targetAfter := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      apply StructuredWasmStep.atomic (fuel := 1)
      · trivial
      · simp only [Wasm.execOne.eq_def, stackSet]
        rfl
    exact .cons unwindStep (.cons storeStep (.refl targetAfter))
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      adapted := related.continuationAdapted
      stateRelated := updatedRelated
      frameAligned := resumedAligned }

/-- Simulation-facing bind-frame rule.  Determinism identifies the successor
constructed by `advance` with the successor supplied by the generic source
transition premise. -/
theorem ConcreteStructuredBindFrameFocus.advance_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels sourceRuntime callerEnv sourceValue result
      continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail witness kind physical
      resultIndex source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter resumedLocals,
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime (bind callerEnv result sourceValue) continuation
        targetStore resumedLocals targetRest witness sourceAfter targetAfter := by
  obtain ⟨computedAfter, targetAfter, resumedLocals, computedStep, path,
      focus⟩ := related.advance (module := module) (hostEnv := hostEnv)
        (externals := externals)
  have afterEq : sourceAfter = computedAfter := by
    rw [sourceStep] at computedStep
    injection computedStep
  subst computedAfter
  exact ⟨targetAfter, resumedLocals, path, focus⟩

/-- Structural rank used when lowering erases a source control step.  Later
frame slices add their own continuation component; the local erased-step laws
need only this strictly decreasing code-control component. -/
def compilerCodeSilenceDepth : Lean.Compiler.LCNF.Code .impure → Nat
  | .inc _ _ _ true continuation =>
      compilerCodeSilenceDepth continuation + 1
  | .dec _ _ _ true _ continuation =>
      compilerCodeSilenceDepth continuation + 1
  | _ => 0

def compilerCodeSilenceRank (state : MachineState) : Nat :=
  match state.control with
  | .code code => compilerCodeSilenceDepth code
  | _ => 0

/-- A persistent increment is one source step, no target steps, and a strict
drop in the local silence rank. -/
theorem ConcreteStructuredCodeFocus.advance_incPersistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.inc objectId amount check true continuation) targetStore targetLocals
      targetCode witness source target) :
    ∃ sourceAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime sourceEnv continuation targetStore targetLocals targetCode
        witness sourceAfter target ∧
      compilerCodeSilenceRank sourceAfter < compilerCodeSilenceRank source := by
  let sourceAfter : MachineState :=
    { source with control := .code continuation }
  refine ⟨sourceAfter, ?_, .refl target, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = _ at controlEq
    subst control
    rfl
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := related.targetStoreEq
      targetControlEq := related.targetControlEq
      adapted := CodeAdapted.incPersistent_eq related.adapted
      stateRelated := related.stateRelated
      frameAligned := related.frameAligned }
  · simp [compilerCodeSilenceRank, compilerCodeSilenceDepth, sourceAfter,
      related.sourceControlEq]

/-- A persistent decrement has the same ranked zero-step target match as a
persistent increment. -/
theorem ConcreteStructuredCodeFocus.advance_decPersistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) targetStore
      targetLocals targetCode witness source target) :
    ∃ sourceAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime sourceEnv continuation targetStore targetLocals targetCode
        witness sourceAfter target ∧
      compilerCodeSilenceRank sourceAfter < compilerCodeSilenceRank source := by
  let sourceAfter : MachineState :=
    { source with control := .code continuation }
  refine ⟨sourceAfter, ?_, .refl target, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = _ at controlEq
    subst control
    rfl
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := related.targetStoreEq
      targetControlEq := related.targetControlEq
      adapted := CodeAdapted.decPersistent_eq related.adapted
      stateRelated := related.stateRelated
      frameAligned := related.frameAligned }
  · simp [compilerCodeSilenceRank, compilerCodeSilenceDepth, sourceAfter,
      related.sourceControlEq]

end FirTalos.Concrete
