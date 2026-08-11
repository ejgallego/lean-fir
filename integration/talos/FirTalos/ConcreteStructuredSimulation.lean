import FirTalos.ConcreteTraceSimulation
import FirTalos.ConcreteCompilerCorrectness
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
