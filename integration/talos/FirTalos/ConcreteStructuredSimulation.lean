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
      stateRelated := related.stateRelated }
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
      stateRelated := related.stateRelated }
  · simp [compilerCodeSilenceRank, compilerCodeSilenceDepth, sourceAfter,
      related.sourceControlEq]

end FirTalos.Concrete
