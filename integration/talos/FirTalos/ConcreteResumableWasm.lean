import FirTalos.ConcreteTraceSimulation
import FirTalos.ConcreteStructuredSimulation
import FirTalos.Correctness.ResumableWasm
import FirTalos.Correctness.StructuredWasmAdequacy

/-!
# Concrete W6 resumable Wasm machine

This module instantiates the instruction-boundary semantics with the concrete
W6 host.  It is the target machine used by `ConcreteRankedTraceSimulation`;
the generic adequacy theorems in `Correctness.ResumableWasm` then reconnect a
finite completed path to the executable Talos `Wasm.run` result.
-/

namespace FirTalos.Concrete

open FirTalos.Correctness

/-- The actual resumable target for a concrete FIR-generated module. -/
def concreteResumableWasmMachine
    (module : Wasm.Module) (env : Wasm.HostEnv Host) :
    ConcreteResumableMachine where
  State := ResumableWasmState Host
  step := ResumableWasmStep module env
  store := ResumableWasmState.store

@[simp] theorem concreteResumableWasmMachine_store
    (module : Wasm.Module) (env : Wasm.HostEnv Host)
    (state : ResumableWasmState Host) :
    (concreteResumableWasmMachine module env).store state = state.store :=
  rfl

/-- The frame-stack target that exposes progress inside emitted calls and
structured control. -/
def concreteStructuredWasmMachine
    (module : Wasm.Module) (env : Wasm.HostEnv Host) :
    ConcreteResumableMachine where
  State := StructuredWasmState Host
  step := StructuredWasmStep module env
  store := StructuredWasmState.store

@[simp] theorem concreteStructuredWasmMachine_store
    (module : Wasm.Module) (env : Wasm.HostEnv Host)
    (state : StructuredWasmState Host) :
    (concreteStructuredWasmMachine module env).store state = state.store :=
  rfl

/-- The exact compiler proof object now has a concrete instruction-boundary
target.  This abbreviation keeps module and host selection explicit at the
public theorem boundary. -/
def ConcreteGeneratedTraceSimulation
    (externals : Fir.LeanIR.Impure.ExternalImpl) (module : Wasm.Module)
    (env : Wasm.HostEnv Host) : Type :=
  ConcreteRankedTraceSimulation externals
    (concreteStructuredWasmMachine module env)

/-- Source-local closure of the strong compiler relation.

The classifier is applied only after the current source transition is known.
It reconstructs the current node's runnable evidence from the admission-free
supported relation; it stores no successor admission, future execution, target
path, or termination evidence.  The eventual public export theorem derives
this interface from compiler coverage instead of asking its caller to provide
it. -/
structure ConcreteStructuredCurrentStepClassifier
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  classify :
    ∀ {source sourceAfter : Fir.LeanIR.Impure.MachineState}
      {target : StructuredWasmState Host},
      ConcreteStructuredSupportedGlobalOutcome program sourceModule
          targetModule hosts externals source target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ConcreteStructuredRunnableGlobalOutcome program sourceModule
          targetModule hosts externals source target

/-- A source-local current-step classifier closes the admission-free strong
relation into the generic ranked finite-prefix simulation object.  This is the
central W6.7e-to-W6.7f bridge: its relation is stable across every step, while
runnable evidence is reconstructed only for the current transition. -/
def ConcreteStructuredCurrentStepClassifier.toGeneratedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (classifier : ConcreteStructuredCurrentStepClassifier program sourceModule
      targetModule hosts externals) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule
      hosts.env where
  relation := ConcreteStructuredSupportedGlobalOutcome program sourceModule
    targetModule hosts externals
  rank := compilerStructuredControlRank
  observes := by
    intro sourceState targetState related
    exact related.observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related sourceStep
    exact (classifier.classify related sourceStep).advance sourceStep

/-- Intermediate certificate-free finite-trace packaging theorem.

The two remaining compiler obligations are now explicit and orthogonal: prove
the universal current-step classifier, and construct the admission-free strong
relation at the compiler-produced root entry.  Neither obligation exposes a
target execution path or a simulation relation to the eventual public caller. -/
theorem ConcreteStructuredCurrentStepClassifier.toFiniteTraceCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (classifier : ConcreteStructuredCurrentStepClassifier program sourceModule
      targetModule hosts externals)
    {sourceInitial : Fir.LeanIR.Impure.MachineState}
    {targetInitial : StructuredWasmState Host}
    (initial : ConcreteStructuredSupportedGlobalOutcome program sourceModule
      targetModule hosts externals sourceInitial targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  ⟨classifier.toGeneratedTraceSimulation, initial⟩

end FirTalos.Concrete
