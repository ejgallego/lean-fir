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

/-- Compiler-derived admission for one currently executing ordinary-code node.

The law is local to the successful source step presented to the simulation.
It recovers only the source/compiler admission and its exact allocation cost;
it contains no target execution, successor admission, recursive evaluator,
termination evidence, or address-space claim. -/
structure ConcreteStructuredCompilerCurrentStepAdmission
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  code :
    ∀ {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      (spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts)
      {labels : List Lean.FVarId}
      {entryRuntime sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : Fir.Wasm.Concrete.RefinementWitness}
      {functionResult : Fir.Wasm.AbiKind}
      {callerExpectedResult : Option Fir.Wasm.AbiKind}
      {facts : Fir.Wasm.ReuseCapacityFacts}
      {remainingBytes : Nat}
      {sourceEnv : Fir.LeanIR.Impure.Env}
      {sourceCode : Lean.Compiler.LCNF.Code .impure}
      {targetLocals : Wasm.Locals}
      {targetCode : Wasm.Program}
      {source sourceAfter : Fir.LeanIR.Impure.MachineState}
      {target : StructuredWasmState Host},
      ConcreteStructuredCodeCoreRel program context sourceModule
          sourceFunction externals labels entryRuntime entryStore entryWitness
          functionResult callerExpectedResult facts remainingBytes sourceRuntime
          sourceEnv sourceCode targetStore targetLocals targetCode witness source
          target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ∃ requiredBytes,
          ConcreteStructuredCodeStepAdmission context sourceModule externals functionResult
            facts sourceRuntime sourceEnv requiredBytes sourceCode

/-- Dynamic finite-address-space safety for an admitted ordinary-code step.

Unlike compiler admission, this law is indexed by the concrete frame's
current `remainingBytes`.  It says that the exact cost selected by admission
fits that retained wasm32 budget.  It is intentionally a separate execution
premise: lowering an unbounded source program cannot establish it. -/
structure ConcreteStructuredCurrentStepAddressSpaceSafety
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  code :
    ∀ {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      (spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts)
      {labels : List Lean.FVarId}
      {entryRuntime sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
      {entryStore targetStore : Wasm.Store Host}
      {entryWitness witness : Fir.Wasm.Concrete.RefinementWitness}
      {functionResult : Fir.Wasm.AbiKind}
      {callerExpectedResult : Option Fir.Wasm.AbiKind}
      {facts : Fir.Wasm.ReuseCapacityFacts}
      {requiredBytes remainingBytes : Nat}
      {sourceEnv : Fir.LeanIR.Impure.Env}
      {sourceCode : Lean.Compiler.LCNF.Code .impure}
      {targetLocals : Wasm.Locals}
      {targetCode : Wasm.Program}
      {source sourceAfter : Fir.LeanIR.Impure.MachineState}
      {target : StructuredWasmState Host},
      ConcreteStructuredCodeCoreRel program context sourceModule
          sourceFunction externals labels entryRuntime entryStore entryWitness
          functionResult callerExpectedResult facts remainingBytes sourceRuntime
          sourceEnv sourceCode targetStore targetLocals targetCode witness source
          target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ConcreteStructuredCodeStepAdmission context sourceModule externals
            functionResult facts sourceRuntime sourceEnv requiredBytes sourceCode →
        requiredBytes ≤ remainingBytes

/-- Compatibility package for clients that already possess both independent
laws.  The compiler-owned field cannot manufacture the execution-owned
address-space premise. -/
structure ConcreteStructuredCompilerCurrentStepCoverage
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  admission : ConcreteStructuredCompilerCurrentStepAdmission program
    sourceModule targetModule hosts externals
  addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
    sourceModule targetModule hosts externals

/-- The split laws reconstruct the former combined current-node conclusion. -/
theorem ConcreteStructuredCompilerCurrentStepCoverage.code
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (coverage : ConcreteStructuredCompilerCurrentStepCoverage program
      sourceModule targetModule hosts externals)
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    (spec : ConcreteSupportedFunction program context functionCode
      sourceModule sourceFunction targetModule hosts)
    (core : ConcreteStructuredCodeCoreRel program context sourceModule
      sourceFunction externals labels entryRuntime entryStore entryWitness
      functionResult callerExpectedResult facts remainingBytes sourceRuntime
      sourceEnv sourceCode targetStore targetLocals targetCode witness source
      target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ requiredBytes,
      ConcreteStructuredCodeStepAdmission context sourceModule externals
          functionResult facts sourceRuntime sourceEnv requiredBytes sourceCode ∧
        requiredBytes ≤ remainingBytes := by
  obtain ⟨requiredBytes, admitted⟩ :=
    coverage.admission.code spec core sourceStep
  exact ⟨requiredBytes, admitted,
    coverage.addressSpaceSafety.code spec core sourceStep admitted⟩

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

/-- Compiler admission plus independent address-space safety discharge the
only non-structural branch of the global classifier.

Ordinary code asks the coverage law for its source-only admission and budget.
The six staged call/cache/bind/return shapes are already branch-exact in the
strong supported outcome, so their runnable constructors are recovered by
inversion.
No future source transition or target execution is inspected. -/
theorem ConcreteStructuredCompilerCurrentStepAdmission.toCurrentStepClassifier
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals) :
    ConcreteStructuredCurrentStepClassifier program sourceModule targetModule
      hosts externals where
  classify := by
    intro source sourceAfter target related sourceStep
    rcases related with
      ⟨context, functionCode, sourceFunction, spec, labels, entryRuntime,
        entryStore, entryWitness, functionResult, callerExpectedResult,
        activeResult, active⟩
    cases active with
    | code contextCaches core supported agrees =>
        obtain ⟨requiredBytes, admitted⟩ :=
          admission.code spec core sourceStep
        have budget :=
          addressSpaceSafety.code spec core sourceStep admitted
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec)
          (activeResult := activeResult)
        exact .code (core.withAdmission contextCaches admitted budget) supported
          agrees
    | directReady ready contextCaches supported agrees =>
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec)
          (activeResult := activeResult)
        exact .directReady ready contextCaches supported agrees
    | saturatedReady row sharedCapacity ready contextCaches supported agrees =>
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec)
          (activeResult := activeResult)
        exact .saturatedReady row sharedCapacity ready contextCaches supported
          agrees
    | lazyReady path ready contextCaches supported agrees =>
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec)
          (activeResult := activeResult)
        exact .lazyReady path ready contextCaches supported agrees
    | externalReady ready contextCaches supported agrees =>
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec)
          (activeResult := activeResult)
        exact .externalReady ready contextCaches supported agrees
    | externalBind bindCore contextCaches supported agrees =>
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec)
          (activeResult := activeResult)
        exact .externalBind bindCore contextCaches supported agrees
    | returned yielded compatible resources contextCaches supported agrees =>
        apply ConcreteStructuredRunnableOutcome.toRunnableGlobal
          (functionCode := functionCode) (spec := spec) (labels := labels)
          (activeResult := activeResult)
        exact .returned yielded compatible resources contextCaches supported agrees

/-- Compatibility projection for callers that already package the two laws. -/
theorem ConcreteStructuredCompilerCurrentStepCoverage.toCurrentStepClassifier
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (coverage : ConcreteStructuredCompilerCurrentStepCoverage program
      sourceModule targetModule hosts externals) :
    ConcreteStructuredCurrentStepClassifier program sourceModule targetModule
      hosts externals :=
  coverage.admission.toCurrentStepClassifier coverage.addressSpaceSafety

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

/-- The orthogonal admission and address-space laws directly construct the
ranked generated trace simulation; callers never supply the intermediate
global classifier. -/
def ConcreteStructuredCompilerCurrentStepAdmission.toGeneratedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule
      hosts.env :=
  (admission.toCurrentStepClassifier addressSpaceSafety).toGeneratedTraceSimulation

/-- Compatibility wrapper for the paired coverage package. -/
def ConcreteStructuredCompilerCurrentStepCoverage.toGeneratedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (coverage : ConcreteStructuredCompilerCurrentStepCoverage program
      sourceModule targetModule hosts externals) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule
      hosts.env :=
  coverage.admission.toGeneratedTraceSimulation coverage.addressSpaceSafety

/-- Independent compiler admission and execution resource safety, together
with an admission-free initial relation, imply finite-prefix correctness. -/
theorem ConcreteStructuredCompilerCurrentStepAdmission.toFiniteTraceCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    {sourceInitial : Fir.LeanIR.Impure.MachineState}
    {targetInitial : StructuredWasmState Host}
    (initial : ConcreteStructuredSupportedGlobalOutcome program sourceModule
      targetModule hosts externals sourceInitial targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  (admission.toCurrentStepClassifier addressSpaceSafety).toFiniteTraceCorrect
    initial

/-- Combined current-node coverage and the admission-free compiler root imply
finite-prefix correctness of the concrete structured Wasm machine. -/
theorem ConcreteStructuredCompilerCurrentStepCoverage.toFiniteTraceCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (coverage : ConcreteStructuredCompilerCurrentStepCoverage program
      sourceModule targetModule hosts externals)
    {sourceInitial : Fir.LeanIR.Impure.MachineState}
    {targetInitial : StructuredWasmState Host}
    (initial : ConcreteStructuredSupportedGlobalOutcome program sourceModule
      targetModule hosts externals sourceInitial targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  coverage.admission.toFiniteTraceCorrect coverage.addressSpaceSafety initial

/-- Combined current-step coverage plus the ordinary concrete export-entry
frame imply finite-prefix correctness at the actual source and structured-Wasm
entries.

Unlike `ConcreteStructuredCompilerCurrentStepCoverage.toFiniteTraceCorrect`,
this export-facing bridge does not ask its caller to construct the simulation's
initial relation. `ConcreteSupportedExport.supportedGlobalRoot` derives it
from production lowering/adaptation and the concrete cache/ABI frame. The
remaining `coverage` premise contains no target path or future execution
evidence, but it does include the explicit wasm32 address-space safety law
described on `ConcreteStructuredCompilerCurrentStepCoverage`. -/
theorem ConcreteSupportedExport.finiteTraceCorrect_of_currentStepCoverage
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (coverage : ConcreteStructuredCompilerCurrentStepCoverage program
      sourceModule targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {initial : Wasm.Store Host}
    {initialWitness : Fir.Wasm.Concrete.RefinementWitness}
    {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  coverage.toFiniteTraceCorrect
    (spec.supportedGlobalRoot contextCaches invariant)

/-- Export-facing finite-prefix correctness with compiler admission and
finite-memory safety stated as visibly independent hypotheses.

This is the preferred theorem surface.  In particular, a future unconditional
compiler theorem may discharge `admission` without acquiring any obligation
to prove that an arbitrary or unbounded execution fits wasm32 memory. -/
theorem ConcreteSupportedExport.finiteTraceCorrect_of_currentStepAdmission
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {initial : Wasm.Store Host}
    {initialWitness : Fir.Wasm.Concrete.RefinementWitness}
    {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  admission.toFiniteTraceCorrect addressSpaceSafety
    (spec.supportedGlobalRoot contextCaches invariant)

end FirTalos.Concrete
