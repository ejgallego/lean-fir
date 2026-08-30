import FirTalos.ConcreteTraceSimulation
import FirTalos.ConcreteStructuredSimulation
import FirTalos.ConcreteStructuredValidation
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
It receives the exact recursively validated current outcome, then recovers
only the source/compiler admission and its exact allocation cost. Requiring
that outcome is essential: residual validator facts cannot be reconstructed
from the admission-free operational core alone. The law contains no target
execution, successor admission, recursive evaluator, termination evidence, or
address-space claim. -/
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
      {labels : LabelContext}
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
      spec.sourceResultKind = functionResult →
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          sourceCode targetStore targetLocals targetCode witness source target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ∃ requiredBytes,
          ConcreteStructuredCodeStepAdmission context sourceModule externals functionResult
            facts sourceRuntime sourceEnv requiredBytes sourceCode

/-- Source/phase readiness of one concrete source state.

The premise is the recursively validated compiler relation, so this law ranges
only over a genuine residual node reached from a validated production root.
It records the semantic facts not derivable from executable validation alone:
return value shape, descriptor typing, normalized cases, and the current
call/external/cache domain.  It contains no future execution or target path. -/
structure ConcreteStructuredSourceReadyAt
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (source : Fir.LeanIR.Impure.MachineState) : Prop where
  code :
    ∀ {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      (spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts)
      {labels : LabelContext}
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
      {sourceAfter : Fir.LeanIR.Impure.MachineState}
      {target : StructuredWasmState Host},
      (activeResult : spec.sourceResultKind = functionResult) →
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          sourceCode targetStore targetLocals targetCode witness source target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ConcreteStructuredSourceAdmissionSafeAt context sourceModule externals
          functionResult facts sourceRuntime sourceEnv source sourceCode

/-- Source/phase readiness with explicit constructor-schema provenance.

The shape is intentionally parallel to `ConcreteStructuredSourceReadyAt` so
final-LCNF type safety can migrate one current-node case at a time. Its field
result is the schema admission boundary: all established cases may use the
legacy alternative, while FVar and erased object-field writes use source
schema typing and never quantify over unrelated refinement witnesses. -/
structure ConcreteStructuredSchemaSourceReadyAt
    (schema : ConstructorSchema)
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (source : Fir.LeanIR.Impure.MachineState) : Prop where
  code :
    ∀ {context : Fir.Wasm.Context}
      {functionCode : Lean.Compiler.LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      (spec : ConcreteSupportedFunction program context functionCode
        sourceModule sourceFunction targetModule hosts)
      {labels : LabelContext}
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
      {sourceAfter : Fir.LeanIR.Impure.MachineState}
      {target : StructuredWasmState Host},
      (activeResult : spec.sourceResultKind = functionResult) →
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          sourceCode targetStore targetLocals targetCode witness source target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ConcreteStructuredSchemaSourceAdmissionSafeAt schema context
          sourceModule externals functionResult facts sourceRuntime sourceEnv
          source sourceCode

/-- Schema-indexed source invariant used by the constructor-provenance
simulation.

Readiness is required only for the schema paired with the current source
state.  Preservation follows the exact source/compiler schema transition;
there is no universal quantification over unrelated schemas or concrete
refinement witnesses. -/
structure ConcreteStructuredSchemaSourceInvariantLaws
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (Invariant : Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop) :
    Prop where
  ready : ∀ {source schema}, Invariant source schema →
    ConcreteStructuredSchemaSourceReadyAt schema program sourceModule
      targetModule hosts externals source
  preserved : ∀ {source sourceAfter schema nextSchema},
    Invariant source schema →
      ConstructorSchema.SourceStep externals source sourceAfter schema
          nextSchema →
        Invariant sourceAfter nextSchema

/-- Validated compiler state, active witness/schema agreement, and the
source-only invariant at the same schema index. -/
def ConcreteStructuredSchemaValidatedInvariantGlobalOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (Invariant : Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop)
    (source : Fir.LeanIR.Impure.MachineState)
    (target : StructuredWasmState Host) : Prop :=
  ∃ (schema : ConstructorSchema)
      (witness : Fir.Wasm.Concrete.RefinementWitness),
    Invariant source schema ∧ schema.WitnessAgrees witness ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals witness source target

/-- The transition-retaining validated successor composes directly with a
schema-indexed source invariant. -/
theorem ConcreteStructuredSchemaValidatedCodeStepOutcome.withInvariant
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop}
    (laws : ConcreteStructuredSchemaSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {schema : ConstructorSchema}
    {targetAfter : StructuredWasmState Host}
    (sourceInvariant : Invariant source schema)
    (related : ConcreteStructuredSchemaValidatedCodeStepOutcome program
      sourceModule targetModule hosts externals source sourceAfter schema
      targetAfter) :
    ConcreteStructuredSchemaValidatedInvariantGlobalOutcome program
      sourceModule targetModule hosts externals Invariant sourceAfter
      targetAfter := by
  obtain ⟨nextSchema, nextWitness, transition, agrees, validated⟩ := related
  exact ⟨nextSchema, nextWitness,
    laws.preserved sourceInvariant transition, agrees, validated⟩

/-- A preserved source semantic invariant supplies current-state readiness.

This is the same ready/preserved interface used by FIR's pass simulations.
The invariant is source-only; compiler validation and concrete runtime
resources stay in their existing independent relations. -/
structure ConcreteStructuredSourceInvariantLaws
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (Invariant : Fir.LeanIR.Impure.MachineState → Prop) : Prop where
  ready : ∀ {source}, Invariant source →
    ConcreteStructuredSourceReadyAt program sourceModule targetModule hosts
      externals source
  preserved : ∀ {source sourceAfter},
    Invariant source →
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        Invariant sourceAfter

/-- Canonical hereditary semantic invariant: every finite source successor is
ready for any validated compiler focus at that state.  Proving this at an
export root is the final-LCNF type-safety obligation; it is not a supplied
source/target execution certificate. -/
def ConcreteStructuredReachablySourceReady
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (source : Fir.LeanIR.Impure.MachineState) : Prop :=
  ∀ {count sourceAfter},
    Fir.LeanIR.Impure.ExecSteps externals count source sourceAfter →
      ConcreteStructuredSourceReadyAt program sourceModule targetModule hosts
        externals sourceAfter

/-- Hereditary source readiness is preserved by path composition. -/
theorem concreteStructuredReachablySourceReadyLaws
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl} :
    ConcreteStructuredSourceInvariantLaws program sourceModule targetModule
      hosts externals
      (ConcreteStructuredReachablySourceReady program sourceModule targetModule
        hosts externals) where
  ready := by
    intro source hereditary
    exact hereditary (.refl source)
  preserved := by
    intro source sourceAfter hereditary sourceStep count final tail
    exact hereditary (.step sourceStep tail)

/-- Compatibility form of source readiness that quantifies over all source
states.  New compiler theorems should prefer a preserved invariant and an
initial proof instead of this module-global law. -/
structure ConcreteStructuredCompilerSourceAdmissionSafety
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  ready : ∀ source,
    ConcreteStructuredSourceReadyAt program sourceModule targetModule hosts
      externals source

/-- Dynamic finite-runtime safety for the selected validated source node.

This law is execution-owned, not compiler-owned.  It currently covers finite
reference-count header headroom and saturated-closure capture retention.  The
separate address-space law below covers allocation bytes against the concrete
frame budget. -/
structure ConcreteStructuredCurrentStepFiniteRuntimeSafety
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
      {labels : LabelContext}
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
      (activeResult : spec.sourceResultKind = functionResult) →
        ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          sourceCode targetStore targetLocals targetCode witness source target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ConcreteStructuredFiniteRuntimeSafeAt context sourceRuntime sourceEnv
          sourceCode

/-- The remaining production-facing source/phase law.

Residual validation is no longer a universal field: it is established at the
real compiler root and transported by `ConcreteStructuredValidatedCodeGlobalOutcome`.
This package contains only the semantic source invariant that executable
validation does not itself establish. -/
structure ConcreteStructuredCompilerAdmissionLaws
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  sourceSafety : ConcreteStructuredCompilerSourceAdmissionSafety program
    sourceModule targetModule hosts externals

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
      {sourceFunction : Fir.Wasm.Function}
      {labels : LabelContext}
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

/-- The active ordinary-code branch advances from schema-aware source
readiness and agreement with its one concrete refinement witness.

Legacy admission keeps the independent address-space premise. The two
schema-typed field mutations have exact cost zero, so they bypass the old
universally witness-quantified admission constructors and dispatch directly to
the active-witness successors. -/
theorem ConcreteStructuredValidatedCodeOutcome.advanceSchemaStep_of_schemaSourceReady
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {schema : ConstructorSchema}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {labels : LabelContext}
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
    {target : StructuredWasmState Host}
    (sourceReady : ConcreteStructuredSchemaSourceReadyAt schema program
      sourceModule targetModule hosts externals source)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (sourceStep : Fir.LeanIR.Impure.executeStep externals source =
      .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  have sourceSafe := sourceReady.code spec activeResult related sourceStep
  have finiteSafe := finiteRuntimeSafety.code spec activeResult related sourceStep
  obtain ⟨requiredBytes, admitted⟩ :=
    related.core.admitSchema_of_source_safe_step sourceSafe finiteSafe sourceStep
  cases admitted with
  | legacy legacyAdmission eligible =>
      have budget := addressSpaceSafety.code related.core.core sourceStep
        legacyAdmission
      exact related.advance_schemaStep_of_schema_admission activeResult
        schemaAgrees
        (.legacy legacyAdmission eligible) budget sourceStep
  | objectFieldFVar fieldTyped =>
      exact related.advance_schemaStep_of_schema_admission activeResult
        schemaAgrees
        (.objectFieldFVar fieldTyped) (Nat.zero_le _) sourceStep
  | objectFieldErased fieldTyped =>
      exact related.advance_schemaStep_of_schema_admission activeResult
        schemaAgrees
        (.objectFieldErased fieldTyped) (Nat.zero_le _) sourceStep

/-- Compatibility projection of schema-aware active-code advancement. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_of_schemaSourceReady
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {schema : ConstructorSchema}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {labels : LabelContext}
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
    {target : StructuredWasmState Host}
    (sourceReady : ConcreteStructuredSchemaSourceReadyAt schema program
      sourceModule targetModule hosts externals source)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (schemaAgrees : schema.WitnessAgrees witness)
    (sourceStep : Fir.LeanIR.Impure.executeStep externals source =
      .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨targetCount, targetAfter, targetPath, next, rank⟩ :=
    related.advanceSchemaStep_of_schemaSourceReady sourceReady
      finiteRuntimeSafety addressSpaceSafety activeResult schemaAgrees sourceStep
  exact ⟨targetCount, targetAfter, targetPath, next.toSchemaGlobal, rank⟩

/-- The witness-indexed validated global relation advances while carrying one
constructor schema through every established outcome shape. Active code uses
schema-aware source readiness and the complete schema-global code dispatcher;
administrative states preserve the witness, except resolved external execution
which transports agreement through its explicit witness extension. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcomeAt.advanceSchemaStep_of_schemaSourceReady
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {schema : ConstructorSchema}
    {witness : Fir.Wasm.Concrete.RefinementWitness}
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {target : StructuredWasmState Host}
    (sourceReady : ConcreteStructuredSchemaSourceReadyAt schema program
      sourceModule targetModule hosts externals source)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (schemaAgrees : schema.WitnessAgrees witness)
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals witness source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeStepOutcome program sourceModule
          targetModule hosts externals source sourceAfter schema targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases related with
  | code activeResult related =>
      exact related.advanceSchemaStep_of_schemaSourceReady sourceReady
        finiteRuntimeSafety addressSpaceSafety activeResult schemaAgrees
        sourceStep
  | directReady related =>
      have noShape : ¬ ∃ nextSchema,
          ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
        simp [ConstructorSchema.DirectLetShapeAt,
          related.core.ready.sourceControlEq]
      obtain ⟨targetAfter, targetPath, next⟩ :=
        related.advance_enter_of_step sourceStep
      exact ⟨1, targetAfter, targetPath,
        next.withSchemaPreservedStep sourceStep noShape schemaAgrees,
        by omega⟩
  | saturatedReady related =>
      have noShape : ¬ ∃ nextSchema,
          ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
        simp [ConstructorSchema.DirectLetShapeAt,
          related.core.ready.sourceControlEq]
      obtain ⟨targetCount, targetAfter, targetPath, targetPositive, next⟩ :=
        related.advance_enter_of_step sourceStep
      exact ⟨targetCount, targetAfter, targetPath,
        next.withSchemaPreservedStep sourceStep noShape schemaAgrees, by omega⟩
  | lazyReady related =>
      have noShape : ¬ ∃ nextSchema,
          ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
        simp [ConstructorSchema.DirectLetShapeAt,
          related.core.ready.sourceControlEq]
      cases related.path with
      | hit sourceValue semanticFound =>
          obtain ⟨physical, targetAfter, targetPath, next⟩ :=
            related.advance_hit_of_step semanticFound sourceStep
          exact ⟨4, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.externalBind next)
              |>.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
      | miss calleeCode internal resultClassified notObject notTObject
          semanticEmpty =>
          obtain ⟨targetAfter, targetPath, next⟩ :=
            related.advance_miss_of_step internal resultClassified notObject
              notTObject semanticEmpty sourceStep
          exact ⟨3, targetAfter, targetPath,
            next.withSchemaPreservedStep sourceStep noShape schemaAgrees,
            by omega⟩
  | externalReady related =>
      have noShape : ¬ ∃ nextSchema,
          ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
        simp [ConstructorSchema.DirectLetShapeAt,
          related.core.ready.sourceControlEq]
      obtain ⟨nextWitness, targetAfter, targetPath, witnessExtension, next⟩ :=
        related.advance_of_step sourceStep
      exact ⟨1, targetAfter, targetPath,
        next.withSchemaExtensionPreservedStep sourceStep noShape schemaAgrees
          witnessExtension,
        by omega⟩
  | externalBind related =>
      have noShape : ¬ ∃ nextSchema,
          ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
        simp [ConstructorSchema.DirectLetShapeAt,
          related.core.bindFocus.sourceControlEq]
      obtain ⟨targetAfter, targetPath, next⟩ :=
        related.advance_of_step sourceStep
      exact ⟨1, targetAfter, targetPath,
        next.withSchemaPreservedStep sourceStep noShape schemaAgrees,
        by omega⟩
  | returned related =>
      have noShape : ¬ ∃ nextSchema,
          ConstructorSchema.DirectLetShapeAt source schema nextSchema := by
        simp [ConstructorSchema.DirectLetShapeAt,
          related.yielded.sourceControlEq]
      obtain ⟨targetCount, targetAfter, targetPath, targetPositive, next⟩ :=
        related.advance_of_step sourceStep
      exact ⟨targetCount, targetAfter, targetPath,
        next.withSchemaPreservedStep sourceStep noShape schemaAgrees, by omega⟩

/-- Compatibility projection of transition-retaining global advancement. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcomeAt.advance_of_schemaSourceReady
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {schema : ConstructorSchema}
    {witness : Fir.Wasm.Concrete.RefinementWitness}
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {target : StructuredWasmState Host}
    (sourceReady : ConcreteStructuredSchemaSourceReadyAt schema program
      sourceModule targetModule hosts externals source)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (schemaAgrees : schema.WitnessAgrees witness)
    (related : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals witness source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨targetCount, targetAfter, targetPath, next, rank⟩ :=
    related.advanceSchemaStep_of_schemaSourceReady sourceReady
      finiteRuntimeSafety addressSpaceSafety schemaAgrees sourceStep
  exact ⟨targetCount, targetAfter, targetPath, next.toSchemaGlobal, rank⟩

/-- One source step preserves the validated compiler state and its
schema-indexed hereditary source invariant in lockstep. -/
theorem ConcreteStructuredSchemaValidatedInvariantGlobalOutcome.advance
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop}
    (laws : ConcreteStructuredSchemaSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredSchemaValidatedInvariantGlobalOutcome program
      sourceModule targetModule hosts externals Invariant source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredSchemaValidatedInvariantGlobalOutcome program
          sourceModule targetModule hosts externals Invariant sourceAfter
          targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨schema, witness, sourceInvariant, schemaAgrees, validated⟩ := related
  obtain ⟨targetCount, targetAfter, targetPath, next, rank⟩ :=
    validated.advanceSchemaStep_of_schemaSourceReady
      (laws.ready sourceInvariant) finiteRuntimeSafety addressSpaceSafety
      schemaAgrees sourceStep
  exact ⟨targetCount, targetAfter, targetPath,
    next.withInvariant laws sourceInvariant, rank⟩

/-- The schema-indexed hereditary invariant closes the validated compiler
relation into the generic ranked finite-prefix simulation. -/
def ConcreteStructuredSchemaSourceInvariantLaws.toGeneratedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop}
    (laws : ConcreteStructuredSchemaSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule
      hosts.env where
  relation := ConcreteStructuredSchemaValidatedInvariantGlobalOutcome program
    sourceModule targetModule hosts externals Invariant
  rank := compilerStructuredControlRank
  observes := by
    intro sourceState targetState related
    obtain ⟨schema, witness, sourceInvariant, schemaAgrees, validated⟩ := related
    exact validated.toValidatedGlobal.toSupportedGlobal.observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related sourceStep
    exact related.advance laws finiteRuntimeSafety addressSpaceSafety sourceStep

/-- Initial schema agreement, validated compiler state, and the corresponding
source invariant imply finite-prefix correctness. -/
theorem ConcreteStructuredSchemaSourceInvariantLaws.toFiniteTraceCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop}
    (laws : ConcreteStructuredSchemaSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    {sourceInitial : Fir.LeanIR.Impure.MachineState}
    {targetInitial : StructuredWasmState Host}
    {schema : ConstructorSchema}
    {witness : Fir.Wasm.Concrete.RefinementWitness}
    (sourceInvariant : Invariant sourceInitial schema)
    (schemaAgrees : schema.WitnessAgrees witness)
    (validated : ConcreteStructuredValidatedCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals witness sourceInitial
      targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  ⟨laws.toGeneratedTraceSimulation finiteRuntimeSafety addressSpaceSafety,
    ⟨schema, witness, sourceInvariant, schemaAgrees, validated⟩⟩

/-- Current source readiness and finite runtime safety preserve the recursively
validated global relation for one source step.

This is the state-local core of compiler admission.  The active-code
branch reads residual validation from `ConcreteStructuredValidatedCodeOutcome`
itself, combines it with source readiness for the current node, and
uses the independent finite-address-space premise only for the selected
allocation cost.  Administrative call, cache, bind, and return states already
carry their suspended validation and therefore require no fresh compiler
certificate. -/
theorem ConcreteStructuredValidatedCodeGlobalOutcome.advance_of_sourceReady
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {target : StructuredWasmState Host}
    (sourceReady : ConcreteStructuredSourceReadyAt program sourceModule
      targetModule hosts externals source)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (related : ConcreteStructuredValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  cases related with
  | code activeResult related =>
      have sourceSafe := sourceReady.code _ activeResult
        related sourceStep
      have finiteSafe := finiteRuntimeSafety.code _ activeResult related
        sourceStep
      obtain ⟨requiredBytes, admitted⟩ :=
        related.core.admit_of_source_safe_step sourceSafe finiteSafe sourceStep
      have budget := addressSpaceSafety.code related.core.core sourceStep
        admitted
      exact related.advance_of_admission activeResult admitted budget sourceStep
  | directReady related =>
      obtain ⟨targetAfter, targetPath, next⟩ :=
        related.advance_enter_of_step sourceStep
      exact ⟨1, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
  | saturatedReady related =>
      obtain ⟨targetCount, targetAfter, targetPath, targetPositive, next⟩ :=
        related.advance_enter_of_step sourceStep
      exact ⟨targetCount, targetAfter, targetPath, next.toValidatedGlobal,
        by omega⟩
  | lazyReady related =>
      cases related.path with
      | hit sourceValue semanticFound =>
          obtain ⟨physical, targetAfter, targetPath, next⟩ :=
            related.advance_hit_of_step semanticFound sourceStep
          exact ⟨4, targetAfter, targetPath,
            (ConcreteStructuredValidatedCodeGlobalOutcomeAt.externalBind next)
              |>.toValidatedGlobal,
            by omega⟩
      | miss calleeCode internal resultClassified notObject notTObject
          semanticEmpty =>
          obtain ⟨targetAfter, targetPath, next⟩ :=
            related.advance_miss_of_step internal resultClassified notObject
              notTObject semanticEmpty sourceStep
          exact ⟨3, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
  | externalReady related =>
      obtain ⟨_nextWitness, targetAfter, targetPath, _witnessExtension, next⟩ :=
        related.advance_of_step sourceStep
      exact ⟨1, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
  | externalBind related =>
      obtain ⟨targetAfter, targetPath, next⟩ :=
        related.advance_of_step sourceStep
      exact ⟨1, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
  | returned related =>
      obtain ⟨targetCount, targetAfter, targetPath, targetPositive, next⟩ :=
        related.advance_of_step sourceStep
      exact ⟨targetCount, targetAfter, targetPath, next.toValidatedGlobal,
        by omega⟩

/-- Compatibility wrapper for the former module-global source-safety law. -/
theorem ConcreteStructuredCompilerAdmissionLaws.advanceValidatedGlobal
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (laws : ConcreteStructuredCompilerAdmissionLaws program sourceModule
      targetModule hosts externals)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) :=
  related.advance_of_sourceReady (laws.sourceSafety.ready source)
    finiteRuntimeSafety addressSpaceSafety sourceStep

/-- The validated compiler relation paired with a source-only semantic
invariant.  Neither component stores a future source transition or a target
execution path. -/
structure ConcreteStructuredValidatedInvariantGlobalOutcome
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl)
    (Invariant : Fir.LeanIR.Impure.MachineState → Prop)
    (source : Fir.LeanIR.Impure.MachineState)
    (target : StructuredWasmState Host) : Prop where
  validated : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
    targetModule hosts externals source target
  sourceInvariant : Invariant source

/-- One source step preserves both compiler validation and the source semantic
invariant. -/
theorem ConcreteStructuredValidatedInvariantGlobalOutcome.advance
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → Prop}
    (laws : ConcreteStructuredSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    {source sourceAfter : Fir.LeanIR.Impure.MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedInvariantGlobalOutcome program
      sourceModule targetModule hosts externals Invariant source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ targetCount targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        ConcreteStructuredValidatedInvariantGlobalOutcome program sourceModule
          targetModule hosts externals Invariant sourceAfter targetAfter ∧
        (targetCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨targetCount, targetAfter, targetPath, validatedAfter, rank⟩ :=
    related.validated.advance_of_sourceReady
      (laws.ready related.sourceInvariant) finiteRuntimeSafety
      addressSpaceSafety sourceStep
  exact ⟨targetCount, targetAfter, targetPath,
    ⟨validatedAfter, laws.preserved related.sourceInvariant sourceStep⟩, rank⟩

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
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      sourceCode targetStore targetLocals targetCode witness source target)
    (sourceStep :
      Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter) :
    ∃ requiredBytes,
      ConcreteStructuredCodeStepAdmission context sourceModule externals
          functionResult facts sourceRuntime sourceEnv requiredBytes sourceCode ∧
        requiredBytes ≤ remainingBytes := by
  obtain ⟨requiredBytes, admitted⟩ :=
    coverage.admission.code spec activeResult related sourceStep
  exact ⟨requiredBytes, admitted,
    coverage.addressSpaceSafety.code related.core.core sourceStep admitted⟩

/-- Source-local closure of the recursively validated compiler relation.

The classifier is applied only after the current source transition is known.
Its input retains the exact residual validator state transported from the
production root; this is the static evidence from which compiler admission is
derived. It stores no successor admission, future execution, target path, or
termination evidence. -/
structure ConcreteStructuredCurrentStepClassifier
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (externals : Fir.LeanIR.Impure.ExternalImpl) : Prop where
  advance :
    ∀ {source sourceAfter : Fir.LeanIR.Impure.MachineState}
      {target : StructuredWasmState Host},
      ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
          targetModule hosts externals source target →
        Fir.LeanIR.Impure.executeStep externals source = .next sourceAfter →
        ∃ targetCount targetAfter,
          FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
              targetCount target targetAfter ∧
            ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
              targetModule hosts externals sourceAfter targetAfter ∧
            (targetCount = 0 →
              compilerStructuredControlRank sourceAfter <
                compilerStructuredControlRank source)

/-- Compiler admission plus independent address-space safety discharge the
only non-structural branch of the global classifier.

Ordinary code asks the compiler law for its current admission and the
independent resource law for its budget. The six staged
call/cache/bind/return shapes already carry their transported validation and
advance directly. No future source transition or target execution is
inspected. -/
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
  advance := by
    intro source sourceAfter target related sourceStep
    cases related with
    | code activeResult related =>
        obtain ⟨requiredBytes, admitted⟩ :=
          admission.code _ activeResult related sourceStep
        have budget := addressSpaceSafety.code related.core.core sourceStep
          admitted
        exact related.advance_of_admission activeResult admitted budget sourceStep
    | directReady related =>
        obtain ⟨targetAfter, targetPath, next⟩ :=
          related.advance_enter_of_step sourceStep
        exact ⟨1, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
    | saturatedReady related =>
        obtain ⟨targetCount, targetAfter, targetPath, targetPositive, next⟩ :=
          related.advance_enter_of_step sourceStep
        exact ⟨targetCount, targetAfter, targetPath, next.toValidatedGlobal,
          by omega⟩
    | lazyReady related =>
        cases related.path with
        | hit sourceValue semanticFound =>
            obtain ⟨physical, targetAfter, targetPath, next⟩ :=
              related.advance_hit_of_step semanticFound sourceStep
            exact ⟨4, targetAfter, targetPath,
              (ConcreteStructuredValidatedCodeGlobalOutcomeAt.externalBind next)
                |>.toValidatedGlobal,
              by omega⟩
        | miss calleeCode internal resultClassified notObject notTObject
            semanticEmpty =>
            obtain ⟨targetAfter, targetPath, next⟩ :=
              related.advance_miss_of_step internal resultClassified notObject
                notTObject semanticEmpty sourceStep
            exact ⟨3, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
    | externalReady related =>
        obtain ⟨_nextWitness, targetAfter, targetPath, _witnessExtension,
            next⟩ := related.advance_of_step sourceStep
        exact ⟨1, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
    | externalBind related =>
        obtain ⟨targetAfter, targetPath, next⟩ :=
          related.advance_of_step sourceStep
        exact ⟨1, targetAfter, targetPath, next.toValidatedGlobal, by omega⟩
    | returned related =>
        obtain ⟨targetCount, targetAfter, targetPath, targetPositive, next⟩ :=
          related.advance_of_step sourceStep
        exact ⟨targetCount, targetAfter, targetPath, next.toValidatedGlobal,
          by omega⟩

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

/-- A source-local current-step classifier closes the recursively validated
relation into the generic ranked finite-prefix simulation object. This is the
central PA2 bridge: production validation is transported by the relation and
consulted only at the current transition. -/
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
  relation := ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
    targetModule hosts externals
  rank := compilerStructuredControlRank
  observes := by
    intro sourceState targetState related
    exact related.toSupportedGlobal.observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related sourceStep
    exact classifier.advance related sourceStep

/-- Intermediate certificate-free finite-trace packaging theorem.

The two remaining compiler obligations are now explicit and orthogonal: prove
the universal current-step classifier, and construct the validated relation at
the compiler-produced root entry. Neither obligation exposes a target
execution path or a simulation relation to the eventual public caller. -/
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
    (initial : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals sourceInitial targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  ⟨classifier.toGeneratedTraceSimulation, initial⟩

/-- A preserved source semantic invariant and the validated compiler relation
construct the ranked finite-prefix simulation directly. -/
def ConcreteStructuredSourceInvariantLaws.toGeneratedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → Prop}
    (laws : ConcreteStructuredSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule
      hosts.env where
  relation := ConcreteStructuredValidatedInvariantGlobalOutcome program
    sourceModule targetModule hosts externals Invariant
  rank := compilerStructuredControlRank
  observes := by
    intro sourceState targetState related
    exact related.validated.toSupportedGlobal.observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related sourceStep
    exact related.advance laws finiteRuntimeSafety addressSpaceSafety sourceStep

/-- Initial validated compiler state plus an initial source invariant imply
finite-prefix correctness. -/
theorem ConcreteStructuredSourceInvariantLaws.toFiniteTraceCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {Invariant : Fir.LeanIR.Impure.MachineState → Prop}
    (laws : ConcreteStructuredSourceInvariantLaws program sourceModule
      targetModule hosts externals Invariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    {sourceInitial : Fir.LeanIR.Impure.MachineState}
    {targetInitial : StructuredWasmState Host}
    (validated : ConcreteStructuredValidatedCodeGlobalOutcome program
      sourceModule targetModule hosts externals sourceInitial targetInitial)
    (sourceInvariant : Invariant sourceInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  ⟨laws.toGeneratedTraceSimulation finiteRuntimeSafety addressSpaceSafety,
    ⟨validated, sourceInvariant⟩⟩

/-- The provenance-preserving compiler simulation.

Its relation contains the residual validator state at the active node and in
every suspended frame.  Validation is therefore established once at the
generated export root and transported by the one-step proof; it is not
reconstructed by a universal law over arbitrary admission-free code cores. -/
def ConcreteStructuredCompilerAdmissionLaws.toValidatedGeneratedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (laws : ConcreteStructuredCompilerAdmissionLaws program sourceModule
      targetModule hosts externals)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule
      hosts.env where
  relation := ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
    targetModule hosts externals
  rank := compilerStructuredControlRank
  observes := by
    intro sourceState targetState related
    exact related.toSupportedGlobal.observes
  advance := by
    intro sourceBefore sourceAfter targetBefore related sourceStep
    exact laws.advanceValidatedGlobal finiteRuntimeSafety addressSpaceSafety
      related sourceStep

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
with the compiler-produced validated root, imply finite-prefix correctness. -/
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
    (initial : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals sourceInitial targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  (admission.toCurrentStepClassifier addressSpaceSafety).toFiniteTraceCorrect
    initial

/-- Production source laws plus the independent finite-memory law preserve a
root-validated compiler relation and imply finite-prefix correctness.

The initial relation contains the production validator state.  The simulation
then transports that state inductively, so no universal residual-validation
premise is needed at later source nodes. -/
theorem ConcreteStructuredCompilerAdmissionLaws.toFiniteTraceCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (laws : ConcreteStructuredCompilerAdmissionLaws program sourceModule
      targetModule hosts externals)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    {sourceInitial : Fir.LeanIR.Impure.MachineState}
    {targetInitial : StructuredWasmState Host}
    (initial : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
      targetModule hosts externals sourceInitial targetInitial) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      sourceInitial targetInitial :=
  ⟨laws.toValidatedGeneratedTraceSimulation finiteRuntimeSafety
      addressSpaceSafety,
    initial⟩

/-- Combined current-node coverage and the validated compiler root imply
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
    (initial : ConcreteStructuredValidatedCodeGlobalOutcome program sourceModule
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
initial relation. `ConcreteSupportedExport.validatedCodeGlobalRoot` derives it
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
    (spec.validatedCodeGlobalRoot contextCaches invariant)

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
    (spec.validatedCodeGlobalRoot contextCaches invariant)

/-- Preferred export-facing finite-prefix theorem.

The source semantic invariant is established once at the source entry and
preserved by source execution.  Compiler validation is established once at
the generated export entry and preserved by the structured simulation.
Finite header/capture safety and allocation headroom remain explicit runtime
premises.  No premise contains a target execution or future source step. -/
theorem ConcreteSupportedExport.finiteTraceCorrect_of_sourceInvariant
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
    {SourceInvariant : Fir.LeanIR.Impure.MachineState → Prop}
    (sourceLaws : ConcreteStructuredSourceInvariantLaws program sourceModule
      targetModule hosts externals SourceInvariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {initial : Wasm.Store Host}
    {initialWitness : Fir.Wasm.Concrete.RefinementWitness}
    {parameters : List Wasm.Value}
    (runtimeInvariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness)
    (sourceInitialInvariant : SourceInvariant
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  sourceLaws.toFiniteTraceCorrect finiteRuntimeSafety addressSpaceSafety
    (spec.validatedCodeGlobalRoot contextCaches runtimeInvariant)
    sourceInitialInvariant

/-- Production-facing schema-indexed finite-prefix correctness.

The compiler constructs the validated target relation at the canonical export
entry and retains its exact initial witness.  The client supplies one source-
only constructor schema agreeing with that witness, the corresponding
hereditary final-LCNF invariant, and the two independent finite-resource laws.
No premise quantifies over unrelated schemas or contains a target execution,
future source step, termination proof, or translation certificate. -/
theorem ConcreteSupportedExport.finiteTraceCorrect_of_schemaSourceInvariant
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
    {SourceInvariant :
      Fir.LeanIR.Impure.MachineState → ConstructorSchema → Prop}
    (sourceLaws : ConcreteStructuredSchemaSourceInvariantLaws program
      sourceModule targetModule hosts externals SourceInvariant)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety
      program sourceModule targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {initial : Wasm.Store Host}
    {initialWitness : Fir.Wasm.Concrete.RefinementWitness}
    {parameters : List Wasm.Value}
    {initialSchema : ConstructorSchema}
    (runtimeInvariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness)
    (schemaAgrees : initialSchema.WitnessAgrees initialWitness)
    (sourceInitialInvariant : SourceInvariant
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      initialSchema) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  sourceLaws.toFiniteTraceCorrect finiteRuntimeSafety addressSpaceSafety
    sourceInitialInvariant schemaAgrees
    (spec.validatedCodeGlobalRootAt contextCaches runtimeInvariant)

/-- Export-facing form of the provenance-preserving production proof route.
The compiler establishes validation once at the real export root, while the
simulation carries it through every active and suspended continuation. -/
theorem ConcreteSupportedExport.finiteTraceCorrect_of_admissionLaws
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
    (laws : ConcreteStructuredCompilerAdmissionLaws program sourceModule
      targetModule hosts externals)
    (finiteRuntimeSafety : ConcreteStructuredCurrentStepFiniteRuntimeSafety
      program sourceModule targetModule hosts externals)
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
  laws.toFiniteTraceCorrect finiteRuntimeSafety addressSpaceSafety
    (spec.validatedCodeGlobalRoot contextCaches invariant)

end FirTalos.Concrete
