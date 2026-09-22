import FirTalos.ConcreteRootedDispatch

/-!
# Rooted finite-prefix composition

The accepted seven-focus step theorem is an instance of the existing ranked
trace simulation. Its relation hides the current heap witness, but not the
original export result kind. The witness is unpacked again at every finite
endpoint; it is never assumed to equal the entry witness.

The real supported export constructs its initial rooted/precise relation.
Clients provide the existing entry runtime contract, compiler admission and
separate address-space law, not a new invariant, root equality or target path.
This is conditional finite-prefix preservation, not terminal adequacy, schema
preservation, a proof of universal admission, or a theorem about linked bytes.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Reuse the generic ranked simulation while retaining the selected root ABI.
Only the heap witness is hidden: allocation and external calls may extend it.
The accepted one-step theorem supplies every path and the strict rank condition. -/
def ConcreteStructuredCompilerCurrentStepAdmission.toRootedTraceSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {externals : ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (rootResult : AbiKind) :
    ConcreteGeneratedTraceSimulation externals targetModule.wasmModule hosts.env where
  relation := fun source target =>
    ∃ witness, ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals rootResult witness source target
  rank := compilerStructuredControlRank
  observes := by
    rintro source target ⟨witness, related⟩
    exact related.toValidatedGlobalAt.toValidatedGlobal.toSupportedGlobal.observes
  advance := by
    rintro source sourceAfter target ⟨witness, related⟩ step
    obtain ⟨count, targetAfter, nextWitness, path, next, decreases⟩ :=
      related.advance_of_step admission addressSpaceSafety step
    exact ⟨count, targetAfter, path, ⟨nextWitness, next⟩, decreases⟩

section Prefix

variable
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {externals : ExternalImpl}
    {rootResult : AbiKind} {witness : RefinementWitness}
    {sourceBefore sourceAfter : MachineState}
    {targetBefore : StructuredWasmState Host} {count : Nat}

/-- A finite source execution retains the same root and precise returned focus
at its actual final witness. No termination or per-program invariant is needed.
Path concatenation and prefix observations come from the common framework. -/
theorem ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt.execSteps
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals rootResult witness
      sourceBefore targetBefore)
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (steps : ExecSteps externals count sourceBefore sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetCount targetBefore targetAfter ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
      ConcretePrefixObservationRel (sourcePrefixObservation sourceAfter)
        (concretePrefixObservation targetAfter.store) := by
  obtain ⟨targetCount, targetAfter, path, ⟨nextWitness, next⟩, observations⟩ :=
    (admission.toRootedTraceSimulation addressSpaceSafety rootResult).execSteps
      ⟨witness, related⟩ steps
  exact ⟨targetCount, targetAfter, nextWitness, path, next, observations⟩

end Prefix

section Export

variable
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl} {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env} {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness} {parameters : List Wasm.Value}

/-- Production export entry supplies its own root identity and precise active
kind. This is the existing validated entry at the same exact heap witness,
not an additional caller-supplied provenance condition. -/
theorem ConcreteSupportedExport.rootedPreciseCodeGlobalRoot
    (contextCaches : context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness) :
    ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
      targetModule hosts externals spec.sourceResultKind initialWitness
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial parameters) :=
  .code rfl (spec.validatedCodeRoot contextCaches invariant)
    (spec.validatedCodeRoot_rootResult contextCaches invariant)

/-- Every finite execution from an actual supported export has a target prefix
whose named outcome still knows the export's result ABI. Initial root metadata
is derived internally. Admission and finite address space remain independent
explicit laws; this does not discharge either one. -/
theorem ConcreteSupportedExport.rootedExecSteps_of_currentStepAdmission
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (contextCaches : context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    {count : Nat} {sourceAfter : MachineState}
    (steps : ExecSteps externals count
      (sourceCodeState context sourceRuntime sourceEnv sourceCode) sourceAfter) :
    ∃ targetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetCount (concreteStructuredFunctionEntry spec.targetFunction initial
          parameters) targetAfter ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals spec.sourceResultKind nextWitness
        sourceAfter targetAfter ∧
      ConcretePrefixObservationRel (sourcePrefixObservation sourceAfter)
        (concretePrefixObservation targetAfter.store) :=
  (spec.rootedPreciseCodeGlobalRoot contextCaches invariant).execSteps
    admission addressSpaceSafety steps

end Export

section CompositionRegressions

variable
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {externals : ExternalImpl}
    {rootResult : AbiKind} {witness : RefinementWitness}
    {sourceBefore sourceMiddle sourceAfter : MachineState}
    {targetBefore : StructuredWasmState Host} {firstCount secondCount : Nat}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)

/-- Regression: packaging keeps the original anti-stuttering rank exactly. -/
example :
    (admission.toRootedTraceSimulation addressSpaceSafety rootResult).rank =
      compilerStructuredControlRank := rfl

/-- Regression: the current witness belongs to the related state, not a fixed
initial witness. Replacing it requires real evidence; it is not a property of
the finite-prefix package. -/
example
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals rootResult witness
      sourceBefore targetBefore) :
    (admission.toRootedTraceSimulation addressSpaceSafety rootResult).relation
      sourceBefore targetBefore := by
  fail_if_success
    have : ∀ arbitraryWitness,
        ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
          targetModule hosts externals rootResult arbitraryWitness
          sourceBefore targetBefore := by
      intro arbitraryWitness
      exact related
  exact ⟨witness, related⟩

/-- Regression: two real prefix applications compose at the first producer's
actual witness and preserve one root ABI, with the exact sum of target counts.
The second prefix has no new initial-entry or client-invariant obligation. -/
example
    (related : ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program
      sourceModule targetModule hosts externals rootResult witness
      sourceBefore targetBefore)
    (first : ExecSteps externals firstCount sourceBefore sourceMiddle)
    (second : ExecSteps externals secondCount sourceMiddle sourceAfter) :
    ∃ firstTargetCount secondTargetCount targetAfter nextWitness,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        (firstTargetCount + secondTargetCount) targetBefore targetAfter ∧
      ConcreteStructuredRootedPreciseCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals rootResult nextWitness sourceAfter targetAfter ∧
      ConcreteStructuredValidatedCodeGlobalOutcomeAt program sourceModule
        targetModule hosts externals nextWitness sourceAfter targetAfter ∧
      ConcretePrefixObservationRel (sourcePrefixObservation sourceAfter)
        (concretePrefixObservation targetAfter.store) := by
  obtain ⟨firstTargetCount, middle, middleWitness, firstPath, middleRelated, _⟩ :=
    related.execSteps admission addressSpaceSafety first
  obtain ⟨secondTargetCount, after, nextWitness, secondPath, next, observations⟩ :=
    middleRelated.execSteps admission addressSpaceSafety second
  exact ⟨firstTargetCount, secondTargetCount, after, nextWitness,
    firstPath.trans secondPath, next, next.toValidatedGlobalAt, observations⟩

end CompositionRegressions

end FirTalos.Concrete
