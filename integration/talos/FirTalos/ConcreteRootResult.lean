import FirTalos.ConcreteStructuredValidation

/-!
# Root result identity from the checked caller spine

The existing validated stack agreement already records the selected result ABI
of each suspended caller. Its oldest caller, or the active function when the
spine is empty, identifies the root result. Calls may change the active result
ABI without changing that root. Case labels do not change the caller spine.

This is an internal, root-indexed refinement of the existing stack agreement,
not a new source invariant or an application-supplied provenance map. The real
export entry constructs it below. Preserving this index through the global
simulation is deliberately a separate step; the unindexed global relation
cannot recover root identity after existentially hiding the caller spine.
-/

namespace FirTalos.Concrete

open Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Recover the oldest caller's selected result ABI. The spine is the existing
non-proof index of `ConcreteStructuredValidatedStackAgreement`, not new runtime
state. Its optional kinds describe immediate consumers, not the root ABI. -/
def concreteStructuredRootResultKind (active : AbiKind) :
    List (AbiKind × Option AbiKind) → AbiKind
  | [] => active
  | (caller, _) :: spine => concreteStructuredRootResultKind caller spine

@[simp] theorem concreteStructuredRootResultKind_nil (active : AbiKind) :
    concreteStructuredRootResultKind active [] = active := rfl

/-- One law covers direct calls, saturated closure calls, and lazy initializer
calls: all three checked constructors push the same caller ABI pair. Read in
reverse, it is the corresponding return/pop law. Callee and caller result ABIs
need not be equal. -/
@[simp] theorem concreteStructuredRootResultKind_push
    (callee caller : AbiKind) (expected : Option AbiKind)
    (spine : List (AbiKind × Option AbiKind)) :
    concreteStructuredRootResultKind callee ((caller, expected) :: spine) =
      concreteStructuredRootResultKind caller spine := rfl

section Stack

variable
    {program : Fir.LeanIR.ImpureProgram} {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {externals : ExternalImpl} {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host} {entryWitness : RefinementWitness}
    {functionResult : AbiKind} {expectedResult : Option AbiKind}
    {sourceFrames : List Frame} {targetFrames : List StructuredWasmFrame}
    {supported : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult sourceFrames targetFrames}
    {resources : ConcreteStructuredSuspendedResourceStack externals program
      entryRuntime entryStore entryWitness functionResult expectedResult
      sourceFrames targetFrames}
    {agrees : supported.Agrees resources}
    {validation : ConcreteStructuredSuspendedValidation program functionResult
      expectedResult sourceFrames}

/-- Source termination empties the ABI spine even if target-only case labels
still need to unwind. The proof uses checked stack constructors, not a guessed
correspondence between source-frame count and target-frame count. -/
theorem ConcreteStructuredValidatedStackAgreement.spine_eq_nil_of_empty
    {spine : List (AbiKind × Option AbiKind)}
    (aligned : ConcreteStructuredValidatedStackAgreement spine agrees validation)
    (empty : sourceFrames = []) : spine = [] := by
  induction aligned with
  | nil => rfl
  | case _ ih => exact ih empty
  | direct => cases empty
  | saturated => cases empty
  | lazy => cases empty

/-- Retain root identity when hiding the checked caller spine. The root is an
explicit non-proof index; it is not extracted from a proof by computation.
Validation and runtime facts are reused unchanged. -/
def ConcreteStructuredValidationAgreesAtRoot (rootResult : AbiKind)
    (agrees : supported.Agrees resources)
    (validation : ConcreteStructuredSuspendedValidation program functionResult
      expectedResult sourceFrames) : Prop :=
  ∃ spine, ConcreteStructuredValidatedStackAgreement spine agrees validation ∧
    concreteStructuredRootResultKind functionResult spine = rootResult

theorem ConcreteStructuredValidationAgreesAtRoot.toValidationAgrees
    {rootResult : AbiKind}
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult agrees validation) :
    ConcreteStructuredValidationAgrees agrees validation := by
  obtain ⟨spine, aligned, _⟩ := rooted
  exact ⟨spine, aligned⟩

/-- At an unframed root, the ordinary checked relation establishes root identity
itself. This is used at the compiler-produced export entry below. -/
theorem ConcreteStructuredValidationAgrees.atRoot_of_empty
    (aligned : ConcreteStructuredValidationAgrees agrees validation)
    (empty : sourceFrames = []) :
    ConcreteStructuredValidationAgreesAtRoot functionResult agrees validation := by
  obtain ⟨spine, aligned⟩ := aligned
  exact ⟨spine, aligned, by rw [aligned.spine_eq_nil_of_empty empty]; rfl⟩

/-- An empty source continuation identifies the active selected result ABI
with the preserved root ABI. No compatibility-to-refinement conversion is
used: compatibility with `none` would be insufficient. -/
theorem ConcreteStructuredValidationAgreesAtRoot.functionResult_eq_of_empty
    {rootResult : AbiKind}
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult agrees validation)
    (empty : sourceFrames = []) : functionResult = rootResult := by
  obtain ⟨spine, aligned, rootEq⟩ := rooted
  simpa [aligned.spine_eq_nil_of_empty empty] using rootEq

/-- Pushing target-only case labels preserves the exact root index and the
existing ABI spine. -/
theorem ConcreteStructuredValidationAgreesAtRoot.case
    {rootResult : AbiKind} {belowStack : List Wasm.Value}
    {targetRest : Wasm.Program} {testCount : Nat}
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult agrees validation) :
    ConcreteStructuredValidationAgreesAtRoot rootResult
      (.case (belowStack := belowStack) (targetRest := targetRest)
        (testCount := testCount) supported resources agrees) validation := by
  obtain ⟨spine, aligned, rootEq⟩ := rooted
  exact ⟨spine, .case aligned, rootEq⟩

/-- Ordinary frame reindexing retains the same root, rather than obtaining a
fresh existential spine from a different agreement proof. -/
theorem ConcreteStructuredValidationAgreesAtRoot.reindex
    {rootResult : AbiKind}
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult agrees validation)
    {nextSourceFrames : List Frame} {nextTargetFrames : List StructuredWasmFrame}
    (sourceFramesEq : nextSourceFrames = sourceFrames)
    (targetFramesEq : nextTargetFrames = targetFrames)
    {nextSupported : ConcreteStructuredSupportedFrameStack program sourceModule
      targetModule hosts functionResult expectedResult nextSourceFrames nextTargetFrames}
    {nextResources : ConcreteStructuredSuspendedResourceStack externals program
      entryRuntime entryStore entryWitness functionResult expectedResult
      nextSourceFrames nextTargetFrames}
    (nextAgrees : nextSupported.Agrees nextResources)
    (nextValidation : ConcreteStructuredSuspendedValidation program functionResult
      expectedResult nextSourceFrames) :
    ConcreteStructuredValidationAgreesAtRoot rootResult nextAgrees nextValidation := by
  subst nextSourceFrames
  subst nextTargetFrames
  exact rooted

end Stack

/-- The actual supported export constructor establishes the root index without
an additional client premise. Entry runtime compatibility is exactly the
existing `validatedCodeRoot` contract. -/
theorem ConcreteSupportedExport.validatedCodeRoot_rootResult
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    (contextCaches : context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {externals : ExternalImpl} {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env} {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness} {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness) :
    let related := spec.validatedCodeRoot contextCaches invariant
    ConcreteStructuredValidationAgreesAtRoot spec.sourceResultKind
      related.agrees related.frames.validation := by
  exact (spec.validatedCodeRoot contextCaches invariant).validationAgrees.atRoot_of_empty rfl

/-- Precise local return evidence plus the preserved checked root index gives
an exact root-ABI yield. This is an internal terminal consumer; the global
dispatcher must still preserve the root index and producer precision. -/
theorem ConcreteStructuredValidatedReturnedOutcome.yieldAtRoot_of_empty
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl} {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState} {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind} {facts : ReuseCapacityFacts}
    {remainingBytes : Nat} {sourceEnv : Env} {sourceValue : Value}
    {targetLocals : Wasm.Locals} {physical : Wasm.Value} {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedReturnedOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv sourceValue targetStore targetLocals
      witness functionResult physical source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (empty : source.frames = []) :
    ConcreteStructuredYieldFocus context sourceFunction sourceRuntime sourceEnv sourceValue
      targetStore targetLocals witness rootResult physical source target := by
  have resultEq := rooted.functionResult_eq_of_empty empty
  simpa only [resultEq] using related.yielded

/-- Heterogeneous nested calls retain the original result, not the deepest
callee's kind or the immediate consumer's kind. -/
example : concreteStructuredRootResultKind .uint8
    [(.object, some .tobject), (.uint64, none)] = .uint64 := rfl

/-- Root precision is meaningful: a different selected result is rejected even
though some physical lanes are shared. -/
example : concreteStructuredRootResultKind .uint8
    [(.object, some .tobject), (.uint64, none)] ≠ .uint8 := by
  intro impossible
  cases impossible

end FirTalos.Concrete
