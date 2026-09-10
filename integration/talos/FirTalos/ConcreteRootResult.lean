import FirTalos.ConcreteStructuredValidation

/-!
# Root result identity from the checked caller spine

The existing validated stack agreement already records the selected result ABI
of each suspended caller. Its oldest caller, or the active function when the
spine is empty, identifies the root result. Calls may change the active result
ABI without changing that root. Case labels do not change the caller spine.

This is an internal, root-indexed refinement of the existing stack agreement,
not a new source invariant or an application-supplied provenance map. The real
export entry constructs it below. Precise returns, direct lets and erased
default-only and tested object/UInt8 cases retain it. The validated case
dispatcher derives the applicable family from production validation and
composes those rooted producers without a caller-supplied case classifier.
Persistent and ordinary reference-count operations retain the same root by
reindexing their existing zero-step and two-step successors, respectively.
Validation-derived ordinary increment, decrement and explicit delete derive
their effect facts internally; increment retains its exact refcount headroom
premise. Delete includes erased physical zero through the existing rule.
Constructor-tag mutation likewise derives compiler/heap-shape facts and
retains the root through its existing exact two-step effect rule.
USize and packed-scalar field mutations retain it through their three-step
rules; the packed-scalar rule keeps its existing descriptor-layout premise.
Preservation through the other global transitions is still separate; the
unindexed global relation cannot recover root identity after existentially
hiding the caller spine.
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

/-- Preserve the compiler-owned root index through one successful return.
The represented kind stays exactly `functionResult`; the dependent existential
retains the returned stack proof needed to state its root agreement. This adds
no execution assumption to the precise return rule: `rooted` is internal
metadata constructed at export entry and transported by the simulation.
The target path, witness, and unchanged-frame equations are reused verbatim. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_returnPreciseAtRoot_of_step
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
    {remainingBytes : Nat} {sourceEnv : Env} {result : Lean.FVarId}
    {targetLocals : Wasm.Locals} {targetCode : Wasm.Program}
    {source sourceAfter : MachineState} {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.return result)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv 0 (.return result))
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter sourceValue physical,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target targetAfter ∧
      ∃ returned : ConcreteStructuredValidatedReturnedOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult callerExpectedResult
          facts remainingBytes sourceRuntime sourceEnv sourceValue targetStore targetLocals
          witness functionResult physical sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          returned.agrees returned.frames.validation ∧
        sourceAfter.frames = source.frames ∧ targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, sourceValue, physical, path, returned, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_returnPrecise_of_step activeResult admitted sourceStep
  exact ⟨targetAfter, sourceValue, physical, path, returned,
    rooted.reindex sourceFramesEq targetFramesEq returned.agrees returned.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- Exact-root regression and terminal consumer for the return transition.
An empty source continuation derives an exact root-ABI yield from the producer;
no `functionResult = rootResult` or caller-supplied result-precision premise is
needed. This composition would fail if the producer existentially hid either
the represented kind or the root. Target-only labels may remain for the
existing terminal bridge to unwind. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_returnYieldAtRoot_of_step
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
    {remainingBytes : Nat} {sourceEnv : Env} {result : Lean.FVarId}
    {targetLocals : Wasm.Locals} {targetCode : Wasm.Program}
    {source sourceAfter : MachineState} {target : StructuredWasmState Host}
    (activeResult : spec.sourceResultKind = functionResult)
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult callerExpectedResult
      facts remainingBytes sourceRuntime sourceEnv (.return result)
      targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (admitted : ConcreteStructuredCodeStepAdmission context sourceModule
      externals functionResult facts sourceRuntime sourceEnv 0 (.return result))
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter sourceValue physical,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target targetAfter ∧
      ConcreteStructuredYieldFocus context sourceFunction sourceRuntime sourceEnv sourceValue
        targetStore targetLocals witness rootResult physical sourceAfter targetAfter ∧
      sourceAfter.frames = [] ∧ targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, sourceValue, physical, path, returned, rootedAfter,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_returnPreciseAtRoot_of_step activeResult rooted admitted sourceStep
  have emptyAfter : sourceAfter.frames = [] := sourceFramesEq.trans empty
  exact ⟨targetAfter, sourceValue, physical, path,
    returned.yieldAtRoot_of_empty rootedAfter emptyAfter, emptyAfter, targetFramesEq⟩

/-- A direct local binding preserves the compiler-owned root agreement.
The successor keeps the exact active/caller result indices, evolved witness
and runtime, bound environment, and allocation-budget subtraction. The same
positive target path and frame equations come from the existing producer;
only its root metadata is reindexed. No global relation or admission changes. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_directLetAtRoot_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ReuseBudgetedDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextRuntime sourceValue nextStore resumedLocals nextWitness
        nextFacts nextTargetCode targetCount,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetCount target targetAfter ∧
        0 < targetCount ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult nextFacts
          (remainingBytes - directLetAllocationCost decl) nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation nextStore
          resumedLocals nextTargetCode nextWitness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧ targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
      nextWitness, nextFacts, nextTargetCode, targetCount, targetPath,
      targetPositive, nextRelated, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_directLetWithFrames_of_step supported budget sourceStep
  exact ⟨targetAfter, nextRuntime, sourceValue, nextStore, resumedLocals,
    nextWitness, nextFacts, nextTargetCode, targetCount, targetPath, targetPositive,
    nextRelated, rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation, sourceFramesEq, targetFramesEq⟩

/-- Regression: recover the exact active/root equality from the *successor*
of the direct let when there is no caller. This exercises the retained root
index and source-frame equation, with no result-kind equality premise. The
existing heterogeneous-spine and same-i32-lane negative tests below remain
independent of this empty-continuation specialization. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ReuseBudgetedDirectSupported context facts decl)
    (budget : directLetAllocationCost decl ≤ remainingBytes)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) : functionResult = rootResult := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, nextRooted, sourceFramesEq, _⟩ :=
    related.advance_directLetAtRoot_of_step rooted supported budget sourceStep
  exact nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)

/-- An erased default-only case preserves the exact root index while taking
zero target steps. The validated successor retains runtime, witness, locals,
budget and active/caller result indices. Reindex only the source frames; the
target is unchanged. The existing strict source-rank decrease is retained. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_defaultOnlyCaseAtRoot_of_step
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : DefaultOnlyCaseSupported sourceRuntime sourceEnv cases selected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 0 target
        target ∧
      ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
        sourceModule sourceFunction targetModule hosts spec externals labels
        entryRuntime entryStore entryWitness functionResult callerExpectedResult
        facts remainingBytes sourceRuntime sourceEnv selected targetStore
        targetLocals targetCode witness sourceAfter target,
      ConcreteStructuredValidationAgreesAtRoot rootResult
        nextRelated.agrees nextRelated.frames.validation ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source ∧
      sourceAfter.frames = source.frames := by
  obtain ⟨path, nextRelated, rank, sourceFramesEq⟩ :=
    related.advance_defaultOnlyCaseWithFrames_of_step supported sourceStep
  exact ⟨path, nextRelated, rooted.reindex sourceFramesEq rfl
    nextRelated.agrees nextRelated.frames.validation, rank, sourceFramesEq⟩

/-- Regression: the rooted successor supplies exact active/root precision
with no caller, alongside the zero-step target path and strict rank decrease.
No root/active-kind equality premise is assumed. -/
example
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {selected : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : DefaultOnlyCaseSupported sourceRuntime sourceEnv cases selected)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 0 target target ∧
      compilerStructuredControlRank sourceAfter < compilerStructuredControlRank source ∧
      functionResult = rootResult := by
  obtain ⟨path, _, nextRooted, rank, sourceFramesEq⟩ :=
    related.advance_defaultOnlyCaseAtRoot_of_step rooted supported sourceStep
  exact ⟨path, rank, nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

section RootedTestedCases

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {admittedSelected : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

/-- Preserve root identity through object case tests. Keep the exact 5-step
cost per test, selected branch, target-only labels and existing zero-rank
condition; do not equate source callers with target case labels. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_objectCasesAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ObjectConstructorCasesSupported context sourceRuntime
      sourceEnv cases admittedSelected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ testCount targetAfter selected selectedTarget,
      ∃ targetSuffix : Wasm.Program,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          (5 * testCount) target targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals
          (List.replicate testCount none ++ labels)
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          selected targetStore
          { targetLocals with values := targetLocals.values } selectedTarget
          witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        SourceCaseResult sourceRuntime sourceEnv cases selected ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames =
          structuredWasmCaseLabels (targetLocals.values.drop 0) targetSuffix
            testCount ++ target.frames ∧
        (5 * testCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix, path,
      nextRelated, selectedResult, sourceFramesEq, targetFramesEq, zeroRank⟩ :=
    related.advance_objectCasesWithFrames_of_step supported sourceStep
  have pushed := rooted.case (belowStack := targetLocals.values.drop 0)
    (targetRest := targetSuffix) (testCount := testCount)
  exact ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix, path,
    nextRelated, pushed.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    selectedResult, sourceFramesEq, targetFramesEq, zeroRank⟩

/-- Regression over the actual object producer: an empty source caller
stack still determines the root, even with target-only labels. Exercise both
the zero-test rank result and the nonempty nested/outer-label frame shape. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ObjectConstructorCasesSupported context sourceRuntime
      sourceEnv cases admittedSelected)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ testCount targetAfter selected, ∃ targetSuffix : Wasm.Program,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          (5 * testCount) target targetAfter ∧
        SourceCaseResult sourceRuntime sourceEnv cases selected ∧
        sourceAfter.frames = source.frames ∧
        functionResult = rootResult ∧
        (testCount = 0 →
          targetAfter = target ∧
          targetAfter.frames = target.frames ∧
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) ∧
        (∀ count, testCount = count + 1 →
          targetAfter.frames =
            List.replicate count (.label 0 (targetLocals.values.drop 0) []) ++
              .label 0 (targetLocals.values.drop 0) targetSuffix :: target.frames) := by
  obtain ⟨testCount, targetAfter, selected, _, targetSuffix, path,
      _, nextRooted, selectedResult, sourceFramesEq, targetFramesEq, zeroRank⟩ :=
    related.advance_objectCasesAtRoot_of_step rooted supported sourceStep
  refine ⟨testCount, targetAfter, selected, targetSuffix, path, selectedResult,
    sourceFramesEq, nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty),
    ?_, ?_⟩
  · intro zero
    have emptyPath : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        0 target targetAfter := by simpa [zero] using path
    refine ⟨emptyPath.eq_of_zero.symm, ?_, zeroRank (by simp [zero])⟩
    simpa [zero, structuredWasmCaseLabels] using targetFramesEq
  · intro count nonzero
    simpa [nonzero, structuredWasmCaseLabels, List.append_assoc] using targetFramesEq

/-- Preserve root identity through UInt8 case tests. Keep the exact 4-step
cost per test, selected branch, target-only labels and existing zero-rank
condition; do not equate source callers with target case labels. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_scalarUInt8CasesAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ScalarUInt8CasesSupported context sourceRuntime sourceEnv cases
      admittedSelected)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ testCount targetAfter selected selectedTarget,
      ∃ targetSuffix : Wasm.Program,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          (4 * testCount) target targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals
          (List.replicate testCount none ++ labels)
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          selected targetStore
          { targetLocals with values := targetLocals.values } selectedTarget
          witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        SourceCaseResult sourceRuntime sourceEnv cases selected ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames =
          structuredWasmCaseLabels (targetLocals.values.drop 0) targetSuffix
            testCount ++ target.frames ∧
        (4 * testCount = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix, path,
      nextRelated, selectedResult, sourceFramesEq, targetFramesEq, zeroRank⟩ :=
    related.advance_scalarUInt8CasesWithFrames_of_step supported sourceStep
  have pushed := rooted.case (belowStack := targetLocals.values.drop 0)
    (targetRest := targetSuffix) (testCount := testCount)
  exact ⟨testCount, targetAfter, selected, selectedTarget, targetSuffix, path,
    nextRelated, pushed.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    selectedResult, sourceFramesEq, targetFramesEq, zeroRank⟩

/-- Regression over the actual UInt8 producer: an empty source caller
stack still determines the root, even with target-only labels. Exercise both
the zero-test rank result and the nonempty nested/outer-label frame shape. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ScalarUInt8CasesSupported context sourceRuntime sourceEnv cases
      admittedSelected)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ testCount targetAfter selected, ∃ targetSuffix : Wasm.Program,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          (4 * testCount) target targetAfter ∧
        SourceCaseResult sourceRuntime sourceEnv cases selected ∧
        sourceAfter.frames = source.frames ∧
        functionResult = rootResult ∧
        (testCount = 0 →
          targetAfter = target ∧
          targetAfter.frames = target.frames ∧
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) ∧
        (∀ count, testCount = count + 1 →
          targetAfter.frames =
            List.replicate count (.label 0 (targetLocals.values.drop 0) []) ++
              .label 0 (targetLocals.values.drop 0) targetSuffix :: target.frames) := by
  obtain ⟨testCount, targetAfter, selected, _, targetSuffix, path,
      _, nextRooted, selectedResult, sourceFramesEq, targetFramesEq, zeroRank⟩ :=
    related.advance_scalarUInt8CasesAtRoot_of_step rooted supported sourceStep
  refine ⟨testCount, targetAfter, selected, targetSuffix, path, selectedResult,
    sourceFramesEq, nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty),
    ?_, ?_⟩
  · intro zero
    have emptyPath : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        0 target targetAfter := by simpa [zero] using path
    refine ⟨emptyPath.eq_of_zero.symm, ?_, zeroRank (by simp [zero])⟩
    simpa [zero, structuredWasmCaseLabels] using targetFramesEq
  · intro count nonzero
    simpa [nonzero, structuredWasmCaseLabels, List.append_assoc] using targetFramesEq

/-- Production validation selects the default-only, object or UInt8 protocol;
the successful source step supplies its dynamic branch. Compose the accepted
rooted rules without a caller-supplied classifier, branch or target path.

Like `advance_cases_of_validated_step`, this uniform interface existentially
hides the target-step count and successor labels. The specialized producers
retain their exact zero/5*n/4*n costs. The named successor also retains the
compiler-internal root index, source branch and unchanged source frames. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_casesAtRoot_of_validated_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetSteps targetAfter selected selectedTarget nextLabels,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetSteps target targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals
          nextLabels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
          selected targetStore
          { targetLocals with values := targetLocals.values } selectedTarget
          witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        SourceCaseResult sourceRuntime sourceEnv cases selected ∧
        sourceAfter.frames = source.frames ∧
        (targetSteps = 0 →
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨selected, sourceResult, _sourceAfterEq⟩ :=
    related.core.core.focus.caseResult_of_step sourceStep
  rcases related.productionCasesSupported_of_validation sourceResult with
      defaultOnly | objectCases | scalarCases
  · obtain ⟨targetPath, nextRelated, nextRooted, rank, sourceFramesEq⟩ :=
      related.advance_defaultOnlyCaseAtRoot_of_step rooted defaultOnly sourceStep
    exact ⟨0, target, selected, targetCode, labels, targetPath,
      nextRelated, nextRooted, sourceResult, sourceFramesEq, fun _ => rank⟩
  · obtain ⟨testCount, targetAfter, selected, selectedTarget, _, targetPath,
        nextRelated, nextRooted, selectedResult, sourceFramesEq, _, zeroRank⟩ :=
      related.advance_objectCasesAtRoot_of_step rooted objectCases sourceStep
    exact ⟨5 * testCount, targetAfter, selected, selectedTarget,
      List.replicate testCount none ++ labels, targetPath, nextRelated,
      nextRooted, selectedResult, sourceFramesEq, zeroRank⟩
  · obtain ⟨testCount, targetAfter, selected, selectedTarget, _, targetPath,
        nextRelated, nextRooted, selectedResult, sourceFramesEq, _, zeroRank⟩ :=
      related.advance_scalarUInt8CasesAtRoot_of_step rooted scalarCases sourceStep
    exact ⟨4 * testCount, targetAfter, selected, selectedTarget,
      List.replicate testCount none ++ labels, targetPath, nextRelated,
      nextRooted, selectedResult, sourceFramesEq, zeroRank⟩

/-- Regression through the actual validation-derived dispatcher: the successor
retains exact root precision with no source caller, regardless of which family
validation selected. No case-admission or selected-branch premise is supplied.
Zero target steps still imply an unchanged target and strict source progress. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.cases cases) targetStore targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetSteps targetAfter selected,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
          targetSteps target targetAfter ∧
        SourceCaseResult sourceRuntime sourceEnv cases selected ∧
        functionResult = rootResult ∧
        (targetSteps = 0 →
          targetAfter = target ∧
          compilerStructuredControlRank sourceAfter <
            compilerStructuredControlRank source) := by
  obtain ⟨targetSteps, targetAfter, selected, _, _, path,
      _, nextRooted, selectedResult, sourceFramesEq, zeroRank⟩ :=
    related.advance_casesAtRoot_of_validated_step rooted sourceStep
  refine ⟨targetSteps, targetAfter, selected, path, selectedResult,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty), ?_⟩
  intro zero
  have emptyPath : FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
      0 target targetAfter := by simpa [zero] using path
  exact ⟨emptyPath.eq_of_zero.symm, zeroRank zero⟩

end RootedTestedCases

section RootedReferenceCounts

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}

/-- Persistent increment derives its own admission and retains the root on
its named successor. The target, runtime, witness and budget stay unchanged;
the target takes zero steps while the source rank strictly decreases. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_incPersistentAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check true continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.inc objectId amount check true continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      sourceAfter.frames = source.frames ∧
      ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec externals
        labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        continuation targetStore targetLocals targetCode witness sourceAfter target,
      ConcreteStructuredValidationAgreesAtRoot rootResult
        nextRelated.agrees nextRelated.frames.validation ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  obtain ⟨admitted, path, framesEq, nextRelated, rank⟩ :=
    related.advance_incPersistent_of_step
      (module := module) (hostEnv := hostEnv) sourceStep
  exact ⟨admitted, path, framesEq, nextRelated,
    rooted.reindex framesEq rfl nextRelated.agrees nextRelated.frames.validation,
    rank⟩

/-- The actual persistent increment producer derives admission, takes zero
target steps and recovers exact root precision from its successor. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check true continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.inc objectId amount check true continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source ∧
      functionResult = rootResult := by
  obtain ⟨admitted, path, framesEq, _, nextRooted, rank⟩ :=
    related.advance_incPersistentAtRoot_of_step
      (module := module) (hostEnv := hostEnv) rooted sourceStep
  exact ⟨admitted, path, rank,
    nextRooted.functionResult_eq_of_empty (framesEq.trans empty)⟩

/-- Persistent decrement retains the same zero-cost, admission-producing
transition and exact root index, without a persistent-admission premise. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_decPersistentAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.dec objectId amount check true objectFields? continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      sourceAfter.frames = source.frames ∧
      ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
        functionCode sourceModule sourceFunction targetModule hosts spec externals
        labels entryRuntime entryStore entryWitness functionResult
        callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
        continuation targetStore targetLocals targetCode witness sourceAfter target,
      ConcreteStructuredValidationAgreesAtRoot rootResult
        nextRelated.agrees nextRelated.frames.validation ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source := by
  obtain ⟨admitted, path, framesEq, nextRelated, rank⟩ :=
    related.advance_decPersistent_of_step
      (module := module) (hostEnv := hostEnv) sourceStep
  exact ⟨admitted, path, framesEq, nextRelated,
    rooted.reindex framesEq rfl nextRelated.agrees nextRelated.frames.validation,
    rank⟩

/-- The actual persistent decrement producer derives admission, takes zero
target steps and recovers exact root precision from its successor. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
        functionResult facts sourceRuntime sourceEnv 0
        (.dec objectId amount check true objectFields? continuation) ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      compilerStructuredControlRank sourceAfter <
        compilerStructuredControlRank source ∧
      functionResult = rootResult := by
  obtain ⟨admitted, path, framesEq, _, nextRooted, rank⟩ :=
    related.advance_decPersistentAtRoot_of_step
      (module := module) (hostEnv := hostEnv) rooted sourceStep
  exact ⟨admitted, path, rank,
    nextRooted.functionResult_eq_of_empty (framesEq.trans empty)⟩

/-- Ordinary increment retains the root across the existing exact two-step
path. Keep its effect predicate, runtime/store evolution, witness and budget;
only transport compiler-internal metadata through the exposed frame equations. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryIncrementAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : OrdinaryIncrementEffectSupported context sourceRuntime
      sourceEnv (.inc objectId amount check false continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec externals
          labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryIncrementWithFrames_of_step supported sourceStep
  exact ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
    rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- Unlike persistent operations, the actual ordinary increment
producer retains an exact two-step path while recovering successor root precision.
Its existing effect predicate and runtime evolution are not weakened. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : OrdinaryIncrementEffectSupported context sourceRuntime
      sourceEnv (.inc objectId amount check false continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryIncrementAtRoot_of_step rooted supported sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

/-- Ordinary decrement uses the same rooted reindexing over its existing
recursive-decrement contract and two-step path. This adds no release,
allocation or ownership theorem, and does not weaken its effect predicate. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDecrementAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : OrdinaryDecrementEffectSupported context sourceRuntime
      sourceEnv (.dec objectId amount check false objectFields? continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec externals
          labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDecrementWithFrames_of_step supported sourceStep
  exact ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
    rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- Unlike persistent operations, the actual ordinary decrement
producer retains an exact two-step path while recovering successor root precision.
Its existing effect predicate and runtime evolution are not weakened. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : OrdinaryDecrementEffectSupported context sourceRuntime
      sourceEnv (.dec objectId amount check false objectFields? continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDecrementAtRoot_of_step rooted supported sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

/-- Explicit delete transports the same root through the existing two-step
rule, including erased physical zero, without changing its effect contract. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDeleteAtRoot_of_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.del objectId continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : OrdinaryDeleteEffectSupported context sourceRuntime
      sourceEnv (.del objectId continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec externals
          labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDeleteWithFrames_of_step supported sourceStep
  exact ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
    rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- Compiler-validated increment derives its local/effect facts and retains
root identity on the named successor. The only extra execution premise is the
unchanged finite-wasm32 reference-count headroom condition. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryIncrementAtRoot_of_validated_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (fits : ∀ (sourceObject : Value) (location : Location) (cell : HeapCell),
      lookupValue sourceEnv objectId = .ok sourceObject →
        sourceObject = .object (.heap location) →
          findCell? sourceRuntime.heap location = some cell →
            cell.rc + amount < UInt32.size)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec externals
          labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees, localAlignment⟩ :=
    related.core.validation
  obtain ⟨objectKind, objectCompiled, objectRefines⟩ :=
    validated.incOrdinary_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.core.core.focus.incOrdinary_source_of_step sourceStep
  let supported : OrdinaryIncrementEffectSupported context sourceRuntime
      sourceEnv (.inc objectId amount check false continuation) continuation
      nextRuntime :=
    .inc sourceRuntime nextRuntime sourceEnv objectId amount check continuation
      objectKind sourceObject objectCompiled objectRefines objectLookup updated
      (fun location cell sourceObjectEq found =>
        fits sourceObject location cell objectLookup sourceObjectEq found)
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryIncrementAtRoot_of_step rooted supported sourceStep
  exact ⟨nextRuntime, targetAfter, nextStore, nextTargetCode, path, nextRelated,
    nextRooted, sourceFramesEq, targetFramesEq⟩

/-- The validation-derived increment producer needs no caller-supplied
effect facts. Root precision is recovered from its actual successor, retaining
the exact two-step path and both frame equations. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (fits : ∀ (sourceObject : Value) (location : Location) (cell : HeapCell),
      lookupValue sourceEnv objectId = .ok sourceObject →
        sourceObject = .object (.heap location) →
          findCell? sourceRuntime.heap location = some cell →
            cell.rc + amount < UInt32.size)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨_, targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryIncrementAtRoot_of_validated_step rooted fits sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

/-- Compiler-validated decrement derives all current-node effect facts from
validation and the successful source step, with no additional caller premise. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDecrementAtRoot_of_validated_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec externals
          labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees, localAlignment⟩ :=
    related.core.validation
  obtain ⟨objectKind, objectCompiled, objectRefines⟩ :=
    validated.decOrdinary_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.core.core.focus.decOrdinary_source_of_step sourceStep
  let supported : OrdinaryDecrementEffectSupported context sourceRuntime
      sourceEnv
      (.dec objectId amount check false objectFields? continuation)
      continuation nextRuntime :=
    .dec sourceRuntime nextRuntime sourceEnv objectId amount check objectFields?
      continuation objectKind sourceObject objectCompiled objectRefines
      objectLookup updated
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDecrementAtRoot_of_step rooted supported sourceStep
  exact ⟨nextRuntime, targetAfter, nextStore, nextTargetCode, path, nextRelated,
    nextRooted, sourceFramesEq, targetFramesEq⟩

/-- The validation-derived decrement producer needs no caller-supplied
effect facts. Root precision is recovered from its actual successor, retaining
the exact two-step path and both frame equations. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨_, targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDecrementAtRoot_of_validated_step rooted sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

/-- Compiler-validated explicit deletion retains root identity on its named
successor. Physical-zero deletion is covered by the same existing rule; no new
effect, admission or nonzero premise is introduced. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_ordinaryDeleteAtRoot_of_validated_step
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.del objectId continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ nextRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context
          functionCode sourceModule sourceFunction targetModule hosts spec externals
          labels entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees, localAlignment⟩ :=
    related.core.validation
  have objectCompiled := validated.del_compiler agrees
  obtain ⟨sourceObject, nextRuntime, objectLookup, updated⟩ :=
    related.core.core.focus.del_source_of_step sourceStep
  let supported : OrdinaryDeleteEffectSupported context sourceRuntime sourceEnv
      (.del objectId continuation) continuation nextRuntime :=
    .del sourceRuntime nextRuntime sourceEnv objectId continuation .object
      sourceObject objectCompiled objectLookup updated
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDeleteAtRoot_of_step rooted supported sourceStep
  exact ⟨nextRuntime, targetAfter, nextStore, nextTargetCode, path, nextRelated,
    nextRooted, sourceFramesEq, targetFramesEq⟩

/-- The validation-derived delete producer needs no caller-supplied
effect facts. Root precision is recovered from its actual successor, retaining
the exact two-step path and both frame equations. -/
example
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.del objectId continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨_, targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_ordinaryDeleteAtRoot_of_validated_step rooted sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

end RootedReferenceCounts

section RootedConstructorTags

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

/-- Constructor-tag mutation retains the same root on its actual named
successor through the existing two-step effect rule and frame reindexing. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_constructorTagAtRoot_of_step
    {objectId : Lean.FVarId} {tag : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.setTag objectId tag continuation) targetStore targetLocals targetCode
      witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ConstructorTagEffectSupported context sourceRuntime sourceEnv
      (.setTag objectId tag continuation) continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_constructorTagWithFrames_of_step supported sourceStep
  exact ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
    rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- Constructor-tag mutation derives width/local facts from production
validation and heap-shape/effect facts from the successful source step. No
caller effect or admission premise is needed to retain the original root. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_constructorTagAtRoot_of_validated_step
    {objectId : Lean.FVarId} {tag : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.setTag objectId tag continuation) targetStore targetLocals targetCode
      witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees, localAlignment⟩ :=
    related.core.validation
  obtain ⟨tagFits, objectCompiled⟩ := validated.setTag_compiler agrees
  obtain ⟨location, cell, semantic, resultRuntime, objectLookup, updated,
      found, live, objectEq⟩ :=
    related.core.core.focus.setTag_source_of_step sourceStep
  let supported : ConstructorTagEffectSupported context sourceRuntime sourceEnv
      (.setTag objectId tag continuation) continuation resultRuntime :=
    .setTag sourceRuntime resultRuntime sourceEnv objectId tag continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq tagFits
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_constructorTagAtRoot_of_step rooted supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, path, nextRelated,
    nextRooted, sourceFramesEq, targetFramesEq⟩

/-- The actual validation-derived tag producer recovers root precision from
its successor without caller-supplied effect facts or result-kind equality.
Its exact two-step path and both frame equations remain visible. -/
example
    {objectId : Lean.FVarId} {tag : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.setTag objectId tag continuation) targetStore targetLocals targetCode
      witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 2 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨_, targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_constructorTagAtRoot_of_validated_step rooted sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

end RootedConstructorTags

section RootedScalarFields

variable
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult rootResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}

/-- `USize` field mutation retains the original root through its existing
three-step effect proof and the unchanged source/target frame equations. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_usizeFieldAtRoot_of_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) targetStore targetLocals
      targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : USizeFieldEffectSupported context sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_usizeFieldWithFrames_of_step supported sourceStep
  exact ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
    rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- `USize` field mutation reconstructs compiler and dynamic facts from
validation and successful source execution. No extra caller effect, admission
or source-layout premise is needed for root transport. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_usizeFieldAtRoot_of_validated_step
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) targetStore targetLocals
      targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees, localAlignment⟩ :=
    related.core.validation
  obtain ⟨objectCompiled, fieldCompiled⟩ := validated.uset_compiler agrees
  obtain ⟨location, cell, semantic, field, resultRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq, slotStart, slotEnd⟩ :=
    related.core.core.focus.uset_source_of_step sourceStep
  let supported : USizeFieldEffectSupported context sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) continuation resultRuntime :=
    .uset sourceRuntime resultRuntime sourceEnv objectId fieldId index
      continuation location cell semantic field objectCompiled fieldCompiled
      objectLookup fieldLookup updated found live objectEq slotStart slotEnd
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_usizeFieldAtRoot_of_step rooted supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, path, nextRelated,
    nextRooted, sourceFramesEq, targetFramesEq⟩

/-- The actual validated USize producer recovers precision from its
successor with only its existing premises. No caller effect facts or
result-kind equality are supplied; the exact three-step path is retained. -/
example
    {objectId fieldId : Lean.FVarId} {index : Nat}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) targetStore targetLocals
      targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨_, targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_usizeFieldAtRoot_of_validated_step rooted sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

/-- Packed-scalar mutation retains the original root through the existing
layout-checked three-step effect proof. Its effect contract is unchanged. -/
theorem ConcreteStructuredValidatedCodeOutcome.advance_scalarFieldAtRoot_of_step
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (supported : ScalarFieldEffectSupported context sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      continuation nextRuntime)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes nextRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      sourceFramesEq, targetFramesEq⟩ :=
    related.advance_scalarFieldWithFrames_of_step supported sourceStep
  exact ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
    rooted.reindex sourceFramesEq targetFramesEq
      nextRelated.agrees nextRelated.frames.validation,
    sourceFramesEq, targetFramesEq⟩

/-- Packed-scalar mutation derives compiler/dynamic facts and retains the
root, keeping exactly the existing source descriptor-layout `fieldTyped`
premise. That invariant is not derived from validation or source execution. -/
theorem
    ConcreteStructuredValidatedCodeOutcome.advance_scalarFieldAtRoot_of_validated_step
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime
      sourceEnv objectId fieldId slotIndex byteOffset)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ resultRuntime targetAfter nextStore nextTargetCode,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        ∃ nextRelated : ConcreteStructuredValidatedCodeOutcome program context functionCode
          sourceModule sourceFunction targetModule hosts spec externals labels
          entryRuntime entryStore entryWitness functionResult
          callerExpectedResult facts remainingBytes resultRuntime sourceEnv
          continuation nextStore targetLocals nextTargetCode witness sourceAfter
          targetAfter,
        ConcreteStructuredValidationAgreesAtRoot rootResult
          nextRelated.agrees nextRelated.frames.validation ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  obtain ⟨_joins, _locals, _validatorFacts, _sharing, validated, agrees, localAlignment⟩ :=
    related.core.validation
  obtain ⟨fieldKind, objectCompiled, fieldCompiled, _annotationFound,
      _scalarSupported⟩ := validated.sset_compiler agrees
  obtain ⟨location, cell, semantic, field, resultRuntime, objectLookup,
      fieldLookup, updated, found, live, objectEq⟩ :=
    related.core.core.focus.sset_source_of_step sourceStep
  let supported : ScalarFieldEffectSupported context sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      continuation resultRuntime :=
    .sset sourceRuntime resultRuntime sourceEnv objectId fieldId slotIndex
      byteOffset type continuation location cell semantic field fieldKind
      objectCompiled fieldCompiled objectLookup fieldLookup updated found live
      objectEq (fun objectRelated descriptorFound =>
        fieldTyped fieldCompiled objectLookup found live objectEq objectRelated
          descriptorFound)
  obtain ⟨targetAfter, nextStore, nextTargetCode, path, nextRelated,
      nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_scalarFieldAtRoot_of_step rooted supported sourceStep
  exact ⟨resultRuntime, targetAfter, nextStore, nextTargetCode, path, nextRelated,
    nextRooted, sourceFramesEq, targetFramesEq⟩

/-- The actual validated packed-scalar producer recovers precision from its
successor with only its existing premises. No caller effect facts or
result-kind equality are supplied; the exact three-step path is retained. -/
example
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation) targetStore
      targetLocals targetCode witness source target)
    (rooted : ConcreteStructuredValidationAgreesAtRoot rootResult
      related.agrees related.frames.validation)
    (fieldTyped : ConcreteScalarFieldMutationTyped context sourceRuntime
      sourceEnv objectId fieldId slotIndex byteOffset)
    (sourceStep : executeStep externals source = .next sourceAfter)
    (empty : source.frames = []) :
    ∃ targetAfter,
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
          targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames ∧
        functionResult = rootResult := by
  obtain ⟨_, targetAfter, _, _, path, _, nextRooted, sourceFramesEq, targetFramesEq⟩ :=
    related.advance_scalarFieldAtRoot_of_validated_step rooted fieldTyped sourceStep
  exact ⟨targetAfter, path, sourceFramesEq, targetFramesEq,
    nextRooted.functionResult_eq_of_empty (sourceFramesEq.trans empty)⟩

end RootedScalarFields

/-- Heterogeneous nested calls retain the original result, not the deepest
callee's kind or the immediate consumer's kind. -/
example : concreteStructuredRootResultKind .uint8
    [(.object, some .tobject), (.uint64, none)] = .uint64 := rfl

/-- Root precision is meaningful: a different selected result is rejected even
when both root kinds use the same physical i32 lane. -/
example : concreteStructuredRootResultKind .uint8
    [(.uint64, some .tobject), (.object, none)] ≠ .tobject := by
  intro impossible
  cases impossible

end FirTalos.Concrete
