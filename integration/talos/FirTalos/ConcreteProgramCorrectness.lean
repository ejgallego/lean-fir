import FirTalos.ConcreteDeclarationCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
Exact control-flow postcondition used by syntax-directed case composition.

Unlike `ConcreteFunctionBodyPost`, this assertion admits only an explicit
Wasm `return`. It is therefore invariant under the resumption wrapper installed
around generated case arms: returns pass through unchanged, while fallthrough
and branch continuations are deliberately unavailable.
-/
def ExactReturnControlPost (afterCall : Wasm.Store Host)
    (physical : Wasm.Value) : Wasm.Assertion Host :=
  fun continuation =>
    continuation = .Return afterCall [physical]

/-- Weakening the target continuation preserves the concrete code judgment. -/
theorem CodeWP.conseq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {code : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q Q' : Wasm.Assertion Host}
    (post : Q ⇛ Q')
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code target targetStore targetLocals witness
        tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv code target targetStore targetLocals witness
      tail Q' :=
  ⟨correct.1, correct.2.1, Wasm.wp.conseq post correct.2.2⟩

/--
Concrete-host return rule with the exact control result exposed directly.
This is the terminal leaf used internally by case-aware structural proofs.
-/
theorem codeWP_return_to_exactControlPost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {result : Lean.FVarId}
    {sourceValue : Value}
    {kind : AbiKind}
    {resultIndex : Nat}
    {physical : Wasm.Value}
    (localCompiled :
      Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (targetLookup : targetLocals.get resultIndex = some physical) :
    CodeWP context sourceModule sourceFunction labels module hostEnv sourceRuntime
      sourceEnv (.return result) [.localGet resultIndex, .ret]
      targetStore targetLocals witness []
      (ExactReturnControlPost targetStore physical) := by
  obtain ⟨actual, actualLookup, _⟩ :=
    stateRelated.resolve sourceLookup resultFound kindAt
  rw [targetLookup] at actualLookup
  injection actualLookup with physicalEq
  subst actual
  refine ⟨codeAdapted_return localCompiled resultFound, stateRelated, ?_⟩
  rw [Wasm.wp_localGet_cons]
  have targetLookupWithStack :
      ({ targetLocals with values := [] } : Wasm.Locals).get resultIndex =
        some physical := by
    simpa [Wasm.Locals.get] using targetLookup
  simp only [targetLookupWithStack]
  rw [Wasm.wp_ret_cons]
  rfl

/-- Concrete-host return rule for an arbitrary generated function and caller
operand remainder. The compiler-selected local contains the exact related
physical result, and Talos's body postcondition restores the caller tail. -/
theorem codeWP_return_to_exactBodyPost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetFunction : Wasm.Function}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {result : Lean.FVarId}
    {sourceValue : Value}
    {kind : AbiKind}
    {resultIndex : Nat}
    {physical : Wasm.Value}
    (localCompiled :
      Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (targetLookup : targetLocals.get resultIndex = some physical)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1) :
    CodeWP context sourceModule sourceFunction labels module hostEnv sourceRuntime
      sourceEnv (.return result) [.localGet resultIndex, .ret]
      targetStore targetLocals witness []
      (ConcreteFunctionBodyPost targetFunction
        (parameters ++ callerTail)
        (ExactReturnPost targetStore physical callerTail)) := by
  obtain ⟨actual, actualLookup, _⟩ :=
    stateRelated.resolve sourceLookup resultFound kindAt
  rw [targetLookup] at actualLookup
  injection actualLookup with physicalEq
  subst actual
  refine ⟨codeAdapted_return localCompiled resultFound, stateRelated, ?_⟩
  rw [Wasm.wp_localGet_cons]
  have targetLookupWithStack :
      ({ targetLocals with values := [] } : Wasm.Locals).get resultIndex =
        some physical := by
    simpa [Wasm.Locals.get] using targetLookup
  simp only [targetLookupWithStack]
  rw [Wasm.wp_ret_cons]
  simp [ConcreteFunctionBodyPost, ExactReturnPost, resultCount,
    ← parameterCount]

/-- Generic concrete recursive rule for a direct, non-calling `let`. Every
operation-specific W6 rule only needs to construct `LetStepSimulates`; this
theorem supplies compiler/adaptor composition with an arbitrary continuation
postcondition. -/
theorem codeWP_letValue
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {resultIndex : Nat}
    {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex witness nextWitness)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest nextStore nextLocals nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals witness tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Turn a concrete case-chain proof back into the enclosing source `.cases`
judgment. The chain already carries target adaptation, initial refinement, and
the exact Talos weakest precondition. -/
theorem codeWP_cases
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {cases : LCNF.Cases .impure}
    {fallback : List Fir.Wasm.Instruction}
    {target : Wasm.Program}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (fallbackCompiled :
      Fir.Wasm.compileCaseFallback context cases.alts.toList = .ok fallback)
    (chain :
      CaseChainWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv cases.discr cases.alts.toList fallback target
        targetStore targetLocals witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.cases cases) target targetStore targetLocals
      witness tail Q := by
  exact ⟨codeAdapted_cases ⟨fallback, fallbackCompiled, chain.1⟩,
    chain.2.1, chain.2.2⟩

/-- Concrete case-control-flow boundary. Operation-specific proofs establish
the selected source branch and transform any proof of that branch into a proof
of the complete generated test chain. Universality over the operand tail and
postcondition makes the step reusable inside arbitrary generated functions. -/
def ConcreteCasesStepSimulates
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (cases : LCNF.Cases .impure)
    (selected : LCNF.Code .impure)
    (target selectedTarget : Wasm.Program)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  SourceCaseResult sourceRuntime sourceEnv cases selected ∧
    ∀ (tail : List Wasm.Value) (Q : Wasm.Assertion Host),
      CodeWP context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv selected selectedTarget targetStore
          targetLocals witness tail Q →
        CodeWP context sourceModule sourceFunction labels module hostEnv
          sourceRuntime sourceEnv (.cases cases) target targetStore targetLocals
          witness tail Q

/-- Recursive concrete `CodeWP` rule for a source-selected case branch. -/
theorem codeWP_caseOf
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {cases : LCNF.Cases .impure}
    {selected : LCNF.Code .impure}
    {target selectedTarget : Wasm.Program}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (step :
      ConcreteCasesStepSimulates context sourceModule sourceFunction labels
        module hostEnv sourceRuntime sourceEnv cases selected target
        selectedTarget targetStore targetLocals witness)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv selected selectedTarget targetStore targetLocals
        witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.cases cases) target targetStore targetLocals
      witness tail Q :=
  step.2 tail Q continued

/-- Prefix a successful executable source run by any finite sequence of
interpreter steps. This is the source-side composition rule needed once the
concrete syntax certificate admits calls and foreign operations. -/
theorem execEvaluates_of_steps
    {externals : ExternalImpl}
    {prefixCount : Nat}
    {first middle : MachineState}
    {observation : Observation}
    (prefixSteps : ExecSteps externals prefixCount first middle)
    (continued : ExecEvaluates externals middle observation) :
    ExecEvaluates externals first observation := by
  induction prefixSteps with
  | refl =>
      exact continued
  | step head _ ih =>
      obtain ⟨count, final, steps, done⟩ := ih continued
      exact ⟨count + 1, final, .step head steps, done⟩

private theorem evalLetValue_sourceCodeState_control_independent
    (context : Fir.Wasm.Context)
    (runtime : RuntimeState)
    (env : Env)
    (code : LCNF.Code .impure)
    (decl : LCNF.LetDecl .impure) :
    evalLetValue (sourceCodeState context runtime env code) decl =
      evalLetValue
        (sourceCodeState context runtime env (.return decl.fvarId)) decl := by
  cases decl.value <;> rfl

private theorem executeStep_source_let
    (externals : ExternalImpl)
    (context : Fir.Wasm.Context)
    (runtime nextRuntime : RuntimeState)
    (env : Env)
    (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure)
    (value : Value)
    (sourceStep :
      SourceLetResult context runtime env decl nextRuntime value) :
    executeStep externals
        (sourceCodeState context runtime env (.let decl continuation)) =
      .next
        (sourceCodeState context nextRuntime
          (bind env decl.fvarId value) continuation) := by
  have evaluated :
      evalLetValue
          (sourceCodeState context runtime env (.let decl continuation)) decl =
        .ok (nextRuntime, .value value) := by
    rw [evalLetValue_sourceCodeState_control_independent]
    exact sourceStep
  unfold sourceCodeState at evaluated
  simp [executeStep, coreStep, sourceCodeState, evaluated]

private theorem executeStep_source_cases
    (externals : ExternalImpl)
    (context : Fir.Wasm.Context)
    (runtime : RuntimeState)
    (env : Env)
    (cases : LCNF.Cases .impure)
    (selected : LCNF.Code .impure)
    (sourceStep : SourceCaseResult runtime env cases selected) :
    executeStep externals
        (sourceCodeState context runtime env (.cases cases)) =
      .next (sourceCodeState context runtime env selected) := by
  rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
  simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen]

theorem sourceLetResult_thenExecEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    {observation : Observation}
    (sourceStep :
      SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
        sourceValue)
    (continued :
      ExecEvaluates externals
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation)
        observation) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      observation := by
  apply execEvaluates_of_steps
      (.step
        (executeStep_source_let externals context sourceRuntime nextRuntime
          sourceEnv decl continuation sourceValue sourceStep)
        (.refl _))
    continued

theorem sourceCaseResult_thenExecEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {cases : LCNF.Cases .impure}
    {selected : LCNF.Code .impure}
    {observation : Observation}
    (sourceStep :
      SourceCaseResult sourceRuntime sourceEnv cases selected)
    (continued :
      ExecEvaluates externals
        (sourceCodeState context sourceRuntime sourceEnv selected)
        observation) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.cases cases))
      observation := by
  apply execEvaluates_of_steps
      (.step
        (executeStep_source_cases externals context sourceRuntime sourceEnv
          cases selected sourceStep)
        (.refl _))
    continued

theorem sourceEffectResult_thenExecEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {code continuation : LCNF.Code .impure}
    {observation : Observation}
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (continued :
      ExecEvaluates externals
        (sourceCodeState context nextRuntime sourceEnv continuation)
        observation) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code)
      observation := by
  apply execEvaluates_of_steps
      (.step (by simpa [sourceCodeState] using sourceStep externals) (.refl _))
    continued

theorem sourceExternalLetResult_thenExecEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    {observation : Observation}
    (sourceStep :
      SourceExternalLetResult context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (continued :
      ExecEvaluates externals
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation)
        observation) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      observation := by
  apply execEvaluates_of_steps
      (middle := sourceCodeState context nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) continuation)
      (by
        unfold SourceExternalLetResult at sourceStep
        simpa [sourceCodeState] using sourceStep)
    continued

theorem sourceLazyLetResult_thenExecEvaluates
    {path : LazyCachePath}
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    {observation : Observation}
    (sourceStep :
      SourceLazyLetResult path context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (continued :
      ExecEvaluates externals
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation)
        observation) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      observation := by
  obtain ⟨prefixCount, sourceSteps⟩ := sourceStep.execSteps
  apply execEvaluates_of_steps
      (middle := sourceCodeState context nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) continuation)
      (prefixCount := prefixCount)
      (by
        simpa [sourceCodeState] using sourceSteps)
    continued

theorem sourceCallLetResult_thenExecEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    {observation : Observation}
    (sourceStep :
      SourceCallLetResult context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (continued :
      ExecEvaluates externals
        (sourceCodeState context nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation)
        observation) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv (.let decl continuation))
      observation := by
  obtain ⟨count, callSteps⟩ := sourceStep
  apply execEvaluates_of_steps
      (middle := sourceCodeState context nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) continuation)
      (prefixCount := count)
      (by simpa [sourceCodeState] using callSteps)
    continued

/-- Syntax-directed W6 certificate for concrete return, direct-value,
case-control-flow, no-result-effect, call, external, and lazy-cache code.
Unlike `SuccessfulDeclaration`, this certificate derives its final
runtime/value facts from the return leaf and threads them backwards through
each concrete step. -/
inductive ConcreteCodeSimulation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl) :
    RuntimeState → Env → LCNF.Code .impure → Wasm.Program →
      Wasm.Store Host → Wasm.Locals → RefinementWitness →
      RuntimeState → Value → AbiKind → Wasm.Store Host →
      RefinementWitness → Wasm.Value → Prop where
  | ret
      (localCompiled :
        Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
      (resultFound :
        findFVar? (functionBindings sourceFunction) result = some resultIndex)
      (kindAt :
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some kind)
      (sourceLookup : lookup sourceEnv result = some sourceValue)
      (stateRelated :
        StateRelated sourceFunction sourceRuntime sourceEnv targetStore
          targetLocals witness)
      (targetLookup : targetLocals.get resultIndex = some physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.return result)
        [.localGet resultIndex, .ret] targetStore targetLocals witness
        sourceRuntime sourceValue kind targetStore witness physical
  | letValue
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        LetStepSimulates context sourceFunction module hostEnv decl targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
          targetLocals nextLocals resultIndex witness nextWitness)
      (continued :
        ConcreteCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultRuntime resultValue resultKind
          resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultRuntime resultValue resultKind
        resultStore resultWitness physical
  | callLet
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        CallLetStepSimulates context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
          nextLocals resultIndex witness nextWitness)
      (continued :
        ConcreteCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultRuntime resultValue resultKind
          resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultRuntime resultValue resultKind
        resultStore resultWitness physical
  | externalLet
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        ExternalLetStepSimulates context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
          nextLocals resultIndex witness nextWitness)
      (continued :
        ConcreteCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultRuntime resultValue resultKind
          resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultRuntime resultValue resultKind
        resultStore resultWitness physical
  | lazyLet
      (path : LazyCachePath)
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        LazyLetStepSimulates path context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
          nextLocals resultIndex witness nextWitness)
      (continued :
        ConcreteCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultRuntime resultValue resultKind
          resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultRuntime resultValue resultKind
        resultStore resultWitness physical
  | caseOf
      (target selectedTarget : Wasm.Program)
      (step :
        ConcreteCasesStepSimulates context sourceModule sourceFunction labels
          module hostEnv sourceRuntime sourceEnv cases selected target
          selectedTarget targetStore targetLocals witness)
      (continued :
        ConcreteCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals sourceRuntime sourceEnv selected
          selectedTarget targetStore targetLocals witness resultRuntime
          resultValue resultKind resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.cases cases) target
        targetStore targetLocals witness resultRuntime resultValue resultKind
        resultStore resultWitness physical
  | effect
      (target targetRest : Wasm.Program)
      (step :
        EffectStepSimulates context sourceModule sourceFunction labels module
          hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
          targetRest targetStore nextStore targetLocals witness nextWitness)
      (continued :
        ConcreteCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime sourceEnv continuation
          targetRest nextStore targetLocals nextWitness resultRuntime
          resultValue resultKind resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv code target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical

/-- The concrete syntax induction constructs the exact compiler/adaptor body
judgment for every caller operand remainder. -/
theorem ConcreteCodeSimulation.toCodeWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value}
    {resultKind : AbiKind}
    {physical : Wasm.Value}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv sourceCode target targetStore targetLocals witness
      []
      (ConcreteFunctionBodyPost targetFunction
        (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail)) := by
  induction simulation with
  | ret localCompiled resultFound kindAt sourceLookup stateRelated targetLookup =>
      exact codeWP_return_to_exactBodyPost (callerTail := callerTail)
        localCompiled resultFound kindAt sourceLookup stateRelated targetLookup
        parameterCount resultCount
  | letValue valueCompiled valueAdapted resultFound step continued ih =>
      exact codeWP_letValue valueCompiled valueAdapted resultFound step ih
  | callLet valueCompiled valueAdapted resultFound step _ ih =>
      exact codeWP_callLet valueCompiled valueAdapted resultFound step ih
  | externalLet valueCompiled valueAdapted resultFound step _ ih =>
      exact codeWP_externalLet valueCompiled valueAdapted resultFound step ih
  | lazyLet _ valueCompiled valueAdapted resultFound step _ ih =>
      exact codeWP_lazyLet valueCompiled valueAdapted resultFound step ih
  | caseOf _ _ step _ ih =>
      exact codeWP_caseOf step ih
  | effect _ _ step _ ih =>
      exact codeWP_effect step ih

/-- The concrete syntax induction composes every exact source prefix with its
recursive continuation and therefore proves a real finite interpreter run,
including cases, calls, external calls, and both lazy-cache paths. -/
theorem ConcreteCodeSimulation.execEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value}
    {resultKind : AbiKind}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    ExecEvaluates sourceExternals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (ReturnedObservation resultRuntime resultValue) := by
  induction simulation with
  | ret _ _ _ sourceLookup _ _ =>
      exact (CodeEvaluates.ret sourceLookup).execEvaluates sourceExternals
  | letValue _ _ _ step _ ih =>
      exact sourceLetResult_thenExecEvaluates step.1 ih
  | callLet _ _ _ step _ ih =>
      exact sourceCallLetResult_thenExecEvaluates step.1 ih
  | externalLet _ _ _ step _ ih =>
      exact sourceExternalLetResult_thenExecEvaluates step.1 ih
  | lazyLet _ _ _ _ step _ ih =>
      exact sourceLazyLetResult_thenExecEvaluates step.1 ih
  | caseOf _ _ step _ ih =>
      exact sourceCaseResult_thenExecEvaluates step.1 ih
  | effect _ _ step _ ih =>
      exact sourceEffectResult_thenExecEvaluates step.1 ih

/-- Final concrete runtime refinement is not an extra declaration hypothesis:
it is inherited from the return leaf through the syntax induction. -/
theorem ConcreteCodeSimulation.runtimeRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value}
    {resultKind : AbiKind}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    ConcreteRuntimeRel resultStore.host.runtime resultWitness resultRuntime := by
  induction simulation with
  | ret _ _ _ _ stateRelated _ =>
      exact stateRelated.1
  | letValue _ _ _ _ _ ih =>
      exact ih
  | callLet _ _ _ _ _ ih =>
      exact ih
  | externalLet _ _ _ _ _ ih =>
      exact ih
  | lazyLet _ _ _ _ _ _ ih =>
      exact ih
  | caseOf _ _ _ _ ih =>
      exact ih
  | effect _ _ _ _ ih =>
      exact ih

/-- The same return-leaf invariant proves that successful generated execution
does not finish with a structured concrete failure. -/
theorem ConcreteCodeSimulation.failureClear
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value}
    {resultKind : AbiKind}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    resultStore.host.failure? = none := by
  induction simulation with
  | ret _ _ _ _ stateRelated _ =>
      exact stateRelated.2.1
  | letValue _ _ _ _ _ ih =>
      exact ih
  | callLet _ _ _ _ _ ih =>
      exact ih
  | externalLet _ _ _ _ _ ih =>
      exact ih
  | lazyLet _ _ _ _ _ _ ih =>
      exact ih
  | caseOf _ _ _ _ ih =>
      exact ih
  | effect _ _ _ _ ih =>
      exact ih

/-- The physical return lane relation is likewise derived at the return leaf
and transported unchanged through every preceding source step. -/
theorem ConcreteCodeSimulation.valueRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value}
    {resultKind : AbiKind}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    PhysicalValueRel resultWitness resultKind physical resultValue := by
  induction simulation with
  | ret _ resultFound kindAt sourceLookup stateRelated targetLookup =>
      obtain ⟨actual, actualLookup, valueRelated⟩ :=
        stateRelated.resolve sourceLookup resultFound kindAt
      rw [targetLookup] at actualLookup
      injection actualLookup with physicalEq
      subst actual
      exact valueRelated
  | letValue _ _ _ _ _ ih =>
      exact ih
  | callLet _ _ _ _ _ ih =>
      exact ih
  | externalLet _ _ _ _ _ ih =>
      exact ih
  | lazyLet _ _ _ _ _ _ ih =>
      exact ih
  | caseOf _ _ _ _ ih =>
      exact ih
  | effect _ _ _ _ ih =>
      exact ih

/-- T2's initial bridge: the syntax-directed simulation constructs every
field of T1's public successful declaration certificate. -/
theorem ConcreteCodeSimulation.toSuccessfulDeclaration
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction []
        module hostEnv sourceExternals sourceRuntime sourceEnv sourceCode
        targetFunction.body initial
        (targetFunction.toLocals parameters.reverse) initialWitness resultRuntime
        resultValue resultKind resultStore resultWitness physical)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1)
    (notImport : module.imports[functionIndex]? = none)
    (functionFound :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction) :
    SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
      sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
      targetFunction functionIndex initial resultStore initialWitness
      resultWitness parameters resultKind resultValue physical := {
  sourceEvaluates := simulation.execEvaluates
  notImport
  functionFound
  body := ⟨parameterCount, resultCount,
    fun callerTail =>
      simulation.toCodeWP (callerTail := callerTail) parameterCount resultCount⟩
  runtimeRelated := simulation.runtimeRelated
  failureClear := simulation.failureClear
  valueRelated := simulation.valueRelated }

/-- Public source/target correctness for the current concrete simulation
fragment, with no separately supplied final refinement facts. -/
theorem ConcreteCodeSimulation.correct
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial resultStore : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (simulation :
      ConcreteCodeSimulation context sourceModule sourceFunction []
        module hostEnv sourceExternals sourceRuntime sourceEnv sourceCode
        targetFunction.body initial
        (targetFunction.toLocals parameters.reverse) initialWitness resultRuntime
        resultValue resultKind resultStore resultWitness physical)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1)
    (notImport : module.imports[functionIndex]? = none)
    (functionFound :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      Wasm.TerminatesWith hostEnv module functionIndex initial
        (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) :=
  (simulation.toSuccessfulDeclaration parameterCount resultCount notImport
    functionFound).correct callerTail

end FirTalos.Concrete
