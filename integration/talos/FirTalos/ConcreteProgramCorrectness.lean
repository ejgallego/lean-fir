import FirTalos.ConcreteDeclarationCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

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

/-- Syntax-directed W6 certificate for the first concrete program fragment.
Unlike `SuccessfulDeclaration`, this certificate derives its final
runtime/value facts from the return leaf and threads them backwards through
each concrete step. Further constructors can consume the already-defined call,
external, lazy, and case step predicates without changing the result indices. -/
inductive ConcreteCodeSimulation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) :
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
        hostEnv sourceRuntime sourceEnv (.return result)
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
          module hostEnv nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultRuntime resultValue resultKind
          resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
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
          module hostEnv nextRuntime sourceEnv continuation targetRest nextStore
          targetLocals nextWitness resultRuntime resultValue resultKind
          resultStore resultWitness physical) :
      ConcreteCodeSimulation context sourceModule sourceFunction labels module
        hostEnv sourceRuntime sourceEnv code target targetStore targetLocals
        witness resultRuntime resultValue resultKind resultStore resultWitness
        physical

/-- The concrete syntax induction constructs the exact compiler/adaptor body
judgment for every caller operand remainder. -/
theorem ConcreteCodeSimulation.toCodeWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
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
        hostEnv sourceRuntime sourceEnv sourceCode target targetStore
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
  | effect _ _ step _ ih =>
      exact codeWP_effect step ih

/-- The same concrete syntax induction proves successful source big-step
evaluation for the return/direct-let/effect spine. -/
theorem ConcreteCodeSimulation.sourceEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
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
        hostEnv sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    CodeEvaluates context sourceRuntime sourceEnv sourceCode resultRuntime
      resultValue := by
  induction simulation with
  | ret _ _ _ sourceLookup _ _ =>
      exact .ret sourceLookup
  | letValue _ _ _ step _ ih =>
      exact .letValue step.1 ih
  | effect _ _ step _ ih =>
      exact .effect step.1 ih

/-- In particular, the source certificate runs in FIR's executable
interpreter for any installed external implementation; the current fragment
contains no external source step. -/
theorem ConcreteCodeSimulation.execEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
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
        hostEnv sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical)
    (externals : ExternalImpl) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (ReturnedObservation resultRuntime resultValue) :=
  simulation.sourceEvaluates.execEvaluates externals

/-- Final concrete runtime refinement is not an extra declaration hypothesis:
it is inherited from the return leaf through the syntax induction. -/
theorem ConcreteCodeSimulation.runtimeRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
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
        hostEnv sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    ConcreteRuntimeRel resultStore.host.runtime resultWitness resultRuntime := by
  induction simulation with
  | ret _ _ _ _ stateRelated _ =>
      exact stateRelated.1
  | letValue _ _ _ _ _ ih =>
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
        hostEnv sourceRuntime sourceEnv sourceCode target targetStore
        targetLocals witness resultRuntime resultValue resultKind resultStore
        resultWitness physical) :
    resultStore.host.failure? = none := by
  induction simulation with
  | ret _ _ _ _ stateRelated _ =>
      exact stateRelated.2.1
  | letValue _ _ _ _ _ ih =>
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
        hostEnv sourceRuntime sourceEnv sourceCode target targetStore
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
        module hostEnv sourceRuntime sourceEnv sourceCode targetFunction.body
        initial (targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
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
  sourceEvaluates := simulation.execEvaluates sourceExternals
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
        module hostEnv sourceRuntime sourceEnv sourceCode targetFunction.body
        initial (targetFunction.toLocals parameters.reverse) initialWitness
        resultRuntime resultValue resultKind resultStore resultWitness physical)
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
