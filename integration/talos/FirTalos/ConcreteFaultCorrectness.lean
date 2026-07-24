import FirTalos.ConcreteSupportedExportCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- The canonical source observation for a structured runtime fault. -/
def FaultObservation (runtime : RuntimeState) (fault : RuntimeFault) :
    Observation :=
  { outcome := .fault fault
    heap := runtime.heap
    world := runtime.world
    trace := runtime.trace }

/-- Public structured-fault relation for W6. The final concrete runtime still
refines the complete source runtime at the fault point, and the host failure
must be a concrete-runtime trap whose payload is related to the exact FIR
fault. Wasm ABI-shape failures and target memory/global errors cannot satisfy
this postcondition. -/
def RefinedFaultPost (sourceRuntime : RuntimeState) (fault : RuntimeFault) :
    Wasm.Store Host → String → Prop :=
  fun final _ =>
    ∃ witness failure,
      ConcreteRuntimeRel final.host.runtime witness sourceRuntime ∧
      final.host.failure? = some (.runtime failure.toTrap) ∧
      ConcreteErrorSourceRel witness failure fault

/-- Fuel-free total correctness for a concrete Wasm invocation that traps.
Unlike Talos's success-only `Wasm.TerminatesWith`, this predicate retains the
final store and trap message so a later FIR-specific postcondition can inspect
the structured failure recorded by the concrete host. -/
def ConcreteTrapsWith
    (env : Wasm.HostEnv Host)
    (module : Wasm.Module)
    (functionIndex : Nat)
    (initial : Wasm.Store Host)
    (args : List Wasm.Value)
    (Post : Wasm.Store Host → String → Prop) : Prop :=
  ∃ fuelBound, ∀ fuel ≥ fuelBound, ∃ final message,
    Wasm.run fuel module functionIndex initial args env =
        .Trap final message ∧
      Post final message

/-- Fuel-free concrete target correctness for a trapping function selected by
exported name. -/
def ConcreteExportTrapsWith
    (hostEnv : Wasm.HostEnv Host)
    (module : Wasm.Module)
    (exportName : String)
    (initial : Wasm.Store Host)
    (args : List Wasm.Value)
    (Post : Wasm.Store Host → String → Prop) : Prop :=
  ∃ functionIndex,
    module.findExport exportName = some functionIndex ∧
      ConcreteTrapsWith hostEnv module functionIndex initial args Post

/-- A function-body postcondition that accepts exactly a Wasm trap. All
successful, invalid, exceptional, and fuel-exhausted continuations are
excluded. -/
def ConcreteFunctionFaultPost
    (Post : Wasm.Store Host → String → Prop) :
    Wasm.Assertion Host :=
  fun continuation =>
    match continuation with
    | .Trap final message => Post final message
    | _ => False

/-- Store-specific bridge from a body WP to the fuel-free concrete trap
predicate. The function must be an in-module definition; imported calls have
a separate host-contract boundary. -/
theorem concreteTrapsWith_of_wp_body_at
    {env : Wasm.HostEnv Host} {module : Wasm.Module}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {Post : Wasm.Store Host → String → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (bodyWP :
      Wasm.wp module function.body
        (ConcreteFunctionFaultPost Post) initial
        (function.toLocals (args.take function.numParams).reverse) env) :
    ConcreteTrapsWith env module functionIndex initial args Post := by
  unfold Wasm.wp at bodyWP
  rcases bodyWP with ⟨fuelBound, bodyWP⟩
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  have bodyPost := bodyWP fuel enoughFuel
  rw [Wasm.run_eq notImport]
  simp only [found]
  cases execution : Wasm.exec fuel module initial
      (function.toLocals (args.take function.numParams).reverse)
      function.body env with
  | Fallthrough final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Return final values =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Break level final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Trap final message =>
      rw [execution] at bodyPost
      exact ⟨final, message, rfl, bodyPost⟩
  | Invalid message =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | OutOfFuel =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | ReturnCall callee final values =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Throwing tag values final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim

/-- A concrete compiler body proof with a trap-only postcondition supplies
the public fuel-free trap theorem at the generated function index. -/
theorem CodeWP.toConcreteTrapsWith
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {initial : Wasm.Store Host}
    {args : List Wasm.Value}
    {witness : Fir.Wasm.Concrete.RefinementWitness}
    {Post : Wasm.Store Host → String → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) witness []
        (ConcreteFunctionFaultPost Post)) :
    ConcreteTrapsWith hostEnv module functionIndex initial args Post := by
  apply concreteTrapsWith_of_wp_body_at notImport found
  simpa [Wasm.Function.toLocals] using correct.2.2

/-- One terminal failing source fragment paired with its compiler-adapted,
trap-only concrete body proof. Operation-specific fault theorems construct
this leaf; the recursive certificate below transports it through every
successful prefix admitted by T2. -/
def ConcreteFaultLeaf
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : LCNF.Code .impure)
    (target : Wasm.Program)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness : RefinementWitness)
    (faultRuntime : RuntimeState)
    (fault : RuntimeFault) : Prop :=
  ExecEvaluates sourceExternals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (FaultObservation faultRuntime fault) ∧
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv sourceCode target targetStore targetLocals witness
      [] (ConcreteFunctionFaultPost (RefinedFaultPost faultRuntime fault))

/-- Syntax-directed T4 certificate. A terminal operation-specific fault leaf
is transported backwards through successful direct lets, calls, external
calls, lazy-cache paths, selected cases, and no-result effects. Thus the
source and target must fail at the same dynamic point after the same
successfully simulated prefix. -/
inductive ConcreteFaultSimulation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl) :
    RuntimeState → Env → LCNF.Code .impure → Wasm.Program →
      Wasm.Store Host → Wasm.Locals → RefinementWitness →
      RuntimeState → RuntimeFault → Prop where
  | terminal
      (leaf :
        ConcreteFaultLeaf context sourceModule sourceFunction labels module
          hostEnv sourceExternals sourceRuntime sourceEnv sourceCode targetCode
          targetStore targetLocals witness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode targetCode
        targetStore targetLocals witness faultRuntime fault
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
        ConcreteFaultSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness faultRuntime fault
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
        ConcreteFaultSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness faultRuntime fault
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
        ConcreteFaultSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness faultRuntime fault
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
        ConcreteFaultSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness faultRuntime fault
  | caseOf
      (target selectedTarget : Wasm.Program)
      (step :
        ConcreteCasesStepSimulates context sourceModule sourceFunction labels
          module hostEnv sourceRuntime sourceEnv cases selected target
          selectedTarget targetStore targetLocals witness)
      (continued :
        ConcreteFaultSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals sourceRuntime sourceEnv selected
          selectedTarget targetStore targetLocals witness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv (.cases cases) target
        targetStore targetLocals witness faultRuntime fault
  | effect
      (target targetRest : Wasm.Program)
      (step :
        EffectStepSimulates context sourceModule sourceFunction labels module
          hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
          targetRest targetStore nextStore targetLocals witness nextWitness)
      (continued :
        ConcreteFaultSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextRuntime sourceEnv continuation
          targetRest nextStore targetLocals nextWitness faultRuntime fault) :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv code target targetStore
        targetLocals witness faultRuntime fault

/-- The T4 syntax induction constructs the exact trap-only concrete body
judgment from its terminal failure leaf. -/
theorem ConcreteFaultSimulation.toCodeWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {fault : RuntimeFault}
    (simulation :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target
        targetStore targetLocals witness faultRuntime fault) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv sourceCode target targetStore targetLocals witness
      [] (ConcreteFunctionFaultPost
        (RefinedFaultPost faultRuntime fault)) := by
  induction simulation with
  | terminal leaf =>
      exact leaf.2
  | letValue valueCompiled valueAdapted resultFound step _ ih =>
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

/-- The same T4 induction composes the exact finite source prefixes with the
terminal fault execution. -/
theorem ConcreteFaultSimulation.execEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {target : Wasm.Program}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {fault : RuntimeFault}
    (simulation :
      ConcreteFaultSimulation context sourceModule sourceFunction labels module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target
        targetStore targetLocals witness faultRuntime fault) :
    ExecEvaluates sourceExternals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (FaultObservation faultRuntime fault) := by
  induction simulation with
  | terminal leaf =>
      exact leaf.1
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

/-- Function-index form of T4 for the complete syntax certificate. -/
theorem ConcreteFaultSimulation.correct
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {fault : RuntimeFault}
    (simulation :
      ConcreteFaultSimulation context sourceModule sourceFunction [] module
        hostEnv sourceExternals sourceRuntime sourceEnv sourceCode
        targetFunction.body initial
        (targetFunction.toLocals parameters.reverse) initialWitness
        faultRuntime fault)
    (parameterCount : parameters.length = targetFunction.numParams)
    (notImport : module.imports[functionIndex]? = none)
    (functionFound :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (FaultObservation faultRuntime fault) ∧
      ConcreteTrapsWith hostEnv module functionIndex initial
        (parameters ++ callerTail) (RefinedFaultPost faultRuntime fault) := by
  have parameterPrefix :
      (parameters ++ callerTail).take targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  refine ⟨simulation.execEvaluates, ?_⟩
  apply CodeWP.toConcreteTrapsWith notImport functionFound
  simpa [parameterPrefix] using simulation.toCodeWP

/-- An operation-level related concrete error produces exactly the public
structured-fault postcondition when the concrete host traps. -/
theorem refinedFaultPost_of_runtimeFailure
    {initial : Wasm.Store Host}
    {sourceRuntime : RuntimeState}
    {witness : RefinementWitness}
    {failure : ConcreteError}
    {fault : RuntimeFault}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness sourceRuntime)
    (failureRelated : ConcreteErrorSourceRel witness failure fault) :
    ∃ final message,
      trap (clearFailure initial) (.runtime failure.toTrap) =
          .Trap final message ∧
        RefinedFaultPost sourceRuntime fault final message := by
  unfold trap
  refine ⟨_, _, rfl, witness, failure, ?_, rfl, failureRelated⟩
  simpa [clearFailure] using runtimeRelated

/-- Export-level T4 shell. A syntax-directed body proof supplies the exact
generated function selected by the static export certificate. -/
theorem ConcreteSupportedExport.trapsWith
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {fault : RuntimeFault}
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (body :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness []
        (ConcreteFunctionFaultPost
          (RefinedFaultPost faultRuntime fault))) :
    ConcreteExportTrapsWith hosts.env target.wasmModule exportName initial
      (parameters ++ callerTail) (RefinedFaultPost faultRuntime fault) := by
  have parameterPrefix :
      (parameters ++ callerTail).take spec.targetFunction.numParams =
        parameters := by
    rw [← parameterCount]
    simp
  refine ⟨spec.targetFunctionIndex, spec.exported, ?_⟩
  apply CodeWP.toConcreteTrapsWith spec.notImport spec.targetFunctionFound
  simpa [parameterPrefix] using body

/-- Public T4 consequence once a syntax-directed fault certificate has
constructed both the finite source execution and trap-only concrete body WP.
The target conclusion is selected by generated export name and retains the
related structured failure. -/
theorem ConcreteSupportedExport.faultCorrect
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceExternals : ExternalImpl}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {fault : RuntimeFault}
    (sourceEvaluates :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (FaultObservation faultRuntime fault))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams)
    (body :
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
        sourceRuntime sourceEnv sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness []
        (ConcreteFunctionFaultPost
          (RefinedFaultPost faultRuntime fault))) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (FaultObservation faultRuntime fault) ∧
      ConcreteExportTrapsWith hosts.env target.wasmModule exportName initial
        (parameters ++ callerTail) (RefinedFaultPost faultRuntime fault) :=
  ⟨sourceEvaluates, spec.trapsWith parameterCount body⟩

/-- T4 whole-export correctness constructed entirely by the syntax-directed
fault simulation. No separately supplied source execution or target body
judgment remains in the public theorem. -/
theorem ConcreteSupportedExport.faultCorrectOfSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {fault : RuntimeFault}
    (simulation :
      ConcreteFaultSimulation context sourceModule sourceFunction []
        target.wasmModule hosts.env sourceExternals sourceRuntime sourceEnv
        sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        faultRuntime fault)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (FaultObservation faultRuntime fault) ∧
      ConcreteExportTrapsWith hosts.env target.wasmModule exportName initial
        (parameters ++ callerTail) (RefinedFaultPost faultRuntime fault) :=
  spec.faultCorrect simulation.execEvaluates parameterCount simulation.toCodeWP

end FirTalos.Concrete
