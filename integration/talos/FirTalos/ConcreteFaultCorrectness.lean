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

end FirTalos.Concrete
