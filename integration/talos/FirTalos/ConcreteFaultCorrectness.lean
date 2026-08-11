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

/-- Generic exact-contract lifting for a concrete host trap. A trap aborts the
remaining instruction sequence, so the only continuation obligation is the
trap postcondition itself. -/
theorem wp_exact_host_call_of_trap
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {spec : Wasm.HostSpec host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store host → List Wasm.Value → Wasm.HostResult host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {initial final : Wasm.Store host} {locals : Wasm.Locals}
    {physicalArgs : List Wasm.Value} {message : String}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hArgs :
      (locals.values.take imp.params.length).reverse = physicalArgs)
    (operation : step initial physicalArgs = .Trap final message)
    (post : Q (.Trap final message)) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply Wasm.wp_call_host_contract hImp hSat hi hContract
  · intro actualResults actualFinal contract
    change Wasm.HostResult.Return actualResults actualFinal =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    contradiction
  · intro actualFinal actualMessage contract
    change Wasm.HostResult.Trap actualFinal actualMessage =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    injection contract with finalEq messageEq
    subst actualFinal
    subst actualMessage
    exact post
  · intro actualFinal tag arguments contract
    change Wasm.HostResult.Throw actualFinal tag arguments =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    contradiction

/-- A direct source `let` error is already a complete finite execution: the
initial machine state takes no successful prefix steps and its next
interpreter step produces the canonical fault observation. -/
theorem sourceLetFault_execEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {fault : RuntimeFault}
    (evaluated :
      evalLetValue
        (sourceCodeState context sourceRuntime sourceEnv
          (.let decl continuation)) decl = .error fault) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv
        (.let decl continuation))
      (FaultObservation sourceRuntime fault) := by
  refine ⟨0, _, .refl _, ?_⟩
  have evaluated' :
      evalLetValue {
        program := context.program
        control := .code (.let decl continuation)
        env := sourceEnv
        runtime := sourceRuntime } decl = .error fault := by
    simpa [sourceCodeState] using evaluated
  simp [executeStep, coreStep, sourceCodeState, evaluated', fail, observe,
    FaultObservation]

/-- Any source fragment whose very next interpreter step is a fault already
has the finite execution witness required by a terminal T4 leaf. -/
theorem sourceCodeFault_execEvaluates
    {context : Fir.Wasm.Context}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {code : LCNF.Code .impure}
    {fault : RuntimeFault}
    (failed :
      executeStep externals
          (sourceCodeState context sourceRuntime sourceEnv code) =
        .done (FaultObservation sourceRuntime fault)) :
    ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code)
      (FaultObservation sourceRuntime fault) :=
  ⟨0, _, .refl _, failed⟩

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

/-- Trap counterpart of the common no-result effect prefix. Source-order
locals are pushed in Wasm stack order, consumed by the exact-contract host
call, and the trap discards the continuation and caller tail. -/
theorem wp_effect_localGets_of_trap
    {host : Type}
    {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {spec : Wasm.HostSpec host}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {step : Wasm.Store host → List Wasm.Value → Wasm.HostResult host}
    {rest : Wasm.Program}
    {Q : Wasm.Assertion host}
    {initial final : Wasm.Store host}
    {locals : Wasm.Locals}
    {indices : List Nat}
    {physicalArgs tail : List Wasm.Value}
    {message : String}
    (hGets :
      List.Forall₂ (fun index value => locals.get index = some value)
        indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (fun initial args result => result = step initial args))
    (hParams : imp.params.length = physicalArgs.length)
    (operation : step initial physicalArgs = .Trap final message)
    (post : Q (.Trap final message)) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++ .call id :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_trap
    (physicalArgs := physicalArgs) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · exact post

/-- A concrete external implementation's exact source failure is preserved
by the resolved Talos host. Argument decoding has already succeeded, so the
foreign implementation is the operation that establishes the trap payload. -/
theorem externalStep_sourceFailure
    (operation : ExternalOperation) (resultKind : AbiKind)
    (initial : Wasm.Store Host) (physicalArgs : List Wasm.Value)
    (concreteArgs : List LaneValue) (fault : RuntimeFault)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (concreteCalled : initial.host.externals.call
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      initial.host.runtime = .error (.source fault)) :
    externalStep operation resultKind initial physicalArgs =
      trap (clearFailure initial)
        (.runtime ((.source fault : ConcreteError).toTrap)) := by
  simp [externalStep, decoded, ConcreteExternalImpl.invoke, concreteCalled]

/-- Terminal T4 leaf for an arbitrary-arity generated external call whose
concrete and source implementations report the same source fault. The trap
preempts the generated result-local write and the entire continuation. -/
theorem concreteFaultLeaf_external_sourceFailure
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {code : LCNF.Code .impure}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {indices : List Nat}
    {physicalArgs : List Wasm.Value}
    {concreteArgs : List LaneValue}
    {resultIndex : Nat}
    {targetRest : Wasm.Program}
    {fault : RuntimeFault}
    (operation : ExternalOperation)
    (resultKind : AbiKind)
    (sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv code)
        (FaultObservation sourceRuntime fault))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code
        (indices.map Wasm.Instruction.localGet ++
          .call id :: .localSet resultIndex :: targetRest))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? =
      some (externalContract operation resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (decoded : decodePhysicalLanes 0 operation.signature.params.toList
      physicalArgs = .ok concreteArgs)
    (concreteCalled : initial.host.externals.call
      (concreteExternalRequest operation resultKind concreteArgs.toArray)
      initial.host.runtime = .error (.source fault)) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv code
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime fault := by
  have operationStep :=
    externalStep_sourceFailure operation resultKind initial physicalArgs
      concreteArgs fault decoded concreteCalled
  obtain ⟨final, message, trapped, post⟩ :=
    refinedFaultPost_of_runtimeFailure initialRelated.1
      (ConcreteErrorSourceRel.source fault)
  refine ⟨sourceFault, adapted, initialRelated, ?_⟩
  simpa using wp_effect_localGets_of_trap
    (step := externalStep operation resultKind)
    (rest := .localSet resultIndex :: targetRest)
    (indices := indices) (physicalArgs := physicalArgs) (tail := [])
    hGets hImp hSat hi hContract hParams (operationStep.trans trapped)
    (by simpa [ConcreteFunctionFaultPost] using post)

/-- Generic terminal T4 leaf for an arbitrary-arity, result-producing host
call whose argument prefix consists of generated local loads. The host trap
preempts the result-local write and continuation. -/
theorem concreteFaultLeaf_hostLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {code : LCNF.Code .impure}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {indices : List Nat}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {targetRest : Wasm.Program}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {failure : ConcreteError}
    {fault : RuntimeFault}
    (sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv code)
        (FaultObservation sourceRuntime fault))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code
        (indices.map Wasm.Instruction.localGet ++
          .call id :: .localSet resultIndex :: targetRest))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hParams : imp.params.length = physicalArgs.length)
    (operation :
      step initial physicalArgs =
        trap (clearFailure initial) (.runtime failure.toTrap))
    (failureRelated : ConcreteErrorSourceRel witness failure fault) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv code
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨final, message, trapped, post⟩ :=
    refinedFaultPost_of_runtimeFailure initialRelated.1 failureRelated
  refine ⟨sourceFault, adapted, initialRelated, ?_⟩
  simpa using wp_effect_localGets_of_trap
    (step := step)
    (rest := .localSet resultIndex :: targetRest)
    (indices := indices) (physicalArgs := physicalArgs) (tail := [])
    hGets hImp hSat hi hContract hParams (operation.trans trapped)
    (by simpa [ConcreteFunctionFaultPost] using post)

/-- Generic terminal T4 leaf for a unary, result-producing concrete host
operation. It centralizes compiler/adaptor composition and Talos trap
propagation; operation-specific leaves supply only the source error, concrete
trap equation, and exact source-failure relation. -/
theorem concreteFaultLeaf_unaryHostLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {operandIndex resultIndex : Nat}
    {physical : Wasm.Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetRest : Wasm.Program}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {failure : ConcreteError}
    {fault : RuntimeFault}
    (evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error fault)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok [.localGet operandIndex, .call id])
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hOperand : locals.get operandIndex = some physical)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hParams : imp.params.length = 1)
    (operation :
      step initial [physical] =
        trap (clearFailure initial) (.runtime failure.toTrap))
    (failureRelated : ConcreteErrorSourceRel witness failure fault) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet operandIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨final, message, trapped, post⟩ :=
    refinedFaultPost_of_runtimeFailure initialRelated.1 failureRelated
  constructor
  · exact sourceLetFault_execEvaluates evaluated
  · refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
        continuationAdapted, initialRelated, ?_⟩
    have hOperandTail :
        ({ locals with values := [] } : Wasm.Locals).get operandIndex =
          some physical := by
      simpa [Wasm.Locals.get] using hOperand
    rw [Wasm.wp_localGet_cons, hOperandTail]
    apply wp_exact_host_call_of_trap
      (step := step) (physicalArgs := [physical])
      hImp hSat hi hContract
    · simp [hParams]
    · exact operation.trans trapped
    · simpa [ConcreteFunctionFaultPost] using post

/-- Generic terminal T4 leaf for a binary no-result concrete host effect.
Unlike the successful effect rule, no post-state or continuation simulation is
needed: an exact related host trap terminates both generated control flow and
the source execution at the current effect. -/
theorem concreteFaultLeaf_binaryHostEffect
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {code : LCNF.Code .impure}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {firstIndex secondIndex : Nat}
    {physicalFirst physicalSecond : Wasm.Value}
    {targetRest : Wasm.Program}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {failure : ConcreteError}
    {fault : RuntimeFault}
    (sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv code)
        (FaultObservation sourceRuntime fault))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code
        ([.localGet firstIndex, .localGet secondIndex, .call id] ++ targetRest))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hFirst : locals.get firstIndex = some physicalFirst)
    (hSecond : locals.get secondIndex = some physicalSecond)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (fun initial args result => result = step initial args))
    (hParams : imp.params.length = 2)
    (operation :
      step initial [physicalFirst, physicalSecond] =
        trap (clearFailure initial) (.runtime failure.toTrap))
    (failureRelated : ConcreteErrorSourceRel witness failure fault) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv code
      ([.localGet firstIndex, .localGet secondIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨final, message, trapped, post⟩ :=
    refinedFaultPost_of_runtimeFailure initialRelated.1 failureRelated
  refine ⟨sourceFault, adapted, initialRelated, ?_⟩
  simpa using wp_effect_localGets_of_trap
    (indices := [firstIndex, secondIndex])
    (physicalArgs := [physicalFirst, physicalSecond])
    (tail := [])
    (.cons hFirst (.cons hSecond .nil)) hImp hSat hi hContract hParams
    (operation.trans trapped)
    (by simpa [ConcreteFunctionFaultPost] using post)

/-- Unary specialization of the no-result fault boundary used by tag mutation,
reference counting, and explicit deletion. -/
theorem concreteFaultLeaf_unaryHostEffect
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {code : LCNF.Code .impure}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {operandIndex : Nat}
    {physical : Wasm.Value}
    {targetRest : Wasm.Program}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {failure : ConcreteError}
    {fault : RuntimeFault}
    (sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv code)
        (FaultObservation sourceRuntime fault))
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code
        ([.localGet operandIndex, .call id] ++ targetRest))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hOperand : locals.get operandIndex = some physical)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (fun initial args result => result = step initial args))
    (hParams : imp.params.length = 1)
    (operation :
      step initial [physical] =
        trap (clearFailure initial) (.runtime failure.toTrap))
    (failureRelated : ConcreteErrorSourceRel witness failure fault) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv code
      ([.localGet operandIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨final, message, trapped, post⟩ :=
    refinedFaultPost_of_runtimeFailure initialRelated.1 failureRelated
  refine ⟨sourceFault, adapted, initialRelated, ?_⟩
  simpa using wp_effect_localGets_of_trap
    (indices := [operandIndex]) (physicalArgs := [physical]) (tail := [])
    (.cons hOperand .nil) hImp hSat hi hContract hParams
    (operation.trans trapped)
    (by simpa [ConcreteFunctionFaultPost] using post)

/-- First terminal T4 leaf: a stale object passed to generated `isShared`.
The source fault names its semantic heap location, while the concrete host
records the related wasm32 address. -/
theorem concreteFaultLeaf_isShared_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .isShared objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime .isShared)])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime .isShared) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? = some isSharedContract)
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    isSharedStep_deadObject_of_refines initialRelated.1 objectRelated found dead
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime .isShared)] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.deadObject location) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        isShared sourceRuntime (.object (.heap location))) =
      .error (.deadObject location)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := isSharedStep)
    (failure := .sourceAddress (.deadObject objectWord))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- An object projection past the declared constructor field count becomes the
same FIR bounds fault in the generated concrete body. -/
theorem concreteFaultLeaf_objectProjection_outOfBounds
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex index : Nat}
    {objectWord : Word32}
    {sourceObject : Value}
    {resultKind : AbiKind}
    {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .oproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.objectProj index resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.objectProj index resultKind)) =
        some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor :
      witness.descriptors.lookup? objectWord =
        some (.constructor info fieldKinds))
    (projected :
      getObjectField sourceRuntime sourceObject index =
        .error (.objectFieldOutOfBounds index info.size))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime
      (.objectFieldOutOfBounds index info.size) := by
  have operation :=
    objectProjStep_outOfBounds_of_refines initialRelated.1 objectRelated
      descriptor projected
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.objectProj index resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.objectFieldOutOfBounds index info.size) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getObjectField sourceRuntime sourceObject index) =
      .error (.objectFieldOutOfBounds index info.size)
    rw [projected]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := objectProjStep index)
    (failure := .source (.objectFieldOutOfBounds index info.size))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    (.source (.objectFieldOutOfBounds index info.size))

/-- Object projection checks liveness before bounds or payload access, so a
stale operand preserves the exact address/location dead-object relation. -/
theorem concreteFaultLeaf_objectProjection_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex index : Nat}
    {objectWord : Word32}
    {resultKind : AbiKind}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .oproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.objectProj index resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.objectProj index resultKind)) =
        some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    objectProjStep_deadObject_of_refines index initialRelated.1 objectRelated
      found dead
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.objectProj index resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.deadObject location) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getObjectField sourceRuntime (.object (.heap location)) index) =
      .error (.deadObject location)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := objectProjStep index)
    (failure := .sourceAddress (.deadObject objectWord))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- A `USize` projection past the combined object/`USize` slot count retains
the exact FIR bounds payload. -/
theorem concreteFaultLeaf_usizeProjection_outOfBounds
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex index : Nat}
    {objectWord : Word32}
    {sourceObject : Value}
    {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .uproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.usizeProj index))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.usizeProj index)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor :
      witness.descriptors.lookup? objectWord =
        some (.constructor info fieldKinds))
    (projected :
      getUSizeSlot sourceRuntime sourceObject index =
        .error (.usizeFieldOutOfBounds index (info.size + info.usize)))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime
      (.usizeFieldOutOfBounds index (info.size + info.usize)) := by
  have operation :=
    usizeProjStep_outOfBounds_of_refines initialRelated.1 objectRelated
      descriptor projected
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.usizeProj index))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.usizeFieldOutOfBounds index
          (info.size + info.usize)) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getUSizeSlot sourceRuntime sourceObject index) =
      .error (.usizeFieldOutOfBounds index (info.size + info.usize))
    rw [projected]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := usizeProjStep index)
    (failure := .source
      (.usizeFieldOutOfBounds index (info.size + info.usize)))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    (.source (.usizeFieldOutOfBounds index (info.size + info.usize)))

/-- A stale `USize` projection faults at the common liveness gate before slot
bounds are inspected. -/
theorem concreteFaultLeaf_usizeProjection_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex index : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .uproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.usizeProj index))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.usizeProj index)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    usizeProjStep_deadObject_of_refines index initialRelated.1 objectRelated
      found dead
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.usizeProj index))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.deadObject location) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getUSizeSlot sourceRuntime (.object (.heap location)) index) =
      .error (.deadObject location)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := usizeProjStep index)
    (failure := .sourceAddress (.deadObject objectWord))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- A stale packed-scalar projection faults at the common liveness gate before
its width, offset, or scalar result kind can affect the outcome. -/
theorem concreteFaultLeaf_scalarProjection_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex width offset : Nat}
    {resultKind : AbiKind}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .sproj width offset objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.scalarProj width offset resultKind)) =
        some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (supported :
      resultKind = .uint8 ∨ resultKind = .uint16 ∨
        resultKind = .uint32 ∨ resultKind = .uint64)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (scalarProjContract width offset resultKind))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    scalarProjStep_deadObject_of_refines width offset resultKind supported
      initialRelated.1 objectRelated found dead
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.deadObject location) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getScalarField sourceRuntime (.object (.heap location)) width offset) =
      .error (.deadObject location)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := scalarProjStep width offset resultKind)
    (failure := .sourceAddress (.deadObject objectWord))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- A nonconstructor object projection stops at the common constructor gate
and preserves the exact source-classified `expectedConstructor` fault. -/
theorem concreteFaultLeaf_objectProjection_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex index : Nat}
    {objectWord : Word32}
    {sourceObject : Value}
    {resultKind : AbiKind}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .oproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.objectProj index resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.objectProj index resultKind)) =
        some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (constructorFailed :
      getConstructor sourceRuntime sourceObject =
        .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    objectProjStep_expectedConstructor_of_refines index initialRelated.1
      objectRelated constructorFailed
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.objectProj index resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error .expectedConstructor := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getObjectField sourceRuntime sourceObject index) =
      .error .expectedConstructor
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := objectProjStep index)
    (failure := .source .expectedConstructor)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- `USize` projection preserves `expectedConstructor` before translating its
absolute fixed-slot coordinate. -/
theorem concreteFaultLeaf_usizeProjection_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex index : Nat}
    {objectWord : Word32}
    {sourceObject : Value}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .uproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.usizeProj index))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.usizeProj index)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (constructorFailed :
      getConstructor sourceRuntime sourceObject =
        .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    usizeProjStep_expectedConstructor_of_refines index initialRelated.1
      objectRelated constructorFailed
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.usizeProj index))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error .expectedConstructor := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getUSizeSlot sourceRuntime sourceObject index) =
      .error .expectedConstructor
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := usizeProjStep index)
    (failure := .source .expectedConstructor)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- Packed-scalar projection also preserves `expectedConstructor` at the
shared header gate, independently of the supported scalar width. -/
theorem concreteFaultLeaf_scalarProjection_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex width offset : Nat}
    {resultKind : AbiKind}
    {objectWord : Word32}
    {sourceObject : Value}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .sproj width offset objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.scalarProj width offset resultKind)) =
        some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (constructorFailed :
      getConstructor sourceRuntime sourceObject =
        .error .expectedConstructor)
    (supported :
      resultKind = .uint8 ∨ resultKind = .uint16 ∨
        resultKind = .uint32 ∨ resultKind = .uint64)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (scalarProjContract width offset resultKind))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    scalarProjStep_expectedConstructor_of_refines width offset resultKind
      supported initialRelated.1 objectRelated constructorFailed
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error .expectedConstructor := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        getScalarField sourceRuntime sourceObject width offset) =
      .error .expectedConstructor
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := scalarProjStep width offset resultKind)
    (failure := .source .expectedConstructor)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- Typed unboxing of a stale mapped object faults at the generated unary host
call before the destination local is written or the continuation begins. -/
theorem concreteFaultLeaf_unbox_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {kind : BoxedScalarKind}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .unbox objectId)
    (resultTypeEq : decl.type = kind.semanticType)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.unbox kind.abiKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.unbox kind.abiKind)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (unboxContract kind))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    unboxStep_deadObject_of_refines kind initialRelated.1 objectRelated found
      dead
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.unbox kind.abiKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.deadObject location) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    rw [resultTypeEq]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        unbox sourceRuntime kind.semanticType (.object (.heap location))) =
      .error (.deadObject location)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := unboxStep kind)
    (failure := .sourceAddress (.deadObject objectWord))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- Typed unboxing of a related live non-box object preserves the exact
`expectedScalar` fault through the compiler/adaptor prefix and concrete host;
the destination-local write and continuation remain unreachable. -/
theorem concreteFaultLeaf_unbox_expectedScalar
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {kind : BoxedScalarKind}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {sourceObject : Value}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .unbox objectId)
    (resultTypeEq : decl.type = kind.semanticType)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.unbox kind.abiKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.unbox kind.abiKind)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (unboxFailed :
      unbox sourceRuntime kind.semanticType sourceObject =
        .error .expectedScalar)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (unboxContract kind))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime .expectedScalar := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    unboxStep_expectedScalar_of_refines kind initialRelated.1 objectRelated
      unboxFailed
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.unbox kind.abiKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error .expectedScalar := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    rw [resultTypeEq]
    change ((fun value : Value =>
      (sourceRuntime, LetAction.value value)) <$>
        unbox sourceRuntime kind.semanticType sourceObject) =
      .error .expectedScalar
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := unboxStep kind)
    (failure := .source .expectedScalar)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- Reset of a stale mapped object traps before producing its reuse token,
writing the destination local, or entering the continuation. -/
theorem concreteFaultLeaf_reset_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {count : Nat}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reset count objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.reset count))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.reset count)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    resetStep_deadObject_of_refines count initialRelated.1 objectRelated found
      dead
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.reset count))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error (.deadObject location) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change (do
      let (runtime, token) ←
        reset sourceRuntime count (.object (.heap location))
      return (runtime, LetAction.value token)) =
      .error (.deadObject location)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := resetStep count)
    (failure := .sourceAddress (.deadObject objectWord))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- A live, ordinary, uniquely owned nonconstructor traps at reset's
constructor-kind gate before bounds, child release, result-local write, or the
continuation. -/
theorem concreteFaultLeaf_reset_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {count : Nat}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reset count objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.reset count))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.reset count)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (unique : cell.rc = 1)
    (notConstructor : ∀ object, cell.object ≠ .ctor object)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    resetStep_expectedConstructor_of_refines count initialRelated.1
      objectRelated found live ordinary unique notConstructor
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.reset count))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error .expectedConstructor := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change (do
      let (runtime, token) ←
        reset sourceRuntime count (.object (.heap location))
      return (runtime, LetAction.value token)) =
      .error .expectedConstructor
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := resetStep count)
    (failure := .source .expectedConstructor)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- An oversized reset prefix on a live, ordinary, uniquely owned constructor
preserves the exact bounds fault before field clearing, child release,
destination-local write, or continuation. -/
theorem concreteFaultLeaf_reset_outOfBounds
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {count : Nat}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {object : ConstructorObject}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reset count objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.reset count))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.reset count)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (unique : cell.rc = 1)
    (constructor : cell.object = .ctor object)
    (outOfBounds : object.objectFields.size < count)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime
        (.objectFieldOutOfBounds count object.objectFields.size) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    resetStep_outOfBounds_of_refines count initialRelated.1 objectRelated found
      live ordinary unique constructor outOfBounds
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.reset count))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error
          (.objectFieldOutOfBounds count object.objectFields.size) := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change (do
      let (runtime, token) ←
        reset sourceRuntime count (.object (.heap location))
      return (runtime, LetAction.value token)) =
      .error (.objectFieldOutOfBounds count object.objectFields.size)
    rw [semantic]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := resetStep count)
    (failure :=
      .source (.objectFieldOutOfBounds count object.objectFields.size))
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- A generated reset whose unique constructor fails while releasing a mapped
child traps at that exact child fault before writing its token local or
entering the continuation. -/
theorem concreteFaultLeaf_reset_unique_fault
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {count : Nat}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {object : ConstructorObject}
    {fault : RuntimeFault}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reset count objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.reset count))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.reset count)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (unique : cell.rc = 1)
    (constructor : cell.object = .ctor object)
    (countFits : count ≤ object.objectFields.size)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticFailure :
      reset sourceRuntime count (.object (.heap location)) = .error fault)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨failure, operation, failureRelated⟩ :=
    resetStep_unique_fault_of_refines initialRelated.1 objectRelated
      descriptorsEq found live ordinary unique constructor countFits notFuel
      semanticFailure
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.reset count))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error fault := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change (do
      let (runtime, token) ←
        reset sourceRuntime count (.object (.heap location))
      return (runtime, LetAction.value token)) =
      .error fault
    rw [semanticFailure]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := resetStep count)
    (failure := failure)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- A generated nonunique reset preserves the exact fault from its delegated
checked decrement and cannot write the empty token or enter the continuation
after that failure. -/
theorem concreteFaultLeaf_reset_nonunique_fault
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {count : Nat}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex resultIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {fault : RuntimeFault}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reset count objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.reset count))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.reset count)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (sourceLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (notUnique : cell.rc ≠ 1)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticFailure :
      reset sourceRuntime count (.object (.heap location)) = .error fault)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (resetContract count))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨failure, operation, failureRelated⟩ :=
    resetStep_nonunique_fault_of_refines initialRelated.1 objectRelated
      descriptorsEq found live notUnique notFuel semanticFailure
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.reset count))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            objectId =
          some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error fault := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState, lookupValue, sourceLookup]
    change (do
      let (runtime, token) ←
        reset sourceRuntime count (.object (.heap location))
      return (runtime, LetAction.value token)) =
      .error fault
    rw [semanticFailure]
    rfl
  exact concreteFaultLeaf_unaryHostLet
    (step := resetStep count)
    (failure := failure)
    evaluated valueCompiled valueAdapted resultFound continuationAdapted
    initialRelated hObject hImp hSat hi hContract hParams operation
    failureRelated

/-- Compiler/adaptor terminal boundary for an arbitrary represented failure
of a generated nonempty reuse call. Operation-specific wrappers provide the
exact source/concrete equations and their error relation. -/
theorem concreteFaultLeaf_reuse_of_refines
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {tokenId : Lean.FVarId}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List Lean.FVarId}
    {indices : List Nat}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value}
    {semanticFields : Array Value}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultIndex : Nat}
    {location : Location}
    {targetRest : Wasm.Program}
    {failure : ConcreteError}
    {fault : RuntimeFault}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok ((tokenId :: fvarIds).map Fir.Wasm.Instruction.localGet ++
          [.call (.runtime
            (.reuse info updateHeader fieldKinds resultKind))]))
    (argumentsFound : List.Forall₂
      (fun fvarId index =>
        findFVar? (functionBindings sourceFunction) fvarId = some index)
      (tokenId :: fvarIds) indices)
    (callFound :
      callIndex? sourceModule
        (.runtime (.reuse info updateHeader fieldKinds resultKind)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (tokenLookup :
      lookup sourceEnv tokenId = some (.reuseToken (some location)))
    (argumentsEvaluated :
      evalArgs sourceEnv args = .ok semanticFields)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (semantic :
      reuse sourceRuntime (.reuseToken (some location)) info updateHeader
          semanticFields =
        .error fault)
    (operation :
      reuseStep info updateHeader fieldKinds resultKind initial physicalArgs =
        trap (clearFailure initial) (.runtime failure.toTrap))
    (failureRelated : ConcreteErrorSourceRel witness failure fault) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime fault := by
  have argumentsAdapted := FirTalos.Correctness.instructions_localGets
    (sourceModule := sourceModule) (sourceFunction := sourceFunction)
    (labels := labels) (found := by
      simpa [functionBindings] using argumentsFound)
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          ((tokenId :: fvarIds).map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime
              (.reuse info updateHeader fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have adaptedBase :=
    codeAdapted_let valueCompiled valueAdapted resultFound continuationAdapted
  have adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.let decl continuation)
        (indices.map Wasm.Instruction.localGet ++
          .call id :: .localSet resultIndex :: targetRest) := by
    simpa only [List.append_assoc, List.singleton_append] using adaptedBase
  have evaluated :
      evalLetValue
          (sourceCodeState context sourceRuntime sourceEnv
            (.let decl continuation)) decl =
        .error fault := by
    unfold evalLetValue
    rw [valueEq]
    simp only [sourceCodeState]
    have tokenLookupValue :
        lookupValue sourceEnv tokenId =
          .ok (.reuseToken (some location)) := by
      simp [lookupValue, tokenLookup]
    rw [tokenLookupValue, argumentsEvaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        reuse sourceRuntime (.reuseToken (some location)) info updateHeader
          semanticFields) =
      .error fault
    rw [semantic]
    rfl
  exact concreteFaultLeaf_hostLet
    (step := reuseStep info updateHeader fieldKinds resultKind)
    (failure := failure)
    (sourceLetFault_execEvaluates evaluated) adapted initialRelated hGets
    hImp hSat hi hContract hParams operation failureRelated

/-- A generated reuse of a stale mapped nonempty token preserves the exact
address-related dead-object fault and cannot write its result local. -/
theorem concreteFaultLeaf_reuse_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {tokenId : Lean.FVarId}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List Lean.FVarId}
    {indices : List Nat}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value}
    {fields : List Word32}
    {semanticFields : Array Value}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultIndex : Nat}
    {address : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok ((tokenId :: fvarIds).map Fir.Wasm.Instruction.localGet ++
          [.call (.runtime
            (.reuse info updateHeader fieldKinds resultKind))]))
    (argumentsFound : List.Forall₂
      (fun fvarId index =>
        findFVar? (functionBindings sourceFunction) fvarId = some index)
      (tokenId :: fvarIds) indices)
    (callFound :
      callIndex? sourceModule
        (.runtime (.reuse info updateHeader fieldKinds resultKind)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (tokenLookup :
      lookup sourceEnv tokenId = some (.reuseToken (some location)))
    (argumentsEvaluated :
      evalArgs sourceEnv args = .ok semanticFields)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
    (tokenRelated :
      ValueRel witness .reuseToken (.word32 address)
        (.reuseToken (some location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    reuseStep_deadObject_of_refines initialRelated.1 argsLength decoded
      tokenRelated found dead arity semanticArity
  exact concreteFaultLeaf_reuse_of_refines
    (failure := .sourceAddress (.deadObject address))
    valueEq valueCompiled argumentsFound callFound resultFound
    continuationAdapted tokenLookup argumentsEvaluated initialRelated hGets
    hImp hSat hi hContract hParams semantic operation failureRelated

/-- A generated reuse of a live mapped nonconstructor preserves exact
`expectedConstructor` and traps before retained-capacity checks, result-local
write, or continuation. -/
theorem concreteFaultLeaf_reuse_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceEnv : Env}
    {tokenId : Lean.FVarId}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool}
    {args : Array (LCNF.Arg .impure)}
    {fvarIds : List Lean.FVarId}
    {indices : List Nat}
    {fieldKinds : Array AbiKind}
    {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value}
    {fields : List Word32}
    {semanticFields : Array Value}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultIndex : Nat}
    {address : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok ((tokenId :: fvarIds).map Fir.Wasm.Instruction.localGet ++
          [.call (.runtime
            (.reuse info updateHeader fieldKinds resultKind))]))
    (argumentsFound : List.Forall₂
      (fun fvarId index =>
        findFVar? (functionBindings sourceFunction) fvarId = some index)
      (tokenId :: fvarIds) indices)
    (callFound :
      callIndex? sourceModule
        (.runtime (.reuse info updateHeader fieldKinds resultKind)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (tokenLookup :
      lookup sourceEnv tokenId = some (.reuseToken (some location)))
    (argumentsEvaluated :
      evalArgs sourceEnv args = .ok semanticFields)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (argsLength : physicalArgs.length = fieldKinds.size + 1)
    (decoded : decodeReuseWords physicalArgs = .ok (address, fields))
    (tokenRelated :
      ValueRel witness .reuseToken (.word32 address)
        (.reuseToken (some location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (notConstructor : ∀ object, cell.object ≠ .ctor object)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? =
      some (reuseContract info updateHeader fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semantic, failureRelated⟩ :=
    reuseStep_expectedConstructor_of_refines initialRelated.1 argsLength
      decoded tokenRelated found live notConstructor arity semanticArity
  exact concreteFaultLeaf_reuse_of_refines
    (failure := .source .expectedConstructor)
    valueEq valueCompiled argumentsFound callFound resultFound
    continuationAdapted tokenLookup argumentsEvaluated initialRelated hGets
    hImp hSat hi hContract hParams semantic operation failureRelated

/-- An object-slot mutation of a related nonconstructor faults at the common
header gate before bounds, padding, old-field decoding, or any heap write. -/
theorem concreteFaultLeaf_objectSet_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {fieldKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord fieldWord : Word32}
    {location : Location}
    {field : Value}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.oset objectId index (.fvar fieldId) continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (fieldLookup : evalArg sourceEnv (.fvar fieldId) = .ok field)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField :
      locals.get fieldIndex =
        some (.i32 (UInt32.ofNat fieldWord.value)))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (constructorFailed :
      getConstructor sourceRuntime (.object (.heap location)) =
        .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (objectSetContract index fieldKind))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    objectSetStep_expectedConstructor_of_refines
      (fieldWord := fieldWord) (fieldKind := fieldKind) (field := field)
      index initialRelated.1 objectRelated constructorFailed
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.oset objectId index (.fvar fieldId) continuation))
        (FaultObservation sourceRuntime .expectedConstructor) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, lookupValue, objectLookup,
      fieldLookup, semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := objectSetStep index fieldKind)
    (failure := .source .expectedConstructor)
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation failureRelated

/-- Absolute-slot `USize` mutation preserves the same nonconstructor fault and
does not reach slot arithmetic or its continuation. -/
theorem concreteFaultLeaf_usizeSet_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord : Word32}
    {field : UInt64}
    {location : Location}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.uset objectId index fieldId continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize field))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField : locals.get fieldIndex = some (.i64 field))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (constructorFailed :
      getConstructor sourceRuntime (.object (.heap location)) =
        .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (usizeSetContract index))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    usizeSetStep_expectedConstructor_of_refines
      (field := field) index initialRelated.1 objectRelated constructorFailed
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.uset objectId index fieldId continuation))
        (FaultObservation sourceRuntime .expectedConstructor) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup, fieldLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := usizeSetStep index)
    (failure := .source .expectedConstructor)
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation failureRelated

/-- A single kind-indexed leaf covers UInt8/16/32/64 mutation of a related
nonconstructor. The physical-value relation fixes the concrete field lane
while the common header theorem fixes the exact trap. -/
theorem concreteFaultLeaf_scalarSet_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord : Word32}
    {physicalField : Wasm.Value}
    {field : ScalarValue}
    {fieldKind : AbiKind}
    {location : Location}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (fieldLookup :
      lookupValue sourceEnv fieldId = .ok (.scalar field))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField : locals.get fieldIndex = some physicalField)
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (fieldRelated :
      PhysicalValueRel witness fieldKind physicalField (.scalar field))
    (constructorFailed :
      getConstructor sourceRuntime (.object (.heap location)) =
        .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (scalarSetContract slotIndex byteOffset fieldKind))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    scalarSetStep_expectedConstructor_of_refines
      (slotIndex := slotIndex) (byteOffset := byteOffset)
      initialRelated.1 objectRelated fieldRelated constructorFailed
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.sset objectId slotIndex byteOffset fieldId type continuation))
        (FaultObservation sourceRuntime .expectedConstructor) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup, fieldLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := scalarSetStep slotIndex byteOffset fieldKind)
    (failure := .source .expectedConstructor)
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation failureRelated

/-- Constructor-tag mutation of a related nonconstructor faults before
encoding the replacement tag, writing the header, or entering its
continuation. -/
theorem concreteFaultLeaf_setTag_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {tag : Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.setTag objectId tag continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (constructorFailed :
      getConstructor sourceRuntime (.object (.heap location)) =
        .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (setTagContract tag))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.setTag objectId tag continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    setTagStep_expectedConstructor_of_refines tag initialRelated.1
      objectRelated constructorFailed
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.setTag objectId tag continuation))
        (FaultObservation sourceRuntime .expectedConstructor) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := setTagStep tag)
    (failure := .source .expectedConstructor)
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- An object-field write beyond the live constructor payload preserves the
exact source-classified bounds fault and does not enter its continuation. -/
theorem concreteFaultLeaf_objectSet_outOfBounds
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {fieldKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord fieldWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {semantic : ConstructorObject}
    {field : Value}
    {info : LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.oset objectId index (.fvar fieldId) continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (fieldLookup : evalArg sourceEnv (.fvar fieldId) = .ok field)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField :
      locals.get fieldIndex =
        some (.i32 (UInt32.ofNat fieldWord.value)))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (descriptorFound :
      witness.descriptors.lookup? objectWord =
        some (.constructor info fieldKinds))
    (outOfBounds : semantic.objectFields.size ≤ index)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (objectSetContract index fieldKind))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime
      (.objectFieldOutOfBounds index semantic.objectFields.size) := by
  obtain ⟨operation, semanticFailure⟩ :=
    objectSetStep_outOfBounds_of_refines
      (fieldWord := fieldWord) (fieldKind := fieldKind) (field := field)
      initialRelated.1 objectRelated found live objectEq descriptorFound
      outOfBounds
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.oset objectId index (.fvar fieldId) continuation))
        (FaultObservation sourceRuntime
          (.objectFieldOutOfBounds index semantic.objectFields.size)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, lookupValue, objectLookup,
      fieldLookup, semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := objectSetStep index fieldKind)
    (failure := .source
      (.objectFieldOutOfBounds index semantic.objectFields.size))
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation
    (.source (.objectFieldOutOfBounds index semantic.objectFields.size))

/-- A stale object-field write faults at the liveness gate before reading or
replacing its old payload word. -/
theorem concreteFaultLeaf_objectSet_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {fieldKind : AbiKind}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord fieldWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {field : Value}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.oset objectId index (.fvar fieldId) continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookup sourceEnv objectId = some (.object (.heap location)))
    (fieldLookup : evalArg sourceEnv (.fvar fieldId) = .ok field)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField :
      locals.get fieldIndex =
        some (.i32 (UInt32.ofNat fieldWord.value)))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (objectSetContract index fieldKind))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    objectSetStep_deadObject_of_refines
      (fieldWord := fieldWord) (fieldKind := fieldKind) (field := field)
      index initialRelated.1 objectRelated found dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.oset objectId index (.fvar fieldId) continuation))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, lookupValue, objectLookup,
      fieldLookup, semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := objectSetStep index fieldKind)
    (failure := .sourceAddress (.deadObject objectWord))
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation failureRelated

/-- A `USize` write outside the constructor's absolute fixed-slot interval
preserves the exact FIR index and combined object/`USize` bound. -/
theorem concreteFaultLeaf_usizeSet_outOfBounds
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord : Word32}
    {field : UInt64}
    {location : Location}
    {cell : HeapCell}
    {semantic : ConstructorObject}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.uset objectId index fieldId continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize field))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField : locals.get fieldIndex = some (.i64 field))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor semantic)
    (outOfBounds :
      index < semantic.objectFields.size ∨
        semantic.objectFields.size + semantic.usizeFields.size ≤ index)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (usizeSetContract index))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime
      (.usizeFieldOutOfBounds index
        (semantic.objectFields.size + semantic.usizeFields.size)) := by
  obtain ⟨operation, semanticFailure⟩ :=
    usizeSetStep_outOfBounds_of_refines
      (field := field) initialRelated.1 objectRelated found live objectEq
      outOfBounds
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.uset objectId index fieldId continuation))
        (FaultObservation sourceRuntime
          (.usizeFieldOutOfBounds index
            (semantic.objectFields.size + semantic.usizeFields.size))) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup, fieldLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := usizeSetStep index)
    (failure := .source
      (.usizeFieldOutOfBounds index
        (semantic.objectFields.size + semantic.usizeFields.size)))
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation
    (.source (.usizeFieldOutOfBounds index
      (semantic.objectFields.size + semantic.usizeFields.size)))

/-- A stale `USize` write faults before the absolute fixed-slot coordinate is
checked or any field is replaced. -/
theorem concreteFaultLeaf_usizeSet_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {index : Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord : Word32}
    {field : UInt64}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.uset objectId index fieldId continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize field))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField : locals.get fieldIndex = some (.i64 field))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (usizeSetContract index))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    usizeSetStep_deadObject_of_refines
      (field := field) index initialRelated.1 objectRelated found dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.uset objectId index fieldId continuation))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup, fieldLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_binaryHostEffect
    (step := usizeSetStep index)
    (failure := .sourceAddress (.deadObject objectWord))
    sourceFault adapted initialRelated hObject hField hImp hSat hi hContract
    hParams operation failureRelated

/-- One kind-indexed stale packed-scalar mutation leaf. The physical-value
relation dispatches the shared proof to the UInt8/16/32 i32 lanes or UInt64
i64 lane, so callers do not need four syntax-level theorems. -/
theorem concreteFaultLeaf_scalarSet_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId}
    {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex fieldIndex : Nat}
    {objectWord : Word32}
    {physicalField : Wasm.Value}
    {field : ScalarValue}
    {fieldKind : AbiKind}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (fieldLookup :
      lookupValue sourceEnv fieldId = .ok (.scalar field))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (hField : locals.get fieldIndex = some physicalField)
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (fieldRelated :
      PhysicalValueRel witness fieldKind physicalField (.scalar field))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (scalarSetContract slotIndex byteOffset fieldKind))
    (hParams : imp.params.length = 2) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.sset objectId slotIndex byteOffset fieldId type continuation)
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  cases fieldRelated with
  | word32 fieldRelated =>
      cases fieldRelated with
      | uint8 encoded =>
          obtain ⟨operation, semanticFailure, failureRelated⟩ :=
            scalarSetStep_uint8_deadObject_of_refines
              (slotIndex := slotIndex) (byteOffset := byteOffset)
              initialRelated.1 objectRelated (.uint8 encoded) found dead
          have sourceFault :
              ExecEvaluates sourceExternals
                (sourceCodeState context sourceRuntime sourceEnv
                  (.sset objectId slotIndex byteOffset fieldId type
                    continuation))
                (FaultObservation sourceRuntime (.deadObject location)) := by
            apply sourceCodeFault_execEvaluates
            simp [executeStep, coreStep, sourceCodeState, objectLookup,
              fieldLookup, semanticFailure, fail, observe, FaultObservation]
          exact concreteFaultLeaf_binaryHostEffect
            (step := scalarSetStep slotIndex byteOffset .uint8)
            (failure := .sourceAddress (.deadObject objectWord))
            sourceFault adapted initialRelated hObject hField hImp hSat hi
            hContract hParams operation failureRelated
      | uint16 encoded =>
          obtain ⟨operation, semanticFailure, failureRelated⟩ :=
            scalarSetStep_uint16_deadObject_of_refines
              (slotIndex := slotIndex) (byteOffset := byteOffset)
              initialRelated.1 objectRelated (.uint16 encoded) found dead
          have sourceFault :
              ExecEvaluates sourceExternals
                (sourceCodeState context sourceRuntime sourceEnv
                  (.sset objectId slotIndex byteOffset fieldId type
                    continuation))
                (FaultObservation sourceRuntime (.deadObject location)) := by
            apply sourceCodeFault_execEvaluates
            simp [executeStep, coreStep, sourceCodeState, objectLookup,
              fieldLookup, semanticFailure, fail, observe, FaultObservation]
          exact concreteFaultLeaf_binaryHostEffect
            (step := scalarSetStep slotIndex byteOffset .uint16)
            (failure := .sourceAddress (.deadObject objectWord))
            sourceFault adapted initialRelated hObject hField hImp hSat hi
            hContract hParams operation failureRelated
      | uint32 encoded =>
          obtain ⟨operation, semanticFailure, failureRelated⟩ :=
            scalarSetStep_uint32_deadObject_of_refines
              (slotIndex := slotIndex) (byteOffset := byteOffset)
              initialRelated.1 objectRelated (.uint32 encoded) found dead
          have sourceFault :
              ExecEvaluates sourceExternals
                (sourceCodeState context sourceRuntime sourceEnv
                  (.sset objectId slotIndex byteOffset fieldId type
                    continuation))
                (FaultObservation sourceRuntime (.deadObject location)) := by
            apply sourceCodeFault_execEvaluates
            simp [executeStep, coreStep, sourceCodeState, objectLookup,
              fieldLookup, semanticFailure, fail, observe, FaultObservation]
          exact concreteFaultLeaf_binaryHostEffect
            (step := scalarSetStep slotIndex byteOffset .uint32)
            (failure := .sourceAddress (.deadObject objectWord))
            sourceFault adapted initialRelated hObject hField hImp hSat hi
            hContract hParams operation failureRelated
  | word64 fieldRelated =>
      cases fieldRelated with
      | uint64 =>
          rename_i fieldValue
          obtain ⟨operation, semanticFailure, failureRelated⟩ :=
            scalarSetStep_uint64_deadObject_of_refines
              (field := fieldValue) (slotIndex := slotIndex)
              (byteOffset := byteOffset)
              initialRelated.1 objectRelated .uint64 found dead
          have sourceFault :
              ExecEvaluates sourceExternals
                (sourceCodeState context sourceRuntime sourceEnv
                  (.sset objectId slotIndex byteOffset fieldId type
                    continuation))
                (FaultObservation sourceRuntime (.deadObject location)) := by
            apply sourceCodeFault_execEvaluates
            simp [executeStep, coreStep, sourceCodeState, objectLookup,
              fieldLookup, semanticFailure, fail, observe, FaultObservation]
          exact concreteFaultLeaf_binaryHostEffect
            (step := scalarSetStep slotIndex byteOffset .uint64)
            (failure := .sourceAddress (.deadObject objectWord))
            sourceFault adapted initialRelated hObject hField hImp hSat hi
            hContract hParams operation failureRelated
  | float32Bits fieldRelated => cases fieldRelated
  | float64Bits fieldRelated => cases fieldRelated

/-- Stale constructor-tag mutation faults before updating the header or
entering its continuation. -/
theorem concreteFaultLeaf_setTag_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {tag : Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.setTag objectId tag continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (setTagContract tag))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.setTag objectId tag continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    setTagStep_deadObject_of_refines tag initialRelated.1 objectRelated found
      dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.setTag objectId tag continuation))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := setTagStep tag)
    (failure := .sourceAddress (.deadObject objectWord))
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- Stale nonpersistent reference-count increment faults before count
arithmetic or a concrete header write. -/
theorem concreteFaultLeaf_increment_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.inc objectId amount check false continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (incrementContract amount check))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.inc objectId amount check false continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    incrementStep_deadObject_of_refines
      (amount := amount) (check := check)
      initialRelated.1 objectRelated found dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.inc objectId amount check false continuation))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := incrementStep amount check)
    (failure := .sourceAddress (.deadObject objectWord))
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- An unchecked increment of a related tagged object traps with
`expectedHeapReference` before count arithmetic, a header read, or the
continuation. -/
theorem concreteFaultLeaf_increment_tagged_unchecked
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {payload : UInt64}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.inc objectId amount false false continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.tagged payload)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.tagged payload)))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? = some (incrementContract amount false))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.inc objectId amount false false continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedHeapReference := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    incrementStep_tagged_unchecked_of_refines (amount := amount)
      initialRelated.1 objectRelated
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.inc objectId amount false false continuation))
        (FaultObservation sourceRuntime .expectedHeapReference) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := incrementStep amount false)
    (failure := .source .expectedHeapReference)
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- A positive stale nonpersistent decrement faults on its first header read,
before recursive ownership release can begin. -/
theorem concreteFaultLeaf_decrement_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.dec objectId (amount + 1) check false objectFields? continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (decrementContract (amount + 1) check objectFields?))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.dec objectId (amount + 1) check false objectFields? continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    decrementStep_deadObject_of_refines
      (amount := amount) (check := check) (objectFields? := objectFields?)
      initialRelated.1 objectRelated found dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.dec objectId (amount + 1) check false objectFields? continuation))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := decrementStep (amount + 1) check objectFields?)
    (failure := .sourceAddress (.deadObject objectWord))
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- A positive decrement of a mapped live, ordinary, zero-count object traps
with the exact related underflow before any header write, child release, or
continuation instruction can execute. -/
theorem concreteFaultLeaf_decrement_underflow
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.dec objectId (amount + 1) check false objectFields? continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (zero : cell.rc = 0)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (decrementContract (amount + 1) check objectFields?))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.dec objectId (amount + 1) check false objectFields? continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime
        (.referenceCountUnderflow location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    decrementStep_underflow_of_refines
      (amount := amount) (check := check) (objectFields? := objectFields?)
      initialRelated.1 objectRelated found live ordinary zero
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.dec objectId (amount + 1) check false objectFields? continuation))
        (FaultObservation sourceRuntime
          (.referenceCountUnderflow location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := decrementStep (amount + 1) check objectFields?)
    (failure := .sourceAddress
      (.referenceCountUnderflow objectWord))
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- Every positive unchecked decrement of a related tagged object traps
with `expectedHeapReference` on its first repetition, before recursive release
or the continuation. -/
theorem concreteFaultLeaf_decrement_tagged_unchecked
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {objectFields? : Option Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {payload : UInt64}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.dec objectId (amount + 1) false false objectFields? continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.tagged payload)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.tagged payload)))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (decrementContract (amount + 1) false objectFields?))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.dec objectId (amount + 1) false false objectFields? continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedHeapReference := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    decrementStep_tagged_unchecked_of_refines
      (amount := amount) (objectFields? := objectFields?)
      initialRelated.1 objectRelated
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.dec objectId (amount + 1) false false objectFields? continuation))
        (FaultObservation sourceRuntime .expectedHeapReference) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := decrementStep (amount + 1) false objectFields?)
    (failure := .source .expectedHeapReference)
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- General mapped-heap decrement fault leaf. It covers direct and recursively
reached dead-object or underflow failures after any successful ownership
prefix; only semantic release-fuel exhaustion remains outside T4 because its
concrete counterpart is target-classified. -/
theorem concreteFaultLeaf_decrement_fault
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {fault : RuntimeFault}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.dec objectId amount check false objectFields? continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord)
        (.object (.heap location)))
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (notFuel :
      fault ≠ .malformed "reference-count release fuel exhausted")
    (semanticFailure :
      decValue sourceRuntime (.object (.heap location)) amount check =
        .error fault)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract :
      hostSpec.contracts[id]? =
        some (decrementContract amount check objectFields?))
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime fault := by
  obtain ⟨failure, operation, failureRelated⟩ :=
    decrementStep_fault_of_refines initialRelated.1 objectRelated
      descriptorsEq notFuel semanticFailure
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.dec objectId amount check false objectFields? continuation))
        (FaultObservation sourceRuntime fault) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := decrementStep amount check objectFields?)
    (failure := failure)
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- Repeating explicit deletion on a stale object preserves the exact related
address/location fault and cannot enter the continuation. -/
theorem concreteFaultLeaf_delete_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {continuation : LCNF.Code .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {objectIndex : Nat}
    {objectWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.del objectId continuation)
        ([.localGet objectIndex, .call id] ++ targetRest))
    (objectLookup :
      lookupValue sourceEnv objectId =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hObject :
      locals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .object (.word32 objectWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? = some deleteContract)
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.del objectId continuation)
      ([.localGet objectIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    deleteStep_deadObject_of_refines initialRelated.1 objectRelated found dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv
          (.del objectId continuation))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, objectLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := deleteStep)
    (failure := .sourceAddress (.deadObject objectWord))
    sourceFault adapted initialRelated hObject hImp hSat hi hContract hParams
    operation failureRelated

/-- An object-mode case chain whose related discriminator is not a
constructor faults at the generated `getTag` prefix before any alternative
comparison or branch selection. The remainder of the adapted chain stays
abstract. -/
theorem concreteFaultLeaf_cases_getTag_expectedConstructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {casesDecl : LCNF.Cases .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {discrIndex : Nat}
    {discrWord : Word32}
    {discrValue : Value}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.cases casesDecl)
        ([.localGet discrIndex, .call id] ++ targetRest))
    (discrLookup :
      lookupValue sourceEnv casesDecl.discr = .ok discrValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hDiscr :
      locals.get discrIndex =
        some (.i32 (UInt32.ofNat discrWord.value)))
    (discrRelated :
      ValueRel witness .tobject (.word32 discrWord) discrValue)
    (tagFailed :
      getTag sourceRuntime discrValue = .error .expectedConstructor)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? = some getTagContract)
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.cases casesDecl)
      ([.localGet discrIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime .expectedConstructor := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    getTagStep_expectedConstructor_of_refines initialRelated.1 discrRelated
      tagFailed
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv (.cases casesDecl))
        (FaultObservation sourceRuntime .expectedConstructor) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, discrLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := getTagStep)
    (failure := .source .expectedConstructor)
    sourceFault adapted initialRelated hDiscr hImp hSat hi hContract hParams
    operation failureRelated

/-- An object-mode case chain whose generated prefix reads a stale
discriminator faults before any constructor comparison or branch selection.
The remainder of the adapted alternative chain stays abstract. -/
theorem concreteFaultLeaf_cases_getTag_deadObject
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {hostSpec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {id : Nat}
    {imp : Wasm.ImportDecl}
    {sourceEnv : Env}
    {casesDecl : LCNF.Cases .impure}
    {sourceRuntime : RuntimeState}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {discrIndex : Nat}
    {discrWord : Word32}
    {location : Location}
    {cell : HeapCell}
    {targetRest : Wasm.Program}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels
        (.cases casesDecl)
        ([.localGet discrIndex, .call id] ++ targetRest))
    (discrLookup :
      lookupValue sourceEnv casesDecl.discr =
        .ok (.object (.heap location)))
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (hDiscr :
      locals.get discrIndex =
        some (.i32 (UInt32.ofNat discrWord.value)))
    (discrRelated :
      ValueRel witness .tobject (.word32 discrWord)
        (.object (.heap location)))
    (found : findCell? sourceRuntime.heap location = some cell)
    (dead : cell.live = false)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module hostSpec)
    (hi : id < module.imports.length)
    (hContract : hostSpec.contracts[id]? = some getTagContract)
    (hParams : imp.params.length = 1) :
    ConcreteFaultLeaf context sourceModule sourceFunction labels module hostEnv
      sourceExternals sourceRuntime sourceEnv (.cases casesDecl)
      ([.localGet discrIndex, .call id] ++ targetRest)
      initial locals witness sourceRuntime (.deadObject location) := by
  obtain ⟨operation, semanticFailure, failureRelated⟩ :=
    getTagStep_deadObject_of_refines initialRelated.1 discrRelated found dead
  have sourceFault :
      ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv (.cases casesDecl))
        (FaultObservation sourceRuntime (.deadObject location)) := by
    apply sourceCodeFault_execEvaluates
    simp [executeStep, coreStep, sourceCodeState, discrLookup,
      semanticFailure, fail, observe, FaultObservation]
  exact concreteFaultLeaf_unaryHostEffect
    (step := getTagStep)
    (failure := .sourceAddress (.deadObject discrWord))
    sourceFault adapted initialRelated hDiscr hImp hSat hi hContract hParams
    operation failureRelated

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
