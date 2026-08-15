import FirTalos.Correctness.Execution
import FirTalos.Correctness.Semantics
import Interpreter.Wasm.Spec.Termination

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

/--
The continuation postcondition used when a verified body is installed as a
Talos function. It is the store-specific counterpart of the postcondition in
`Wasm.FuncSpec.of_wp_body` and retains the caller operand remainder prescribed
by the Wasm calling convention.
-/
def FunctionBodyPost {host : Type} (function : Wasm.Function)
    (args : List Wasm.Value)
    (Post : Wasm.Store host → List Wasm.Value → Prop) :
    Wasm.Assertion host :=
  fun continuation =>
    match continuation with
    | .Fallthrough targetStore targetLocals =>
        Post targetStore
          (targetLocals.values.take function.results.length ++
            args.drop function.numParams)
    | .Return targetStore values =>
        Post targetStore
          (values.take function.results.length ++ args.drop function.numParams)
    | _ => False

/-- The canonical successful source observation for one returned value. -/
def ReturnedObservation (runtime : RuntimeState) (value : Value) : Observation :=
  { outcome := .returned value
    heap := runtime.heap
    world := runtime.world
    trace := runtime.trace }

/-- Weakening the continuation assertion preserves the semantic code judgment. -/
theorem CodeWP.conseq
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {target : Wasm.Program}
    {targetStore : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {tail : List Wasm.Value} {Q Q' : Wasm.Assertion RuntimeHost}
    (post : Q ⇛ Q')
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code target targetStore targetLocals tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv code target targetStore targetLocals tail Q' :=
  ⟨correct.1, correct.2.1, Wasm.wp.conseq post correct.2.2⟩

/--
A decoded local return entails the function-body observation postcondition for
one result lane. The explicit comparison premise isolates the policy-level W3
observation relation from the ABI and control-flow proof.
-/
theorem ReturnPost.toFunctionBodyPost
    {function : Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceValue : Value} {kind : AbiKind}
    (resultCount : function.results.length = 1)
    (related :
      compareObservations (ReturnedObservation sourceRuntime sourceValue)
          (.returned sourceValue sourceRuntime) =
        .related (ReturnedObservation sourceRuntime sourceValue)
          (.returned sourceValue sourceRuntime)) :
    ReturnPost sourceRuntime sourceValue kind [] ⇛
      FunctionBodyPost function []
        (RelatedPost #[kind] (ReturnedObservation sourceRuntime sourceValue)) := by
  intro continuation returned
  rcases returned with ⟨targetStore, physical, rfl, runtimeEq, decoded⟩
  simp only [FunctionBodyPost, List.drop_nil, List.append_nil]
  rw [resultCount]
  simp only [List.take]
  refine ⟨.returned sourceValue sourceRuntime, ?_, related⟩
  have decodedArgs := decodeArgs_singleton_of_decodesValue decoded
  rw [observeTarget_success_singleton decodedArgs, runtimeEq]

/--
Store-specific bridge from total correctness of one function body to Talos's
fuel-free public function predicate. Unlike `Wasm.FuncSpec.of_wp_body`, this
does not quantify over every initial store, so it can consume FIR's concrete
runtime/handle relation directly.
-/
theorem terminatesWith_of_wp_body_at
    {host : Type} {env : Wasm.HostEnv host} {module : Wasm.Module}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store host} {args : List Wasm.Value}
    {Post : Wasm.Store host → List Wasm.Value → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (bodyWP :
      Wasm.wp module function.body (FunctionBodyPost function args Post)
        initial (function.toLocals (args.take function.numParams).reverse) env) :
    Wasm.TerminatesWith env module functionIndex initial args Post := by
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
      exact ⟨finalLocals.values.take function.results.length ++
          args.drop function.numParams, final, rfl, bodyPost⟩
  | Return final values =>
      rw [execution] at bodyPost
      exact ⟨values.take function.results.length ++ args.drop function.numParams,
        final, rfl, bodyPost⟩
  | Break level final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Trap final message =>
      rw [execution] at bodyPost
      exact bodyPost.elim
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

/-- A local semantic lowering proof yields a fuel-free related target call. -/
theorem CodeWP.toTerminatesWithRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {initial : Wasm.Store RuntimeHost}
    {args : List Wasm.Value} {resultKinds : Array AbiKind}
    {source : Observation}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) []
        (FunctionBodyPost function args (RelatedPost resultKinds source))) :
    Wasm.TerminatesWith hostEnv module functionIndex initial args
      (RelatedPost resultKinds source) := by
  apply terminatesWith_of_wp_body_at notImport found
  simpa [Wasm.Function.toLocals] using correct.2.2

/-- Fuel-free partial correctness follows from the same local body proof. -/
theorem CodeWP.toPartiallyMeetsRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {initial : Wasm.Store RuntimeHost}
    {args : List Wasm.Value} {resultKinds : Array AbiKind}
    {source : Observation}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) []
        (FunctionBodyPost function args (RelatedPost resultKinds source))) :
    Wasm.PartiallyMeets hostEnv module functionIndex initial args
      (RelatedPost resultKinds source) :=
  (correct.toTerminatesWithRelated notImport found).toPartiallyMeets

/-- Total correctness for an exported function resolved by name. -/
def ExportTerminatesWith (hostEnv : Wasm.HostEnv RuntimeHost)
    (module : Wasm.Module) (exportName : String)
    (initial : Wasm.Store RuntimeHost) (args : List Wasm.Value)
    (Post : Wasm.Store RuntimeHost → List Wasm.Value → Prop) : Prop :=
  ∃ functionIndex,
    module.findExport exportName = some functionIndex ∧
      Wasm.TerminatesWith hostEnv module functionIndex initial args Post

/-- Partial correctness for an exported function resolved by name. -/
def ExportPartiallyMeets (hostEnv : Wasm.HostEnv RuntimeHost)
    (module : Wasm.Module) (exportName : String)
    (initial : Wasm.Store RuntimeHost) (args : List Wasm.Value)
    (Post : Wasm.Store RuntimeHost → List Wasm.Value → Prop) : Prop :=
  ∃ functionIndex,
    module.findExport exportName = some functionIndex ∧
      Wasm.PartiallyMeets hostEnv module functionIndex initial args Post

/-- Package a body proof as an observation-related exported-function theorem. -/
theorem CodeWP.toExportTerminatesWithRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {exportName : String}
    {initial : Wasm.Store RuntimeHost} {args : List Wasm.Value}
    {resultKinds : Array AbiKind} {source : Observation}
    (exported : module.findExport exportName = some functionIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) []
        (FunctionBodyPost function args (RelatedPost resultKinds source))) :
    ExportTerminatesWith hostEnv module exportName initial args
      (RelatedPost resultKinds source) :=
  ⟨functionIndex, exported, correct.toTerminatesWithRelated notImport found⟩

/-- Package a body proof as an observation-related partial exported theorem. -/
theorem CodeWP.toExportPartiallyMeetsRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {exportName : String}
    {initial : Wasm.Store RuntimeHost} {args : List Wasm.Value}
    {resultKinds : Array AbiKind} {source : Observation}
    (exported : module.findExport exportName = some functionIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) []
        (FunctionBodyPost function args (RelatedPost resultKinds source))) :
    ExportPartiallyMeets hostEnv module exportName initial args
      (RelatedPost resultKinds source) :=
  ⟨functionIndex, exported, correct.toPartiallyMeetsRelated notImport found⟩

/--
A closed single-result local return proof yields total correctness for the
resolved export and the canonical successful source observation.
-/
theorem CodeWP.toExportTerminatesWithRelated_of_return
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {initialSourceRuntime resultSourceRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {kind : AbiKind}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {exportName : String}
    {initial : Wasm.Store RuntimeHost} {args : List Wasm.Value}
    (exported : module.findExport exportName = some functionIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (noArgs : args = [])
    (resultCount : function.results.length = 1)
    (related :
      compareObservations (ReturnedObservation resultSourceRuntime sourceValue)
          (.returned sourceValue resultSourceRuntime) =
        .related (ReturnedObservation resultSourceRuntime sourceValue)
          (.returned sourceValue resultSourceRuntime))
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        initialSourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) []
        (ReturnPost resultSourceRuntime sourceValue kind [])) :
    ExportTerminatesWith hostEnv module exportName initial args
      (RelatedPost #[kind]
        (ReturnedObservation resultSourceRuntime sourceValue)) := by
  subst args
  apply CodeWP.toExportTerminatesWithRelated exported notImport found
  exact correct.conseq (ReturnPost.toFunctionBodyPost resultCount related)

end FirTalos.Correctness
