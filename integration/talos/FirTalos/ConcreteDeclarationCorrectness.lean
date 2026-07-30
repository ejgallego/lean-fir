import FirTalos.ConcreteCacheCorrectness
import FirTalos.Correctness.Program

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Exact deterministic result used while composing a declaration with its
callers. The callee returns one physical lane and leaves the caller operand
remainder unchanged. -/
def ExactReturnPost (afterCall : Wasm.Store Host)
    (physical : Wasm.Value) (callerTail : List Wasm.Value) :
    Wasm.Store Host → List Wasm.Value → Prop :=
  fun final results =>
    final = afterCall ∧ results = physical :: callerTail

/-- Public successful-return relation for W6. The final concrete runtime
refines the complete source runtime (heap, globals, world, and trace), the
structured failure channel is clear, and the singleton physical result
refines the source value at its checked ABI kind. -/
def RefinedReturnPost (sourceRuntime : RuntimeState) (sourceValue : Value)
    (kind : AbiKind) (callerTail : List Wasm.Value) :
    Wasm.Store Host → List Wasm.Value → Prop :=
  fun final results =>
    ∃ witness physical,
      ConcreteRuntimeRel final.host.runtime witness sourceRuntime ∧
      final.host.failure? = none ∧
      PhysicalValueRel witness kind physical sourceValue ∧
      results = physical :: callerTail

/-- Compiler-and-adapter proof for one concrete declaration body. Physical
parameters are fixed, while the proof is polymorphic in the caller operand
remainder restored by Talos's direct-call convention. -/
def DeclarationBodyWP
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : LCNF.Code .impure)
    (targetFunction : Wasm.Function)
    (initial afterCall : Wasm.Store Host)
    (initialWitness : RefinementWitness)
    (parameters : List Wasm.Value)
    (physical : Wasm.Value) : Prop :=
  parameters.length = targetFunction.numParams ∧
    targetFunction.results.length = 1 ∧
      ∀ callerTail,
        CodeWP context sourceModule sourceFunction [] module hostEnv
          sourceRuntime sourceEnv sourceCode targetFunction.body initial
          (targetFunction.toLocals parameters.reverse)
          initialWitness []
          (ConcreteFunctionBodyPost targetFunction
            (parameters ++ callerTail)
            (ExactReturnPost afterCall physical callerTail))

/-- A complete successful-execution theorem package for one generated concrete
declaration. This is the first program-level W6 boundary: it joins actual
source execution, function resolution, compiler/adaptor body correctness, and
the final runtime/value refinement facts.

The package is intentionally stronger than the public relational result:
it names the deterministic final target store and physical result, and retains
the complete terminal source runtime rather than only its lossy observation.
That exact form remains useful to cache publication and other generated
callers. -/
structure SuccessfulDeclaration
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (sourceRuntime resultRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : LCNF.Code .impure)
    (targetFunction : Wasm.Function)
    (functionIndex : Nat)
    (initial afterCall : Wasm.Store Host)
    (initialWitness resultWitness : RefinementWitness)
    (parameters : List Wasm.Value)
    (resultKind : AbiKind)
    (resultValue : Value)
    (physical : Wasm.Value) : Prop where
  sourceResult :
    SourceCodeResult context sourceExternals sourceRuntime sourceEnv sourceCode
      resultRuntime resultValue
  notImport : module.imports[functionIndex]? = none
  functionFound :
    module.funcs[functionIndex - module.imports.length]? =
      some targetFunction
  body :
    DeclarationBodyWP context sourceModule sourceFunction module hostEnv
      sourceRuntime sourceEnv sourceCode targetFunction initial afterCall
      initialWitness parameters physical
  runtimeRelated :
    ConcreteRuntimeRel afterCall.host.runtime resultWitness resultRuntime
  failureClear : afterCall.host.failure? = none
  valueRelated :
    PhysicalValueRel resultWitness resultKind physical resultValue

/-- The exact declaration result entails the existing observation-facing
source evaluation theorem. -/
theorem SuccessfulDeclaration.sourceEvaluates
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
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (correct :
      SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
        sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
        targetFunction functionIndex initial afterCall initialWitness
        resultWitness parameters resultKind resultValue physical) :
    ExecEvaluates sourceExternals
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (ReturnedObservation resultRuntime resultValue) :=
  correct.sourceResult.execEvaluates

/-- The exact body theorem yields the store-specific, fuel-free target
termination theorem used by direct calls. -/
theorem SuccessfulDeclaration.terminatesWithExact
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
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (correct :
      SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
        sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
        targetFunction functionIndex initial afterCall initialWitness
        resultWitness parameters resultKind resultValue physical)
    (callerTail : List Wasm.Value) :
    Wasm.TerminatesWith hostEnv module functionIndex initial
      (parameters ++ callerTail)
      (ExactReturnPost afterCall physical callerTail) := by
  have parameterPrefix :
      (parameters ++ callerTail).take targetFunction.numParams =
        parameters := by
    rw [← correct.body.1]
    simp
  apply CodeWP.toConcreteTerminatesWith correct.notImport correct.functionFound
  simpa [parameterPrefix] using correct.body.2.2 callerTail

/-- Public successful target theorem. It hides the chosen final representation
witness behind `RefinedReturnPost` while retaining the complete concrete
runtime and ABI-indexed result relation. -/
theorem SuccessfulDeclaration.terminatesWith
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
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (correct :
      SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
        sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
        targetFunction functionIndex initial afterCall initialWitness
        resultWitness parameters resultKind resultValue physical)
    (callerTail : List Wasm.Value) :
    Wasm.TerminatesWith hostEnv module functionIndex initial
      (parameters ++ callerTail)
      (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  rcases correct.terminatesWithExact callerTail with
    ⟨fuelBound, terminates⟩
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  obtain ⟨results, final, executed, finalEq, resultsEq⟩ :=
    terminates fuel enoughFuel
  subst final
  subst results
  exact ⟨physical :: callerTail, afterCall, executed, resultWitness, physical,
    correct.runtimeRelated, correct.failureClear, correct.valueRelated, rfl⟩

/-- The program-level successful declaration statement: the same theorem
proves both finite source execution and fuel-free concrete target execution. -/
theorem SuccessfulDeclaration.correct
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
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (certificate :
      SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
        sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
        targetFunction functionIndex initial afterCall initialWitness
        resultWitness parameters resultKind resultValue physical)
    (callerTail : List Wasm.Value) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      Wasm.TerminatesWith hostEnv module functionIndex initial
        (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) :=
  ⟨certificate.sourceEvaluates, certificate.terminatesWith callerTail⟩

/-- A nullary declaration body is exactly the proof package required by lazy
cache publication. This makes cache correctness a caller corollary of the
general declaration-body boundary. -/
theorem DeclarationBodyWP.toCachedDeclarationBodyWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {initial afterCall : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {physical : Wasm.Value}
    (body :
      DeclarationBodyWP context sourceModule sourceFunction module hostEnv
        sourceRuntime [] sourceCode targetFunction initial afterCall
        initialWitness [] physical) :
    CachedDeclarationBodyWP context sourceModule sourceFunction module hostEnv
      sourceRuntime sourceCode targetFunction initial afterCall initialWitness
      physical := by
  refine ⟨?_, body.2.1, fun callerTail => ?_⟩
  · simpa using body.1.symm
  · exact body.2.2 callerTail

/-- Existing exact cached-body proofs enter the general nullary declaration
boundary without re-proving the generated body. -/
theorem CachedDeclarationBodyWP.toDeclarationBodyWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {initial afterCall : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {physical : Wasm.Value}
    (body :
      CachedDeclarationBodyWP context sourceModule sourceFunction module
        hostEnv sourceRuntime sourceCode targetFunction initial afterCall
        initialWitness physical) :
    DeclarationBodyWP context sourceModule sourceFunction module hostEnv
      sourceRuntime [] sourceCode targetFunction initial afterCall
      initialWitness [] physical := by
  refine ⟨?_, body.2.1, fun callerTail => ?_⟩
  · simpa using body.1.symm
  · exact body.2.2 callerTail

/-- The exact body retained by a successful nullary declaration is directly
consumable by the existing lazy-cache miss/publication proof. -/
theorem SuccessfulDeclaration.cachedBody
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (correct :
      SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
        sourceExternals sourceRuntime resultRuntime [] sourceCode
        targetFunction functionIndex initial afterCall initialWitness
        resultWitness [] resultKind resultValue physical) :
    CachedDeclarationBodyWP context sourceModule sourceFunction module hostEnv
      sourceRuntime sourceCode targetFunction initial afterCall initialWitness
      physical :=
  correct.body.toCachedDeclarationBodyWP

/-- Package any existing nullary cached-body proof, exact source result, and
final refinement facts as the public successful declaration theorem. -/
theorem SuccessfulDeclaration.ofCachedBody
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {resultKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    (sourceResult :
      SourceCodeResult context sourceExternals sourceRuntime [] sourceCode
        resultRuntime resultValue)
    (notImport : module.imports[functionIndex]? = none)
    (functionFound :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction)
    (body :
      CachedDeclarationBodyWP context sourceModule sourceFunction module
        hostEnv sourceRuntime sourceCode targetFunction initial afterCall
        initialWitness physical)
    (runtimeRelated :
      ConcreteRuntimeRel afterCall.host.runtime resultWitness resultRuntime)
    (failureClear : afterCall.host.failure? = none)
    (valueRelated :
      PhysicalValueRel resultWitness resultKind physical resultValue) :
    SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
      sourceExternals sourceRuntime resultRuntime [] sourceCode targetFunction
      functionIndex initial afterCall initialWitness resultWitness []
      resultKind resultValue physical := {
  sourceResult
  notImport
  functionFound
  body := body.toDeclarationBodyWP
  runtimeRelated
  failureClear
  valueRelated }

end FirTalos.Concrete
