import FirTalos.ConcreteRuntime
import FirTalos.ConcreteResidentPrimitives

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-!
# Resident-helper replacement boundary

These lemmas isolate the only control-flow difference between a host-backed
external call and a Wasm-resident helper: the generated argument prefix is
unchanged, but the call is justified by a defined-function execution theorem
rather than an import contract.  Operation-specific proofs supply the helper
result and the post-state relation; compiler simulation then resumes through
the same checked destination write.
-/

namespace ResidentReplacement

/-- A compiler-derived argument prefix, a terminating defined helper call,
and a checked result-local write compose with any continuation. -/
theorem wp_defined_ready_let
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {functionIndex resultIndex : Nat}
    {initial nextStore : Wasm.Store host}
    {locals updated : Wasm.Locals}
    {targetArguments rest : Wasm.Program}
    {physicalArgs : List Wasm.Value} {physicalResult : Wasm.Value}
    {Q : Wasm.Assertion host} {tail : List Wasm.Value}
    (ready : ConstructorArgsReady locals targetArguments physicalArgs)
    (callRun :
      Wasm.TerminatesWith env module functionIndex initial
        (physicalArgs.reverse ++ tail)
        (fun final values =>
          final = nextStore ∧ values = physicalResult :: tail))
    (targetSet : locals.set? resultIndex physicalResult = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (targetArguments ++ .call functionIndex :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply ready.wp
  exact ResidentPrimitives.wp_definedCallResultSet callRun targetSet continued

/-- Generic simulation-preservation rule for replacing one external import by
a defined resident helper.  It stores neither a target path nor a translation
certificate: the caller supplies the ordinary source step, the helper's
fuel-free execution theorem, and the resulting state relation. -/
theorem externalLetStepSimulates_of_definedCall
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceRuntime nextRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {sourceValue : Fir.LeanIR.Impure.Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {targetArguments : Wasm.Program} {physicalArgs : List Wasm.Value}
    {physicalResult : Wasm.Value} {functionIndex resultIndex : Nat}
    {witness nextWitness : Fir.Wasm.Concrete.RefinementWitness}
    (sourceStep : SourceExternalLetResult context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness)
    (nextRelated : StateRelated sourceFunction nextRuntime
      (Fir.LeanIR.Impure.bind sourceEnv decl.fvarId sourceValue)
      nextStore nextLocals nextWitness)
    (ready :
      ConstructorArgsReady targetLocals targetArguments physicalArgs)
    (callRun : ∀ tail,
      Wasm.TerminatesWith hostEnv module functionIndex targetStore
        (physicalArgs.reverse ++ tail)
        (fun final values =>
          final = nextStore ∧ values = physicalResult :: tail))
    (targetSet :
      targetLocals.set? resultIndex physicalResult = some nextLocals) :
    ExternalLetStepSimulates context sourceFunction module hostEnv externals
      decl continuation (targetArguments ++ [.call functionIndex])
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex witness nextWitness := by
  refine ⟨sourceStep, initialRelated, nextRelated, ?_⟩
  intro rest Q tail continued
  simpa [List.append_assoc] using
    wp_defined_ready_let ready (callRun tail) targetSet continued

end ResidentReplacement

end FirTalos.Concrete
