import FirTalos.ConcreteReuseCapacityProgramCorrectness
import FirTalos.ConcreteClosureDispatch

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
Successful declaration execution with the two frame facts required by an
arbitrary caller's retained-capacity map.

`SuccessfulDeclaration` already owns source evaluation, target termination,
the final runtime relation, and the returned physical value. This wrapper adds
only the proof-only representation and heap transports from entry to exit.
-/
structure CapacityPreservingSuccessfulDeclaration
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
  successful :
    SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
      sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
      targetFunction functionIndex initial afterCall initialWitness
      resultWitness parameters resultKind resultValue physical
  witnessTransport : WitnessTransport initialWitness resultWitness
  capacityTransport :
    HeaderCapacityTransport initial.host.runtime.heap
      afterCall.host.runtime.heap initialWitness

/-- A complete capacity-aware body certificate supplies the two hereditary
frame fields required by callers; no separate per-declaration heap proof is
needed. -/
theorem CapacityPreservingSuccessfulDeclaration.ofSimulation
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env} {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind} {resultValue : Value} {physical : Wasm.Value}
    (successful :
      SuccessfulDeclaration context sourceModule sourceFunction module hostEnv
        sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
        targetFunction functionIndex initial afterCall initialWitness
        resultWitness parameters resultKind resultValue physical)
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv sourceCode
        targetFunction.body initial targetLocals initialWitness resultFacts
        resultRuntime resultValue resultKind afterCall resultWitness physical) :
    CapacityPreservingSuccessfulDeclaration context sourceModule sourceFunction
      module hostEnv sourceExternals sourceRuntime resultRuntime sourceEnv
      sourceCode targetFunction functionIndex initial afterCall initialWitness
      resultWitness parameters resultKind resultValue physical := by
  have frame := simulation.frameTransport
  exact ⟨successful, frame.1, frame.2⟩

/--
First concrete interprocedural capacity theorem: a direct generated
declaration call preserves the caller's validator facts.

The argument assembly and exact declaration certificate reconstruct the
ordinary `CallLetStepSimulates` theorem. The capacity wrapper then supplies
the checked caller-local write plus the two frame transports required by
`ReuseCapacityCallLetStepSimulates.ofErase`.
-/
theorem ReuseCapacityCallLetStepSimulates.ofDirectDeclaration
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {argumentTarget : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv calleeEnv : Env}
    {calleeCode : LCNF.Code .impure}
    {sourceValue : Value}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {locals updated : Wasm.Locals}
    {resultIndex : Nat}
    {initialWitness resultWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value}
    (sourceStep :
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (initialRelated :
      ReuseCapacityStateRelated facts callerFunction sourceRuntime sourceEnv
        initial locals initialWitness)
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (callee :
      CapacityPreservingSuccessfulDeclaration context sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime nextRuntime
        calleeEnv calleeCode targetFunction functionIndex initial afterCall
        initialWitness resultWitness physicalArgs.reverse resultKind sourceValue
        physical)
    (targetSet :
      locals.set? resultIndex physical = some updated) :
    ReuseCapacityCallLetStepSimulates facts
      (eraseReuseCapacityFact facts decl.fvarId) context callerFunction module
      hostEnv sourceExternals decl continuation
      (argumentTarget ++ [.call functionIndex]) sourceRuntime nextRuntime
      sourceEnv sourceValue initial afterCall locals updated resultIndex
      initialWitness resultWitness := by
  refine ReuseCapacityCallLetStepSimulates.ofErase initialRelated ?_
    resultFound (localUpdate_of_set? targetSet) callee.witnessTransport
    callee.capacityTransport
  refine ⟨sourceStep, initialRelated.stateRelated, ?_, ?_⟩
  · exact initialRelated.stateRelated.bindAfterTransport
      callee.witnessTransport callee.successful.runtimeRelated
      callee.successful.failureClear resultFound resultKindAt
      callee.successful.valueRelated targetSet
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_directCallBody_of_assembly assembled
        (callee.successful.terminatesWithExact tail) targetSet continued

/-- Recursive certificate node for the same direct declaration-call boundary.
The continuation starts under the validator's ordinary-result erasure
transfer, while the callee frame theorem preserves every differently named
caller fact. -/
theorem ReuseCapacityCodeSimulation.callLetOfDirectDeclaration
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {argumentTarget targetRest : Wasm.Program}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState}
    {sourceEnv calleeEnv : Env}
    {calleeCode : LCNF.Code .impure}
    {sourceValue resultValue : Value}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {initial afterCall resultStore : Wasm.Store Host}
    {locals updated : Wasm.Locals}
    {resultIndex : Nat}
    {initialWitness callWitness resultWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {callResultKind resultKind : AbiKind}
    {callPhysical physical : Wasm.Value}
    (safe :
      reuseCapacitySafeCode facts (.let decl continuation) = true)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId))
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule callerFunction labels valueCode =
        .ok (argumentTarget ++ [.call functionIndex]))
    (sourceStep :
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (initialRelated :
      ReuseCapacityStateRelated facts callerFunction sourceRuntime sourceEnv
        initial locals initialWitness)
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some callResultKind)
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (callee :
      CapacityPreservingSuccessfulDeclaration context sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime nextRuntime
        calleeEnv calleeCode targetFunction functionIndex initial afterCall
        initialWitness callWitness physicalArgs.reverse callResultKind
        sourceValue callPhysical)
    (targetSet :
      locals.set? resultIndex callPhysical = some updated)
    (continued :
      ReuseCapacityCodeSimulation context sourceModule callerFunction labels
        module hostEnv sourceExternals
        (eraseReuseCapacityFact facts decl.fvarId) nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        afterCall updated callWitness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical) :
    ReuseCapacityCodeSimulation context sourceModule callerFunction labels
      module hostEnv sourceExternals facts sourceRuntime sourceEnv
      (.let decl continuation)
      ((argumentTarget ++ [.call functionIndex]) ++
        .localSet resultIndex :: targetRest)
      initial locals initialWitness resultFacts resultRuntime resultValue
      resultKind resultStore resultWitness physical :=
  .callLet safe transfer valueCompiled valueAdapted resultFound
    (ReuseCapacityCallLetStepSimulates.ofDirectDeclaration sourceStep
      initialRelated resultFound resultKindAt assembled callee targetSet)
    continued

end FirTalos.Concrete
