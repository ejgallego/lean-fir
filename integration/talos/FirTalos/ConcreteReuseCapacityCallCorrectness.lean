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

/-- Repeating the same checked local write is an identity. Closure dispatch
stores the selected result inside the candidate body and then reloads it for
the enclosing `let`, whose ordinary lowering stores it once more. -/
theorem localsSet?_idempotent
    {before after : Wasm.Locals} {index : Nat} {value : Wasm.Value}
    (updated : before.set? index value = some after) :
    after.set? index value = some after := by
  unfold Wasm.Locals.set? at updated ⊢
  split at updated
  · rename_i inParams
    cases updated
    simp [inParams, List.set_set]
  · rename_i notInParams
    split at updated
    · rename_i inLocals
      cases updated
      simp [notInParams, inLocals, List.set_set]
    · simp_all

/-- A selected closure candidate may sit below any number of preceding
nonmatching candidate branches. Normal fallthrough through those empty
resumption layers reaches the same surrounding suffix. -/
theorem closureDispatchSelectedPost_fallthrough
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    {Q : Wasm.Assertion Host}
    (depth : Nat)
    (continued :
      Wasm.wp module rest Q store { locals with values := tail } hostEnv) :
    closureDispatchSelectedPost module hostEnv tail depth rest Q
      (.Fallthrough store { locals with values := tail }) := by
  induction depth generalizing rest Q with
  | zero =>
      simpa [closureDispatchSelectedPost, closureDispatchResumePost] using
        continued
  | succ depth ih =>
      change closureDispatchSelectedPost module hostEnv tail depth []
        (closureDispatchResumePost module hostEnv rest Q tail)
        (.Fallthrough store { locals with values := tail })
      apply ih
      simpa [closureDispatchResumePost] using continued

/-- The dispatch-local reload and enclosing `let` store are observationally
one local write: the second write is checked and idempotent. -/
theorem wp_closureDispatchResult
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {before after : Wasm.Locals}
    {resultIndex : Nat} {physical : Wasm.Value}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    {Q : Wasm.Assertion Host}
    (targetSet : before.set? resultIndex physical = some after)
    (continued :
      Wasm.wp module rest Q store { after with values := tail } hostEnv) :
    Wasm.wp module
      (.localGet resultIndex :: .localSet resultIndex :: rest)
      Q store { after with values := tail } hostEnv := by
  have resultRead := (localUpdate_of_set? targetSet).1
  have resultReadWithStack :
      ({ after with values := tail } : Wasm.Locals).get resultIndex =
        some physical := by
    simpa [Wasm.Locals.get] using resultRead
  apply (Wasm.wp_localGet_cons).2
  rw [resultReadWithStack]
  exact wp_localSet_of_set (locals := after) (updated := after)
    (localsSet?_idempotent targetSet) continued

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

/--
A saturated selected closure candidate has the same hereditary call boundary
as a source-level named call. Matcher calls and capture projections execute in
the unchanged entry store; the selected ordinary Wasm declaration call uses
the callee frame theorem. The candidate-local result write followed by the
dispatch reload and enclosing `let` write is discharged by
`wp_closureDispatchResult`.
-/
theorem ReuseCapacityCallLetStepSimulates.ofSaturatedClosureDeclaration
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv calleeEnv : Env}
    {calleeCode : LCNF.Code .impure}
    {sourceValue : Value}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {locals updated : Wasm.Locals}
    {resultIndex closureIndex : Nat}
    {closureId : FVarId} {address : Word32}
    {initialWitness resultWitness : RefinementWitness}
    {argumentTarget : Wasm.Program}
    {physicalArgs : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value}
    (before : List
      (ClosureCandidateCase sourceModule callerFunction labels module spec
        initial closureId closureIndex address))
    (selected :
      ClosureCandidateCase sourceModule callerFunction labels module spec
        initial closureId closureIndex address)
    (suffix : List
      (ClosureCandidateCase sourceModule callerFunction labels module spec
        initial closureId closureIndex address))
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
    (hClosure :
      locals.get closureIndex =
        some (.i32 (UInt32.ofNat address.value)))
    (hSat : hostEnv.Satisfies module spec)
    (beforeNonmatching :
      ∀ candidate, candidate ∈ before →
        candidate.matched = (0 : UInt32))
    (selectedMatches : (selected.matched != 0) = true)
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (selectedBodyEq :
      selected.targetBody =
        argumentTarget ++ [.call functionIndex, .localSet resultIndex])
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
      (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
        [.localGet resultIndex])
      sourceRuntime nextRuntime sourceEnv sourceValue initial afterCall locals
      updated resultIndex initialWitness resultWitness := by
  refine ReuseCapacityCallLetStepSimulates.ofErase initialRelated ?_
    resultFound (localUpdate_of_set? targetSet) callee.witnessTransport
    callee.capacityTransport
  refine ⟨sourceStep, initialRelated.stateRelated, ?_, ?_⟩
  · exact initialRelated.stateRelated.bindAfterTransport
      callee.witnessTransport callee.successful.runtimeRelated
      callee.successful.failureClear resultFound resultKindAt
      callee.successful.valueRelated targetSet
  · intro rest Q tail continued
    have selectedBody :
        Wasm.wp module selected.targetBody
          (closureDispatchSelectedPost module hostEnv tail before.length
            (.localGet resultIndex :: .localSet resultIndex :: rest) Q)
          initial { locals with values := tail } hostEnv := by
      rw [selectedBodyEq]
      apply wp_directCallBody_of_assembly assembled
        (callee.successful.terminatesWithExact tail) targetSet
      apply (Wasm.wp_nil).2
      apply closureDispatchSelectedPost_fallthrough before.length
      exact wp_closureDispatchResult targetSet continued
    simpa [List.append_assoc] using
      wp_compileClosureDispatch_of_selected before selected suffix
        (.localSet resultIndex :: rest) Q hClosure hSat
        initialRelated.stateRelated.clearFailure beforeNonmatching
        selectedMatches selectedBody

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

/-- Insert an already-proved saturated closure call into the recursive
certificate while deriving its exact numeric dispatch adaptation from the
compiler candidate list. -/
theorem ReuseCapacityCodeSimulation.callLetOfSaturatedClosureDispatch
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {valueCode argumentCode : List Fir.Wasm.Instruction}
    {argumentKinds : Array AbiKind}
    {targetRest : Wasm.Program}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue resultValue : Value}
    {initial afterCall resultStore : Wasm.Store Host}
    {locals updated : Wasm.Locals}
    {resultIndex closureIndex : Nat}
    {closureId : FVarId} {address : Word32}
    {initialWitness callWitness resultWitness : RefinementWitness}
    {callResultKind resultKind : AbiKind}
    {physical : Wasm.Value}
    (before : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (selected :
      ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)
    (suffix : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (safe :
      reuseCapacitySafeCode facts (.let decl continuation) = true)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId))
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (dispatchCompiled :
      valueCode =
        compileClosureDispatch context decl.fvarId closureId callResultKind
          argumentCode argumentKinds)
    (candidatesEq :
      context.program.decls.toList.flatMap (fun target =>
        compileClosureCandidatesForTarget decl.fvarId closureId callResultKind
          argumentCode argumentKinds target) =
        (before ++ selected :: suffix).map (·.source))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (step :
      ReuseCapacityCallLetStepSimulates facts
        (eraseReuseCapacityFact facts decl.fvarId) context sourceFunction module
        hostEnv sourceExternals decl continuation
        (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
          [.localGet resultIndex])
        sourceRuntime nextRuntime sourceEnv sourceValue initial afterCall locals
        updated resultIndex initialWitness callWitness)
    (continued :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals
        (eraseReuseCapacityFact facts decl.fvarId) nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        afterCall updated callWitness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical) :
    ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
      module hostEnv sourceExternals facts sourceRuntime sourceEnv
      (.let decl continuation)
      ((resolvedClosureCandidateChain (before ++ selected :: suffix) ++
          [.localGet resultIndex]) ++
        .localSet resultIndex :: targetRest)
      initial locals initialWitness resultFacts resultRuntime resultValue
      resultKind resultStore resultWitness physical := by
  apply ReuseCapacityCodeSimulation.callLet safe transfer valueCompiled
      _ resultFound step continued
  subst valueCode
  exact instructions_compileClosureDispatch (before ++ selected :: suffix)
    candidatesEq closureFound resultFound

end FirTalos.Concrete
