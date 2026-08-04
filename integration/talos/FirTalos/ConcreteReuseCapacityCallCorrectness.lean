import FirTalos.ConcreteReuseCapacityProgramCorrectness
import FirTalos.ConcreteClosureDispatch
import FirTalos.ConcreteCompilerCorrectness

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

/--
Hereditary callee theorem at the exact boundary required by the structural
facts-indexed caller proof.

The existing capacity-preserving declaration owns source/target execution,
the returned value, witness growth, and old-header transport. This stronger
package additionally states the source ordinary-token transport, immutable
host-table preservation, and a response-cost-indexed address-space budget.
All fields are uniform properties of the callee execution; callers do not
supply an execution certificate.
-/
structure BudgetedCapacityPreservingSuccessfulDeclaration
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
    (physical : Wasm.Value)
    (stepCost : Nat) : Prop
    extends ClosureTablesTransport initial afterCall initialWitness
      resultWitness where
  capacityPreserving :
    CapacityPreservingSuccessfulDeclaration context sourceModule sourceFunction
      module hostEnv sourceExternals sourceRuntime resultRuntime sourceEnv
      sourceCode targetFunction functionIndex initial afterCall initialWitness
      resultWitness parameters resultKind resultValue physical
  ordinaryTransport :
    OrdinaryPersistenceTransport sourceRuntime resultRuntime
  externalsPreserved :
    afterCall.host.externals = initial.host.externals
  residualBudget :
    ∀ {remainingBytes : Nat},
      stepCost ≤ remainingBytes →
        initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
          afterCall.host.runtime.heap.AddressSpaceBudget
            (remainingBytes - stepCost)

/--
Reinterpret a budgeted declaration result at any ABI kind refined by its
actual physical representation. Execution and all frame transports are
unchanged; only the returned value relation is weakened along
`AbiKind.refines`.
-/
theorem BudgetedCapacityPreservingSuccessfulDeclaration.ofRefines
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
    {actualKind expectedKind : AbiKind}
    {resultValue : Value}
    {physical : Wasm.Value}
    {stepCost : Nat}
    (declaration :
      BudgetedCapacityPreservingSuccessfulDeclaration context sourceModule
        sourceFunction module hostEnv sourceExternals sourceRuntime
        resultRuntime sourceEnv sourceCode targetFunction functionIndex initial
        afterCall initialWitness resultWitness parameters actualKind resultValue
        physical stepCost)
    (refines : actualKind.refines expectedKind = true) :
    BudgetedCapacityPreservingSuccessfulDeclaration context sourceModule
      sourceFunction module hostEnv sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode targetFunction functionIndex initial afterCall
      initialWitness resultWitness parameters expectedKind resultValue physical
      stepCost := by
  exact {
    declaration with
    capacityPreserving := {
      declaration.capacityPreserving with
      successful := {
        declaration.capacityPreserving.successful with
        valueRelated :=
          declaration.capacityPreserving.successful.valueRelated.ofRefines
            refines } } }

/--
Exact concrete partial-application execution plus the two hereditary frame
facts needed by a caller.

This is the allocating-result analogue of
`CapacityPreservingSuccessfulDeclaration`: it packages one concrete host
operation rather than a generated Wasm declaration.
-/
structure CapacityPreservingPartialApplication
    (initial nextStore : Wasm.Store Host)
    (beforeWitness afterWitness : RefinementWitness)
    (sourceRuntime nextRuntime : RuntimeState)
    (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind)
    (physicalArgs : List Wasm.Value)
    (sourceValue : Value) (word : Word32) : Prop where
  operation :
    partialApplyStep function arity fixed fieldKinds resultKind initial
        physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore
  runtimeRelated :
    ConcreteRuntimeRel nextStore.host.runtime afterWitness nextRuntime
  failureClear : nextStore.host.failure? = none
  valueRelated :
    PhysicalValueRel afterWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue
  witnessTransport : WitnessTransport beforeWitness afterWitness
  capacityTransport :
    HeaderCapacityTransport initial.host.runtime.heap
      nextStore.host.runtime.heap beforeWitness

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

/-- Construct the partial-application package from the concrete closure
allocator refinement. The returned witness and semantic location are exactly
the fresh bindings selected by that allocation. -/
theorem CapacityPreservingPartialApplication.ofRefines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {captures : List LaneValue}
    {semantic : Array Value} {heap : MemoryState} {address : Word32}
    {targetId descriptorId : UInt32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (resultKindSupported : resultKind = .object ∨ resultKind = .tobject)
    (fixedArgs : physicalArgs.length = fixed)
    (decoded : decodePhysicalLanes 0 fieldKinds.toList physicalArgs =
      .ok captures)
    (count : fieldKinds.size = captures.toArray.size)
    (semanticCount : semantic.size = captures.toArray.size)
    (capturesLtArity : captures.toArray.size < arity)
    (targetIdEq : closureTargetId initial.host.closureDispatch function =
      .ok targetId)
    (targetLookup :
      initial.host.closureDispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId initial.host.closureDescriptors
      fieldKinds = .ok descriptorId)
    (descriptorLookup :
      initial.host.closureDescriptors.lookup? descriptorId = some fieldKinds)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq : witness.closureDescriptors =
      initial.host.closureDescriptors)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.toArray.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      fieldKinds[index]? = some kind →
      captures.toArray[index]? = some lane →
      lane.valueType = kind.valueType)
    (captureRelated : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue)
        (value : Value),
      fieldKinds[index]? = some kind →
      captures.toArray[index]? = some lane →
      semantic[index]? = some value →
      ValueRel witness kind lane value)
    (allocated : allocateClosure initial.host.runtime.heap
      initial.host.closureDispatch initial.host.closureDescriptors function
      arity fieldKinds captures.toArray = .ok (heap, address)) :
    CapacityPreservingPartialApplication initial (replaceHeap initial heap)
      witness
      (witness.bindClosure runtime.nextLocation address function arity
        fieldKinds)
      runtime (semanticClosureResult runtime function arity semantic)
      function arity fixed fieldKinds resultKind physicalArgs
      (.object (.heap runtime.nextLocation)) address := by
  obtain ⟨extension, operation, nextRuntimeRelated, failureClear,
      valueRelated, capacityTransport, _⟩ :=
    partialApplyStep_of_capacityPreservingRefines runtimeRelated
      resultKindSupported fixedArgs decoded count semanticCount
      capturesLtArity targetIdEq targetLookup descriptorIdEq descriptorLookup
      dispatchEq descriptorsEq arityFits fixedFits captureTyped captureRelated
      allocated
  exact ⟨operation, nextRuntimeRelated, failureClear, valueRelated,
    WitnessTransport.ofExtension extension, by
      simpa [replaceHeap, clearFailure] using capacityTransport⟩

/-- Direct `.pap` result adapter. The ordinary source/target step supplies
execution and binding; the partial-application package supplies the two frame
facts required to erase the destination's stale capacity evidence. -/
theorem ReuseCapacityLetStepSimulates.ofPartialApplication
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : LCNF.LetDecl .impure} {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {word : Word32}
    (initialRelated :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some nextLocals)
    (partialResult :
      CapacityPreservingPartialApplication targetStore nextStore beforeWitness
        afterWitness sourceRuntime nextRuntime function arity fixed fieldKinds
        resultKind physicalArgs sourceValue word) :
    ReuseCapacityLetStepSimulates facts
      (eraseReuseCapacityFact facts decl.fvarId) context sourceFunction module
      hostEnv decl targetValue sourceRuntime nextRuntime sourceEnv sourceValue
      targetStore nextStore targetLocals nextLocals resultIndex beforeWitness
      afterWitness :=
  ReuseCapacityResultStep.ofErase step initialRelated step.2.2.1 resultFound
    (localUpdate_of_set? targetSet) partialResult.witnessTransport
    partialResult.capacityTransport

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
    {calleeContext : Fir.Wasm.Context}
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
      CapacityPreservingSuccessfulDeclaration calleeContext sourceModule
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
Reconstruct the exact canonical caller frame from any already-proved
interprocedural result step and its hereditary callee package.

Direct named calls and saturated closure dispatch differ only in how they
establish `capacityStep`. Once that executable step is known, the
ordinary-token, local-capacity, address-space, external-table, and descriptor
arguments are identical. Factoring them here prevents the closure path from
duplicating or weakening the direct-call frame theorem.
-/
theorem
    ConcreteReuseCapacityPureExternalOwnershipFrame.ofBudgetedCallStepExact
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv calleeEnv : Env}
    {calleeCode : LCNF.Code .impure}
    {sourceValue : Value}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {initial afterCall : Wasm.Store Host}
    {locals updated : Wasm.Locals}
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness resultWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value}
    (invariant :
      ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
    (capacityStep :
      ReuseCapacityCallLetStepSimulates facts
        (eraseReuseCapacityFact facts decl.fvarId) context callerFunction module
        hostEnv sourceExternals decl continuation targetValue sourceRuntime
        nextRuntime sourceEnv sourceValue initial afterCall locals updated
        resultIndex initialWitness resultWitness)
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclaration calleeContext sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime nextRuntime
        calleeEnv calleeCode targetFunction functionIndex initial afterCall
        initialWitness resultWitness parameters resultKind sourceValue physical
        stepCost)
    (targetSet :
      locals.set? resultIndex physical = some updated)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    CallLetStepSimulates context callerFunction module hostEnv sourceExternals
          decl continuation targetValue sourceRuntime nextRuntime sourceEnv
          sourceValue initial afterCall locals updated resultIndex
          initialWitness resultWitness ∧
      afterCall.host.externals = initial.host.externals ∧
        afterCall.host.closureDescriptors =
            initial.host.closureDescriptors ∧
          resultWitness.closureDescriptors =
              initialWitness.closureDescriptors ∧
            reuseCapacityLetFacts? facts decl =
                some (eraseReuseCapacityFact facts decl.fvarId) ∧
              ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
                sourceExternals (eraseReuseCapacityFact facts decl.fvarId)
                (remainingBytes - stepCost) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) afterCall updated
                resultWitness := by
  rcases invariant with
    ⟨⟨⟨initialRelated, ordinaryTokens, frameAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩
  have nextOrdinary :
      ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts decl.fvarId)
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) := by
    simpa using ordinaryTokens.eraseBind callee.ordinaryTransport
  have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
  have nextFrameAligned :
      ConcreteLocalFrameAligned callerFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) afterCall updated
        resultWitness :=
    ⟨lengths.1.trans frameAligned.1, lengths.2.trans frameAligned.2⟩
  have nextBudget :
      afterCall.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - stepCost) :=
    callee.residualBudget stepFits budget
  have nextDescriptorAgreement :
      afterCall.host.closureDescriptors =
        resultWitness.closureDescriptors :=
    callee.hostDescriptorsPreserved.trans
      (descriptorAgreement.trans callee.witnessDescriptorsPreserved.symm)
  exact ⟨capacityStep.ordinary, callee.externalsPreserved,
    callee.hostDescriptorsPreserved, callee.witnessDescriptorsPreserved,
    transfer,
    ⟨⟨⟨capacityStep.nextRelated, nextOrdinary, nextFrameAligned, nextBudget⟩,
      by rw [callee.externalsPreserved]; exact integerImplementation,
      by rw [callee.externalsPreserved]; exact naturalImplementation,
      by rw [callee.externalsPreserved]; exact scalarImplementation⟩,
      nextDescriptorAgreement⟩⟩

/--
One direct declaration call reconstructs the canonical caller frame at its
exact callee post-store and representation witness.

The older existential adapter remains as a convenient runtime-law view. This
endpoint-exact form is the compositional boundary needed by cache-aware and
fixed-entry proofs, which must thread the callee's own evolved state rather
than an opaque existentially equivalent successor.
-/
theorem
    ConcreteReuseCapacityPureExternalOwnershipFrame.ofDirectDeclarationCallExact
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
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
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness resultWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value}
    (invariant :
      ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
    (sourceStep :
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
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
      BudgetedCapacityPreservingSuccessfulDeclaration calleeContext sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime nextRuntime
        calleeEnv calleeCode targetFunction functionIndex initial afterCall
        initialWitness resultWitness physicalArgs.reverse resultKind sourceValue
        physical stepCost)
    (targetSet :
      locals.set? resultIndex physical = some updated)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    CallLetStepSimulates context callerFunction module hostEnv sourceExternals
          decl continuation (argumentTarget ++ [.call functionIndex])
          sourceRuntime nextRuntime sourceEnv sourceValue initial afterCall
          locals updated resultIndex initialWitness resultWitness ∧
      afterCall.host.externals = initial.host.externals ∧
        afterCall.host.closureDescriptors =
            initial.host.closureDescriptors ∧
          resultWitness.closureDescriptors =
              initialWitness.closureDescriptors ∧
            reuseCapacityLetFacts? facts decl =
                some (eraseReuseCapacityFact facts decl.fvarId) ∧
              ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
                sourceExternals (eraseReuseCapacityFact facts decl.fvarId)
                (remainingBytes - stepCost) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) afterCall updated
                resultWitness := by
  rcases invariant with
    ⟨⟨⟨initialRelated, ordinaryTokens, frameAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩
  have capacityStep :
      ReuseCapacityCallLetStepSimulates facts
        (eraseReuseCapacityFact facts decl.fvarId) context callerFunction module
        hostEnv sourceExternals decl continuation
        (argumentTarget ++ [.call functionIndex]) sourceRuntime nextRuntime
        sourceEnv sourceValue initial afterCall locals updated resultIndex
        initialWitness resultWitness :=
    ReuseCapacityCallLetStepSimulates.ofDirectDeclaration sourceStep
      initialRelated resultFound resultKindAt assembled
      callee.capacityPreserving targetSet
  have nextOrdinary :
      ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts decl.fvarId)
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) := by
    simpa using ordinaryTokens.eraseBind callee.ordinaryTransport
  have lengths := FirTalos.Correctness.locals_lengths_of_set? targetSet
  have nextFrameAligned :
      ConcreteLocalFrameAligned callerFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) afterCall updated
        resultWitness :=
    ⟨lengths.1.trans frameAligned.1, lengths.2.trans frameAligned.2⟩
  have nextBudget :
      afterCall.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - stepCost) :=
    callee.residualBudget stepFits budget
  have nextDescriptorAgreement :
      afterCall.host.closureDescriptors =
        resultWitness.closureDescriptors :=
    callee.hostDescriptorsPreserved.trans
      (descriptorAgreement.trans callee.witnessDescriptorsPreserved.symm)
  exact ⟨capacityStep.ordinary, callee.externalsPreserved,
    callee.hostDescriptorsPreserved, callee.witnessDescriptorsPreserved,
    transfer,
    ⟨⟨⟨capacityStep.nextRelated, nextOrdinary, nextFrameAligned, nextBudget⟩,
      by rw [callee.externalsPreserved]; exact integerImplementation,
      by rw [callee.externalsPreserved]; exact naturalImplementation,
      by rw [callee.externalsPreserved]; exact scalarImplementation⟩,
      nextDescriptorAgreement⟩⟩

/--
One direct generated declaration call re-establishes the canonical structural
frame used by the certificate-free compiler theorem.

The caller contributes only its current frame and compiler-derived argument
assembly/local slot. The hereditary callee theorem supplies execution and all
cross-call transports; the validator's ordinary result transfer erases only
the destination fact.
-/
theorem
    ConcreteReuseCapacityPureExternalOwnershipFrame.ofDirectDeclarationCall
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
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
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness resultWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value}
    (invariant :
      ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
    (sourceStep :
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
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
      BudgetedCapacityPreservingSuccessfulDeclaration calleeContext sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime nextRuntime
        calleeEnv calleeCode targetFunction functionIndex initial afterCall
        initialWitness resultWitness physicalArgs.reverse resultKind sourceValue
        physical stepCost)
    (targetSet :
      locals.set? resultIndex physical = some updated)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    ∃ nextStore nextLocals nextWitness nextFacts,
      CallLetStepSimulates context callerFunction module hostEnv sourceExternals
          decl continuation (argumentTarget ++ [.call functionIndex])
          sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
          locals nextLocals resultIndex initialWitness nextWitness ∧
        nextStore.host.externals = initial.host.externals ∧
          nextStore.host.closureDescriptors =
              initial.host.closureDescriptors ∧
            nextWitness.closureDescriptors =
                initialWitness.closureDescriptors ∧
              reuseCapacityLetFacts? facts decl = some nextFacts ∧
              ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
                  sourceExternals nextFacts (remainingBytes - stepCost)
                  nextRuntime (bind sourceEnv decl.fvarId sourceValue)
                  nextStore nextLocals nextWitness := by
  obtain ⟨step, externalsPreserved, hostDescriptorsPreserved,
      witnessDescriptorsPreserved, nextTransfer, nextInvariant⟩ :=
    invariant.ofDirectDeclarationCallExact stepFits sourceStep resultFound
      resultKindAt assembled callee targetSet transfer
  exact ⟨afterCall, updated, resultWitness,
    eraseReuseCapacityFact facts decl.fvarId, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextTransfer,
    nextInvariant⟩

/--
Uniform implementation condition for source calls that compile to direct
generated declaration calls.

This theorem condition isolates the genuinely interprocedural obligation. It
must derive the production argument/call prefix and callee result from source
admission, executable compiler output, adapter output, and the caller state
relation. The conclusion is a budgeted hereditary callee theorem, not a
program-specific execution certificate.
-/
def DirectDeclarationCallImplementation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (CallSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {valueCode : List Fir.Wasm.Instruction}
      {targetValue : Wasm.Program}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {resultIndex stepCost : Nat}
      {initialWitness : RefinementWitness},
    CallSupported sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue →
      ReuseCapacityStateRelated facts callerFunction sourceRuntime sourceEnv
        initial locals initialWitness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule callerFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex →
      ∃ calleeContext : Fir.Wasm.Context,
        ∃ calleeFunction calleeEnv calleeCode targetFunction functionIndex
          argumentTarget afterCall updated resultWitness physicalArgs
          resultKind physical,
        targetValue = argumentTarget ++ [.call functionIndex] ∧
          (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
            some resultKind ∧
          ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
            initial locals ∧
          BudgetedCapacityPreservingSuccessfulDeclaration calleeContext
            sourceModule calleeFunction module hostEnv sourceExternals sourceRuntime
            nextRuntime calleeEnv calleeCode targetFunction functionIndex
            initial afterCall initialWitness resultWitness physicalArgs.reverse
            resultKind sourceValue physical stepCost ∧
          locals.set? resultIndex physical = some updated ∧
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId)

/--
A uniform direct-declaration implementation theorem instantiates the generic
facts-indexed call law for the canonical mixed frame.

The proof merely connects compiler/callee selection to
`ofDirectDeclarationCall`; all resource reconstruction remains in that common
adapter.
-/
theorem DirectDeclarationCallImplementation.runtimeRefines
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {CallSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    (implementation :
      DirectDeclarationCallImplementation context sourceModule callerFunction
        labels module hostEnv sourceExternals CallSupported) :
    ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
      callerFunction labels module hostEnv sourceExternals CallSupported
      (ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction
        sourceExternals) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue initial locals resultIndex remainingBytes stepCost
    initialWitness supported stepFits invariant sourceStep valueCompiled
    valueAdapted resultFound
  obtain ⟨calleeContext, calleeFunction, calleeEnv, calleeCode, targetFunction,
      functionIndex, argumentTarget, afterCall, updated, resultWitness,
      physicalArgs, resultKind, physical, targetEq, resultKindAt, assembled,
      callee, targetSet, transfer⟩ :=
    implementation supported sourceStep invariant.1.1.1 valueCompiled
      valueAdapted resultFound
  subst targetValue
  exact invariant.ofDirectDeclarationCall stepFits sourceStep resultFound
    resultKindAt assembled callee targetSet transfer

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
    {calleeContext : Fir.Wasm.Context}
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
    (selectedStore : selected.nextStore = initial)
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (selectedBodyEq :
      selected.targetBody =
        argumentTarget ++ [.call functionIndex, .localSet resultIndex])
    (callee :
      CapacityPreservingSuccessfulDeclaration calleeContext sourceModule
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
        selectedMatches (by simpa [selectedStore] using selectedBody)

/--
The underapplication sibling of `ofSaturatedClosureDeclaration`.

The selected candidate allocates a fresh partial-application closure through
the concrete host instead of entering a generated declaration. Its
`CapacityPreservingPartialApplication` package supplies the exact final
runtime/value relation and both hereditary frame transports; the surrounding
matcher chain and result-local protocol are unchanged.
-/
theorem ReuseCapacityCallLetStepSimulates.ofUnderappliedClosure
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env} {sourceValue : Value}
    {initial nextStore : Wasm.Store Host}
    {locals updated : Wasm.Locals}
    {resultIndex closureIndex partialApplyIndex : Nat}
    {closureId : FVarId} {closureAddress : Word32}
    {beforeWitness afterWitness : RefinementWitness}
    {argumentTarget : Wasm.Program}
    {physicalArgs : List Wasm.Value}
    {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {word : Word32} {imp : Wasm.ImportDecl}
    (before : List
      (ClosureCandidateCase sourceModule callerFunction labels module spec
        initial closureId closureIndex closureAddress))
    (selected :
      ClosureCandidateCase sourceModule callerFunction labels module spec
        initial closureId closureIndex closureAddress)
    (suffix : List
      (ClosureCandidateCase sourceModule callerFunction labels module spec
        initial closureId closureIndex closureAddress))
    (sourceStep :
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (initialRelated :
      ReuseCapacityStateRelated facts callerFunction sourceRuntime sourceEnv
        initial locals beforeWitness)
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hClosure :
      locals.get closureIndex =
        some (.i32 (UInt32.ofNat closureAddress.value)))
    (hSat : hostEnv.Satisfies module spec)
    (beforeNonmatching :
      ∀ candidate, candidate ∈ before →
        candidate.matched = (0 : UInt32))
    (selectedMatches : (selected.matched != 0) = true)
    (selectedStore : selected.nextStore = initial)
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (selectedBodyEq :
      selected.targetBody =
        argumentTarget ++
          [.call partialApplyIndex, .localSet resultIndex])
    (hImp : module.imports[partialApplyIndex]? = some imp)
    (hi : partialApplyIndex < module.imports.length)
    (hContract : spec.contracts[partialApplyIndex]? =
      some (partialApplyContract function arity fixed fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (partialResult :
      CapacityPreservingPartialApplication initial nextStore beforeWitness
        afterWitness sourceRuntime nextRuntime function arity fixed fieldKinds
        resultKind physicalArgs sourceValue word)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some updated) :
    ReuseCapacityCallLetStepSimulates facts
      (eraseReuseCapacityFact facts decl.fvarId) context callerFunction module
      hostEnv sourceExternals decl continuation
      (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
        [.localGet resultIndex])
      sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore locals
      updated resultIndex beforeWitness afterWitness := by
  refine ReuseCapacityCallLetStepSimulates.ofErase initialRelated ?_
    resultFound (localUpdate_of_set? targetSet) partialResult.witnessTransport
    partialResult.capacityTransport
  refine ⟨sourceStep, initialRelated.stateRelated, ?_, ?_⟩
  · exact initialRelated.stateRelated.bindAfterTransport
      partialResult.witnessTransport partialResult.runtimeRelated
      partialResult.failureClear resultFound resultKindAt
      partialResult.valueRelated targetSet
  · intro rest Q tail continued
    have selectedBody :
        Wasm.wp module selected.targetBody
          (closureDispatchSelectedPost module hostEnv tail before.length
            (.localGet resultIndex :: .localSet resultIndex :: rest) Q)
          initial { locals with values := tail } hostEnv := by
      rw [selectedBodyEq]
      apply wp_partialApplyBody_of_assembly assembled hImp hSat hi hContract
        hParams hResults partialResult.operation targetSet
      apply (Wasm.wp_nil).2
      apply closureDispatchSelectedPost_fallthrough before.length
      exact wp_closureDispatchResult targetSet continued
    simpa [List.append_assoc] using
      wp_compileClosureDispatch_of_selected before selected suffix
        (.localSet resultIndex :: rest) Q hClosure hSat
        initialRelated.stateRelated.clearFailure beforeNonmatching
        selectedMatches (by simpa [selectedStore] using selectedBody)

/-- Recursive certificate node for the same direct declaration-call boundary.
The continuation starts under the validator's ordinary-result erasure
transfer, while the callee frame theorem preserves every differently named
caller fact. -/
theorem ReuseCapacityCodeSimulation.callLetOfDirectDeclaration
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
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
      CapacityPreservingSuccessfulDeclaration calleeContext sourceModule
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
theorem ReuseCapacityCodeSimulation.callLetOfSelectedClosureDispatch
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
        compileClosureCandidatesForTarget context.program decl.fvarId closureId
          callResultKind argumentCode argumentKinds target) =
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
