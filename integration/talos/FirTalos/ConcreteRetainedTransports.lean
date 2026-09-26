import FirTalos.ConcreteArrayPublication

/-! A proof-local replacement for blanket ordinary-persistence transport.
Only token facts represented at entry need survive a callee. The universal
quantification below includes arbitrary older callers through witness transport;
it is not a caller-supplied list, source invariant or execution certificate.
The structured small-step resource stack uses this package; legacy
whole-declaration proofs retain their stronger ordinary-persistence interface.
-/

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Preserve any saved token facts whose representation survives to entry.
Fresh objects allocated later may become persistent. This condition says
nothing about target execution, liveness or arbitrary source programs. -/
def RetainedCallerTransport (entryWitness : RefinementWitness)
    (before after : RuntimeState) : Prop :=
  ∀ {facts : ReuseCapacityFacts} {bindings : List (FVarId × AbiKind)}
    {env : Env} {locals : Wasm.Locals} {savedHeap : MemoryState}
    {savedWitness : RefinementWitness},
    ReuseCapacityFactsRel facts bindings env locals savedHeap savedWitness →
    WitnessTransport savedWitness entryWitness →
    ReuseTokenOrdinaryTransport facts env before after

theorem RetainedCallerTransport.refl (witness : RefinementWitness)
    (runtime : RuntimeState) : RetainedCallerTransport witness runtime runtime :=
  fun _ _ => ReuseTokenOrdinaryTransport.refl _ _ _

theorem RetainedCallerTransport.ofOrdinary
    {witness : RefinementWitness} {before after : RuntimeState}
    (ordinary : OrdinaryPersistenceTransport before after) :
    RetainedCallerTransport witness before after :=
  fun _ _ => .ofOrdinaryPersistence ordinary

/-- Compose at an exact call boundary. Older saved facts are carried to the
inner entry by representation transport, not by replacing their environment. -/
theorem RetainedCallerTransport.trans
    {firstWitness middleWitness : RefinementWitness}
    {first middle last : RuntimeState}
    (left : RetainedCallerTransport firstWitness first middle)
    (witness : WitnessTransport firstWitness middleWitness)
    (right : RetainedCallerTransport middleWitness middle last) :
    RetainedCallerTransport firstWitness first last := by
  intro facts bindings env locals savedHeap savedWitness saved transported
  exact (left saved transported).trans
    (right saved (transported.trans witness))

theorem RetainedCallerTransport.freshArrayPublication
    {heap : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    (related : LiveHeapRel heap witness runtime)
    (capacity : Nat) (payload : UInt64) (name : Name) :
    RetainedCallerTransport witness runtime
      ((semanticArrayResult runtime #[.object (.tagged payload)] capacity).setGlobal
        name (.object (.heap runtime.nextLocation))) := by
  intro facts bindings env locals savedHeap savedWitness saved transported
  exact freshEmptyArray_pushTagged_publication saved transported related
    capacity payload name

/-- The physical/implementation transports are unchanged. Only the source
ordinaryness field is restricted to valid saved facts represented at entry. -/
structure RetainedCodeEntryTransports
    (entryRuntime currentRuntime : RuntimeState)
    (entryStore currentStore : Wasm.Store Host)
    (entryWitness currentWitness : RefinementWitness) : Prop
    extends ClosureTablesTransport entryStore currentStore entryWitness currentWitness where
  witness : WitnessTransport entryWitness currentWitness
  closureAllocationsPersistent : ClosureAllocationsPersistent entryWitness currentWitness
  capacity : HeaderCapacityTransport entryStore.host.runtime.heap
    currentStore.host.runtime.heap entryWitness
  retained : RetainedCallerTransport entryWitness entryRuntime currentRuntime
  externals : currentStore.host.externals = entryStore.host.externals

theorem RetainedCodeEntryTransports.ofLegacy
    {entryRuntime currentRuntime : RuntimeState}
    {entryStore currentStore : Wasm.Store Host}
    {entryWitness currentWitness : RefinementWitness}
    (legacy : ReuseCapacityCodeEntryTransports entryRuntime currentRuntime
      entryStore currentStore entryWitness currentWitness) :
    RetainedCodeEntryTransports entryRuntime currentRuntime entryStore currentStore
      entryWitness currentWitness := {
  toClosureTablesTransport := legacy.toClosureTablesTransport
  witness := legacy.witness
  closureAllocationsPersistent := legacy.closureAllocationsPersistent
  capacity := legacy.capacity
  retained := RetainedCallerTransport.ofOrdinary legacy.ordinary
  externals := legacy.externals }

theorem RetainedCodeEntryTransports.refl (runtime : RuntimeState)
    (store : Wasm.Store Host) (witness : RefinementWitness) :
    RetainedCodeEntryTransports runtime runtime store store witness witness :=
  .ofLegacy (ReuseCapacityCodeEntryTransports.refl runtime store witness)

/-- Inner-call completion composes all transports back to the original outer
entry. No all-location ordinaryness or new post-hoc entry is needed. -/
theorem RetainedCodeEntryTransports.trans
    {first middle last : RuntimeState}
    {firstStore middleStore lastStore : Wasm.Store Host}
    {firstWitness middleWitness lastWitness : RefinementWitness}
    (left : RetainedCodeEntryTransports first middle firstStore middleStore
      firstWitness middleWitness)
    (right : RetainedCodeEntryTransports middle last middleStore lastStore
      middleWitness lastWitness) :
    RetainedCodeEntryTransports first last firstStore lastStore firstWitness lastWitness := {
  toClosureTablesTransport := {
    hostDispatchPreserved := right.hostDispatchPreserved.trans left.hostDispatchPreserved
    witnessDispatchPreserved := right.witnessDispatchPreserved.trans left.witnessDispatchPreserved
    hostDescriptorsPreserved := right.hostDescriptorsPreserved.trans left.hostDescriptorsPreserved
    witnessDescriptorsPreserved := right.witnessDescriptorsPreserved.trans left.witnessDescriptorsPreserved }
  witness := WitnessTransport.trans left.witness right.witness
  closureAllocationsPersistent := ClosureAllocationsPersistent.trans
    left.closureAllocationsPersistent right.closureAllocationsPersistent
  capacity := left.capacity.transAcross left.witness right.capacity
  retained := RetainedCallerTransport.trans left.retained left.witness right.retained
  externals := right.externals.trans left.externals }

/-- The same cache frame as before, paired with the weaker entry transport. -/
def RetainedEntryRelativeFrame
    (Frame : ReuseCapacityFacts → Nat → RuntimeState → Env → Wasm.Store Host →
      Wasm.Locals → RefinementWitness → Prop)
    (entryRuntime : RuntimeState) (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness) (facts : ReuseCapacityFacts)
    (remainingBytes : Nat) (runtime : RuntimeState) (env : Env)
    (store : Wasm.Store Host) (locals : Wasm.Locals) (witness : RefinementWitness) : Prop :=
  Frame facts remainingBytes runtime env store locals witness ∧
  RetainedCodeEntryTransports entryRuntime runtime entryStore store entryWitness witness

/-- Existing ordinary operation laws remain usable one step at a time. -/
theorem RetainedCodeEntryTransports.step
    {entryRuntime currentRuntime nextRuntime : RuntimeState}
    {entryStore currentStore nextStore : Wasm.Store Host}
    {entryWitness currentWitness nextWitness : RefinementWitness}
    (entry : RetainedCodeEntryTransports entryRuntime currentRuntime entryStore
      currentStore entryWitness currentWitness)
    (witness : WitnessTransport currentWitness nextWitness)
    (closureAllocationsPersistent : ClosureAllocationsPersistent currentWitness nextWitness)
    (capacity : HeaderCapacityTransport currentStore.host.runtime.heap
      nextStore.host.runtime.heap currentWitness)
    (ordinary : OrdinaryPersistenceTransport currentRuntime nextRuntime)
    (externals : nextStore.host.externals = currentStore.host.externals)
    (closureTables : ClosureTablesTransport currentStore nextStore currentWitness nextWitness) :
    RetainedCodeEntryTransports entryRuntime nextRuntime entryStore nextStore
      entryWitness nextWitness :=
  entry.trans {
    toClosureTablesTransport := closureTables
    witness, closureAllocationsPersistent, capacity, externals
    retained := RetainedCallerTransport.ofOrdinary ordinary }

theorem RetainedEntryRelativeFrame.ofLegacy
    {Frame : ReuseCapacityFacts → Nat → RuntimeState → Env → Wasm.Store Host →
      Wasm.Locals → RefinementWitness → Prop}
    {entryRuntime runtime : RuntimeState} {entryStore store : Wasm.Store Host}
    {entryWitness witness : RefinementWitness} {facts : ReuseCapacityFacts}
    {remainingBytes : Nat} {env : Env} {locals : Wasm.Locals}
    (frame : ReuseCapacityEntryRelativeFrame Frame entryRuntime entryStore
      entryWitness facts remainingBytes runtime env store locals witness) :
    RetainedEntryRelativeFrame Frame entryRuntime entryStore entryWitness facts
      remainingBytes runtime env store locals witness :=
  ⟨frame.1, RetainedCodeEntryTransports.ofLegacy frame.2⟩

/-- Lift a legacy local operation result while preserving the original entry.
The reflexive entry of the local proof is not substituted for the saved scope. -/
theorem RetainedCodeEntryTransports.afterLegacyFrame
    {Frame : ReuseCapacityFacts → Nat → RuntimeState → Env → Wasm.Store Host →
      Wasm.Locals → RefinementWitness → Prop}
    {entryRuntime runtime nextRuntime : RuntimeState}
    {entryStore store nextStore : Wasm.Store Host}
    {entryWitness witness nextWitness : RefinementWitness}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat} {env : Env}
    {locals : Wasm.Locals}
    (entry : RetainedCodeEntryTransports entryRuntime runtime entryStore store
      entryWitness witness)
    (frame : ReuseCapacityEntryRelativeFrame Frame runtime store witness facts
      remainingBytes nextRuntime env nextStore locals nextWitness) :
    RetainedEntryRelativeFrame Frame entryRuntime entryStore entryWitness facts
      remainingBytes nextRuntime env nextStore locals nextWitness :=
  ⟨frame.1, entry.trans (.ofLegacy frame.2)⟩

def RetainedCacheEntryFrame (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function) (externals : ExternalImpl)
    (entryRuntime : RuntimeState) (entryStore : Wasm.Store Host)
    (entryWitness : RefinementWitness) (facts : ReuseCapacityFacts)
    (remainingBytes : Nat) (runtime : RuntimeState) (env : Env)
    (store : Wasm.Store Host) (locals : Wasm.Locals) (witness : RefinementWitness) : Prop :=
  RetainedEntryRelativeFrame
    (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
    entryRuntime entryStore entryWitness facts remainingBytes runtime env store locals witness

/-- Hereditary caller restoration at the original entry boundary. In contrast
to restoreDirectCaller, the callee may publish fresh heap objects. Its retained
transport discharges the caller-binding obligation and composes into the
restored caller's own entry transport, ready for another enclosing return. -/
theorem RetainedCacheEntryFrame.restoreCaller
    {sourceModule : Fir.Wasm.Module} {callerFunction calleeFunction : Fir.Wasm.Function}
    {externals : ExternalImpl} {entryRuntime callRuntime finalRuntime : RuntimeState}
    {entryStore callStore finalStore : Wasm.Store Host}
    {entryWitness callWitness finalWitness : RefinementWitness}
    {facts calleeFacts : ReuseCapacityFacts} {callerBytes resultBytes : Nat}
    {callerEnv calleeEnv : Env} {callerLocals calleeLocals resumedLocals : Wasm.Locals}
    {result : FVarId} {resultIndex : Nat} {value : Value} {physical : Wasm.Value}
    (caller : RetainedCacheEntryFrame sourceModule callerFunction externals
      entryRuntime entryStore entryWitness facts callerBytes callRuntime callerEnv
      callStore callerLocals callWitness)
    (callee : RetainedCacheEntryFrame sourceModule calleeFunction externals
      callRuntime callStore callWitness calleeFacts resultBytes finalRuntime calleeEnv
      finalStore calleeLocals finalWitness)
    (related : StateRelated callerFunction finalRuntime (bind callerEnv result value)
      finalStore resumedLocals finalWitness)
    (aligned : ConcreteLocalFrameAligned callerFunction finalRuntime
      (bind callerEnv result value) finalStore resumedLocals finalWitness)
    (resultFound : findFVar? (functionBindings callerFunction) result = some resultIndex)
    (localUpdate : LocalUpdate callerLocals resumedLocals resultIndex physical) :
    RetainedCacheEntryFrame sourceModule callerFunction externals
      entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts result)
      resultBytes finalRuntime (bind callerEnv result value) finalStore resumedLocals
      finalWitness := by
  have ordinary := (callee.2.retained caller.1.stateRelated.2
    (WitnessTransport.refl callWitness)).eraseBind (resultId := result) (result := value)
  exact ⟨caller.1.restoreCaller_of_retainedTransport callee.1 callee.2.witness
    callee.2.capacity ordinary related aligned resultFound localUpdate,
    caller.2.trans callee.2⟩

end FirTalos.Concrete
