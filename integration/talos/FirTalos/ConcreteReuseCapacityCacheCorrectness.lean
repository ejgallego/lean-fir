import FirTalos.ConcreteReuseCapacityCallCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Successful folds of cursor-preserving memory transitions preserve the
cursor from the first state to the final state. -/
private theorem List.foldlM_cache_preserves_heapCursor
    {α ε : Type} {step : MemoryState → α → Except ε MemoryState}
    (preserves : ∀ before value after,
      step before value = .ok after →
      after.heapCursor = before.heapCursor)
    {values : List α} {before after : MemoryState}
    (operation :
      values.foldlM (init := before) step = .ok after) :
    after.heapCursor = before.heapCursor := by
  induction values generalizing before with
  | nil =>
      simpa only [List.foldlM_nil, Except.ok.injEq] using
        (congrArg MemoryState.heapCursor
          (Except.ok.inj operation)).symm
  | cons value rest ih =>
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at operation
      cases firstOperation : step before value with
      | error failure =>
          rw [firstOperation] at operation
          contradiction
      | ok middle =>
          rw [firstOperation] at operation
          exact (ih operation).trans
            (preserves before value middle firstOperation)

/-- The canonical-dead persistence fallback is either a failure or an exact
state no-op, hence every successful result preserves the heap frontier. -/
theorem persistenceDeadNoOp_preserves_heapCursor
    {state result : MemoryState} {object : Word32}
    (operation :
      persistenceDeadNoOp state object = .ok result) :
    result.heapCursor = state.heapCursor := by
  unfold persistenceDeadNoOp at operation
  cases read : Header.read state.memory object with
  | error failure =>
      simp [liftMemory, read, Bind.bind,
        Except.bind] at operation
  | ok header =>
      simp only [liftMemory, read, Bind.bind,
        Except.bind] at operation
      by_cases canonical : header.isCanonicalFreedAt state object = true
      · simp [canonical, pure, Except.pure] at operation
        subst result
        rfl
      · simp [canonical] at operation

/-- Recursive cache persistence rewrites only allocation metadata. It may
visit an arbitrary constructor/closure graph, but no successful recursive
step advances or retracts the concrete heap frontier. -/
theorem markPersistentFuel_preserves_heapCursor
    {fuel : Nat} {state result : MemoryState} {object : Word32}
    {descriptors : ClosureDescriptorTable}
    (operation :
      markPersistentFuel fuel state object descriptors = .ok result) :
    result.heapCursor = state.heapCursor := by
  induction fuel generalizing state result object descriptors with
  | zero =>
      simp only [markPersistentFuel] at operation
      cases classified : object.classify <;> rw [classified] at operation
      · simp [pure, Except.pure] at operation
        subst result
        rfl
      · simp [pure, Except.pure] at operation
        subst result
        rfl
      · cases read : state.readLiveHeader object with
        | error failure =>
            cases failure with
            | deadObject address =>
                simp only [read] at operation
                exact persistenceDeadNoOp_preserves_heapCursor operation
            | _ => simp [read] at operation
        | ok header =>
            by_cases persistent : header.persistent = true
            · simp [read, persistent, pure, Except.pure] at operation
              subst result
              rfl
            · simp [read, persistent] at operation
      · simp at operation
  | succ fuel ih =>
      simp only [markPersistentFuel] at operation
      cases classified : object.classify <;> rw [classified] at operation
      · simp [pure, Except.pure] at operation
        subst result
        rfl
      · simp [pure, Except.pure] at operation
        subst result
        rfl
      · cases read : state.readLiveHeader object with
        | error failure =>
            cases failure with
            | deadObject address =>
                simp only [read] at operation
                exact persistenceDeadNoOp_preserves_heapCursor operation
            | _ => simp [read] at operation
        | ok header =>
            simp only [read, Bind.bind, Except.bind] at operation
            by_cases persistent : header.persistent = true
            · simp [persistent, pure, Except.pure] at operation
              subst result
              rfl
            · simp only [persistent] at operation
              cases ownedOperation :
                  readOwnedReferences state object header descriptors with
              | error failure =>
                  rw [ownedOperation] at operation
                  contradiction
              | ok owned =>
                  rw [ownedOperation] at operation
                  cases writeOperation :
                      writeLiveHeader state object
                        { header with persistent := true, refCount := 0 } with
                  | error failure =>
                      rw [writeOperation] at operation
                      contradiction
                  | ok middle =>
                      rw [writeOperation] at operation
                      exact
                        (List.foldlM_cache_preserves_heapCursor
                          (fun before child after childOperation =>
                            ih childOperation)
                          operation).trans
                          (writeLiveHeader_preserves_heapCursor writeOperation)
      · simp at operation

/-- The public cursor-bounded persistence wrapper inherits exact frontier
preservation from its fuel-indexed implementation. -/
theorem markPersistent_preserves_heapCursor
    {state result : MemoryState} {object : Word32}
    {descriptors : ClosureDescriptorTable}
    (operation :
      markPersistent state object descriptors = .ok result) :
    result.heapCursor = state.heapCursor := by
  unfold markPersistent at operation
  exact markPersistentFuel_preserves_heapCursor operation

/-- Publishing a concrete ABI lane may recursively mark its object graph, but
it never allocates and therefore preserves the exact heap frontier. -/
theorem persistGlobalValue_preserves_heapCursor
    {state result : MemoryState} {kind : AbiKind} {value : LaneValue}
    {descriptors : ClosureDescriptorTable}
    (operation :
      persistGlobalValue state kind value descriptors = .ok result) :
    result.heapCursor = state.heapCursor := by
  cases kind <;> cases value <;>
    simp only [persistGlobalValue] at operation
  all_goals try exact markPersistent_preserves_heapCursor operation
  all_goals
    simpa [pure, Except.pure] using
      (congrArg MemoryState.heapCursor (Except.ok.inj operation)).symm

/-- A successful concrete global publication changes the persistent bits and
the global table only; it cannot consume or recover heap address space. -/
theorem ConcreteRuntimeState.writeGlobal_preserves_heapCursor
    {state result : ConcreteRuntimeState} {name : Name} {kind : AbiKind}
    {value : LaneValue} {descriptors : ClosureDescriptorTable}
    (operation :
      state.writeGlobal name kind value descriptors = .ok result) :
    result.heap.heapCursor = state.heap.heapCursor := by
  unfold ConcreteRuntimeState.writeGlobal at operation
  cases persistentOperation :
      persistGlobalValue state.heap kind value descriptors with
  | error failure =>
      rw [persistentOperation] at operation
      contradiction
  | ok heap =>
      rw [persistentOperation] at operation
      cases globalOperation : state.globals.write name kind value with
      | error failure =>
          rw [globalOperation] at operation
          contradiction
      | ok globals =>
          rw [globalOperation] at operation
          simp only [Bind.bind, Except.bind] at operation
          have resultEq := Except.ok.inj operation
          subst result
          exact persistGlobalValue_preserves_heapCursor persistentOperation

/-- The executable Talos cache host call is allocation-free. Failure clearing,
physical decoding, persistent-bit publication, and store reconstruction leave
the heap cursor exactly where the declaration call left it. -/
theorem cacheSetStep_preserves_heapCursor
    {declaration : Name} {kind : AbiKind}
    {initial after : Wasm.Store Host} {physical : Wasm.Value}
    (operation :
      cacheSetStep declaration kind initial [physical] =
        .Return [physical] after) :
    after.host.runtime.heap.heapCursor =
      initial.host.runtime.heap.heapCursor := by
  unfold cacheSetStep at operation
  cases decoded : decodePhysicalLane kind physical with
  | error failure =>
      simp [decoded, trap] at operation
  | ok lane =>
      cases published :
          (clearFailure initial).host.runtime.writeGlobal declaration kind lane
            (clearFailure initial).host.closureDescriptors with
      | error failure =>
          simp [decoded, published, trap] at operation
      | ok runtime =>
          simp only [decoded, published] at operation
          have storeEq :
              replaceRuntime (clearFailure initial) runtime = after := by
            injection operation
          subst after
          simpa [replaceRuntime, clearFailure] using
            ConcreteRuntimeState.writeGlobal_preserves_heapCursor published

/-- The complete cache-publication suffix preserves every residual address
space budget. The host cache write preserves the heap cursor, while both
generated Wasm global writes preserve the host definitionally. -/
theorem cachePublication_preserves_addressSpaceBudget
    {declaration : Name} {kind : AbiKind}
    {afterCall afterCache valueStore : Wasm.Store Host}
    {physical : Wasm.Value} {valueIndex flagIndex : Nat}
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    {remainingBytes : Nat}
    (budget :
      afterCall.host.runtime.heap.AddressSpaceBudget remainingBytes) :
    (writeWasmGlobal valueStore flagIndex
      (.i32 1)).host.runtime.heap.AddressSpaceBudget remainingBytes := by
  apply budget.of_heapCursor_eq
  simpa [writeWasmGlobal, valueStoreEq] using
    cacheSetStep_preserves_heapCursor operation

/-- A related executable cache write preserves every allocation extent mapped
before publication. Recursive constructor and closure persistence is supplied
by the strengthened concrete-runtime theorem; equality of the deterministic
host result identifies its final heap with the observed cache step. -/
theorem cacheSetStep_preserves_mappedHeaderCapacity_of_related
    {initial after : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {declaration : Name} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    {slot : ConcreteGlobalSlot}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated : PhysicalValueRel witness kind physical semantic)
    (found : initial.host.runtime.globals.find? declaration = some slot)
    (kindEq : slot.kind = kind)
    (descriptorsEq :
      initial.host.closureDescriptors = witness.closureDescriptors)
    (operation :
      cacheSetStep declaration kind initial [physical] =
        .Return [physical] after) :
    HeaderCapacityTransport initial.host.runtime.heap after.host.runtime.heap
      witness := by
  obtain ⟨runtimeAfter, implementationOperation, _, _, capacity⟩ :=
    cacheSetStep_of_refines runtimeRelated valueRelated found kindEq
      descriptorsEq
  rw [operation] at implementationOperation
  have finalEq : after = replaceRuntime initial runtimeAfter := by
    injection implementationOperation
  subst after
  simpa [replaceRuntime, clearFailure] using capacity

/--
Recursive persistence leaves every semantic cell outside the published
root's original ownership closure unchanged.

The induction follows the executable metadata write and owned-field fold.
`HeapOwnershipFrame` transports each recursive child's reachability back
through earlier metadata-only visits, so the theorem applies to cyclic and
shared graphs as well as trees.
-/
theorem markPersistentLocationFuel_findCell_eq_of_not_reachable
    (fuel : Nat) (heap : Heap) (root other : Location)
    (unreachable :
      ¬Reachable heap [.object (.heap root)] other) :
    findCell? (markPersistentLocationFuel fuel heap root) other =
      findCell? heap other := by
  induction fuel generalizing heap root with
  | zero => rfl
  | succ fuel ih =>
      rw [markPersistentLocationFuel]
      cases found : findCell? heap root with
      | none => rfl
      | some cell =>
          by_cases skip : !cell.live || cell.persistent
          · simp [skip]
          · simp only [skip, Bool.false_eq_true, if_false]
            obtain ⟨after, post⟩ :=
              Fir.LeanIR.Impure.replaceCell_spec_of_find heap root cell
                { cell with rc := 0, persistent := true } found
            simp only [post.replaced]
            have parentFrame :
                Fir.LeanIR.Passes.ElimDead.HeapOwnershipFrame heap after :=
              Fir.LeanIR.Passes.ElimDead.heapOwnershipFrame_replace
                found post.target post.frame rfl
            have parentLookup :
                findCell? after other = findCell? heap other := by
              apply post.frame other
              intro same
              subst other
              exact unreachable (.root (by simp))
            have reachableTrans
                {parent target : Location}
                (head : Reachable heap [.object (.heap root)] parent)
                (tail : Reachable heap [.object (.heap parent)] target) :
                Reachable heap [.object (.heap root)] target := by
              induction tail with
              | @root location member =>
                  have same : location = parent := by simpa using member
                  subst location
                  exact head
              | child parentReachable childFound member reference recurse =>
                  exact .child recurse childFound member reference
            have foldLookup
                (items : List Value) (start : Heap)
                (ownership :
                  Fir.LeanIR.Passes.ElimDead.HeapOwnershipFrame heap start)
                (lookupFrame :
                  findCell? start other = findCell? heap other)
                (members : ∀ value, value ∈ items →
                  value ∈ cell.object.ownedValues.toList) :
                findCell?
                    (items.foldl (init := start) fun next value =>
                      match value with
                      | .object (.heap child) =>
                          markPersistentLocationFuel fuel next child
                      | _ => next)
                    other =
                  findCell? heap other := by
              induction items generalizing start with
              | nil => exact lookupFrame
              | cons head tail tailIH =>
                  simp only [List.foldl]
                  have tailMembers : ∀ value, value ∈ tail →
                      value ∈ cell.object.ownedValues.toList := by
                    intro value member
                    exact members value (List.mem_cons_of_mem head member)
                  cases head with
                  | object reference =>
                      cases reference with
                      | tagged payload =>
                          exact tailIH start ownership lookupFrame tailMembers
                      | heap child =>
                          have childMember :
                              Value.object (.heap child) ∈
                                cell.object.ownedValues.toList :=
                            members _ List.mem_cons_self
                          have childReachable :
                              Reachable heap [.object (.heap root)] child :=
                            .child (.root (by simp)) found childMember rfl
                          have childUnreachable :
                              ¬Reachable start [.object (.heap child)] other := by
                            intro reachable
                            have original := ownership.symm.reachable reachable
                            exact unreachable
                              (reachableTrans childReachable original)
                          have childFrame :=
                            Fir.LeanIR.Passes.ElimDead.heapOwnershipFrame_markPersistentLocationFuel
                              fuel start child
                          have childLookup := ih start child childUnreachable
                          exact tailIH
                            (markPersistentLocationFuel fuel start child)
                            (ownership.trans childFrame)
                            (childLookup.trans lookupFrame) tailMembers
                  | usize value =>
                      exact tailIH start ownership lookupFrame tailMembers
                  | scalar value =>
                      exact tailIH start ownership lookupFrame tailMembers
                  | erased =>
                      exact tailIH start ownership lookupFrame tailMembers
                  | reuseToken location? =>
                      exact tailIH start ownership lookupFrame tailMembers
            rw [← Array.foldl_toList]
            exact foldLookup cell.object.ownedValues.toList after parentFrame
              parentLookup (fun _ member => member)

/--
Facts-aware ordinary-token transport for a result-binding step.

Unlike `OrdinaryPersistenceTransport`, this boundary does not require every
source heap location to remain ordinary. It preserves exactly the retained
reuse-token facts that survive destination erasure. This is the right
contract for cache publication, which intentionally makes the returned graph
persistent and must therefore invalidate or exclude aliases into that graph.
-/
def ReuseTokenOrdinaryBindTransport
    (facts : ReuseCapacityFacts) (resultId : FVarId)
    (before after : RuntimeState)
    (sourceEnv : Env) (result : Value) : Prop :=
  ReuseTokenOrdinaryRel facts before sourceEnv →
    ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts resultId) after
      (bind sourceEnv resultId result)

/--
Semantic alias-safety condition for publishing one cache value.

Every retained nonzero reuse token must point outside the ownership closure
rooted at the value about to become persistent. This is deliberately stated
against the authoritative source fact map and environment rather than all
heap locations.
-/
def ReuseTokenPublicationDisjoint
    (facts : ReuseCapacityFacts) (runtime : RuntimeState)
    (sourceEnv : Env) (value : Value) : Prop :=
  ∀ (tokenId : FVarId) (available : Nat) (location : Location),
    findReuseCapacityEvidence? facts tokenId =
        some (.retainedAtLeast available) →
      lookup sourceEnv tokenId = some (.reuseToken (some location)) →
        ¬Reachable runtime.heap [value] location

/-- An empty fact map has no retained token that can alias publication. -/
theorem ReuseTokenPublicationDisjoint.empty
    (runtime : RuntimeState) (sourceEnv : Env) (value : Value) :
    ReuseTokenPublicationDisjoint [] runtime sourceEnv value := by
  intro tokenId available location tracked
  simp [findReuseCapacityEvidence?] at tracked

/-- Non-heap cache values have no semantic ownership closure, so publication
is disjoint from every retained token. -/
theorem ReuseTokenPublicationDisjoint.of_nonHeapReference
    {facts : ReuseCapacityFacts} {runtime : RuntimeState}
    {sourceEnv : Env} {value : Value}
    (nonHeap : IsNonHeapReference value) :
    ReuseTokenPublicationDisjoint facts runtime sourceEnv value := by
  intro tokenId available location tracked tokenLookup reachable
  clear tokenId available tracked tokenLookup
  induction reachable with
  | root member =>
      simp only [List.mem_singleton] at member
      subst value
      exact nonHeap
  | child parentReachable found member reference recurse =>
      exact recurse

/--
Recursive persistence retains the ordinary-token relation whenever every
tracked token is disjoint from the published ownership closure.
-/
theorem ReuseTokenOrdinaryRel.markPersistent_of_publicationDisjoint
    {facts : ReuseCapacityFacts} {runtime : RuntimeState}
    {sourceEnv : Env} {value : Value}
    (ordinary : ReuseTokenOrdinaryRel facts runtime sourceEnv)
    (disjoint :
      ReuseTokenPublicationDisjoint facts runtime sourceEnv value) :
    ReuseTokenOrdinaryRel facts (runtime.markPersistent value) sourceEnv := by
  intro tokenId available location cell tracked tokenLookup found
  have unreachable := disjoint tokenId available location tracked tokenLookup
  cases value with
  | object reference =>
      cases reference with
      | tagged payload =>
          exact ordinary tokenId available location cell tracked tokenLookup
            (by simpa [RuntimeState.markPersistent] using found)
      | heap root =>
          have lookupFrame :=
            markPersistentLocationFuel_findCell_eq_of_not_reachable
              (runtime.heap.length + 1) runtime.heap root location unreachable
          change
            findCell?
                (markPersistentLocationFuel (runtime.heap.length + 1)
                  runtime.heap root)
                location =
              some cell at found
          rw [lookupFrame] at found
          exact ordinary tokenId available location cell tracked tokenLookup
            found
  | usize value =>
      exact ordinary tokenId available location cell tracked tokenLookup
        (by simpa [RuntimeState.markPersistent] using found)
  | scalar value =>
      exact ordinary tokenId available location cell tracked tokenLookup
        (by simpa [RuntimeState.markPersistent] using found)
  | erased =>
      exact ordinary tokenId available location cell tracked tokenLookup
        (by simpa [RuntimeState.markPersistent] using found)
  | reuseToken location? =>
      exact ordinary tokenId available location cell tracked tokenLookup
        (by simpa [RuntimeState.markPersistent] using found)

/-- An all-location ordinary-persistence theorem remains a sufficient, but no
longer necessary, implementation of the facts-aware binding boundary. -/
theorem ReuseTokenOrdinaryBindTransport.ofOrdinaryPersistence
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {before after : RuntimeState}
    {sourceEnv : Env} {result : Value}
    (transport : OrdinaryPersistenceTransport before after) :
    ReuseTokenOrdinaryBindTransport facts resultId before after sourceEnv
      result := by
  intro ordinary
  exact ordinary.eraseBind transport

/--
Reachability disjointness constructively discharges the facts-aware cache
publication boundary for the exact semantic `setGlobal` transition.
-/
theorem ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {runtime : RuntimeState} {sourceEnv : Env} {result : Value}
    (name : Name)
    (disjoint :
      ReuseTokenPublicationDisjoint facts runtime sourceEnv result) :
    ReuseTokenOrdinaryBindTransport facts resultId runtime
      (runtime.setGlobal name result) sourceEnv result := by
  intro ordinary
  have persisted := ordinary.markPersistent_of_publicationDisjoint disjoint
  have published :
      ReuseTokenOrdinaryRel facts (runtime.setGlobal name result)
        sourceEnv := by
    intro tokenId available location cell tracked tokenLookup found
    apply persisted tokenId available location cell tracked tokenLookup
    simpa [RuntimeState.setGlobal] using found
  exact published.eraseBind
    (OrdinaryPersistenceTransport.refl (runtime.setGlobal name result))

/-- Clearing retained facts is a conservative alias-safe cache boundary:
there is no ordinary-token obligation regardless of which graph publication
makes persistent. -/
theorem ReuseTokenOrdinaryBindTransport.empty
    (resultId : FVarId) (before after : RuntimeState)
    (sourceEnv : Env) (result : Value) :
    ReuseTokenOrdinaryBindTransport [] resultId before after sourceEnv
      result := by
  intro ordinary tokenId available location cell tracked
  simp [eraseReuseCapacityFact, findReuseCapacityEvidence?] at tracked

/--
One lazy-cache result with all transports needed by the facts-indexed
resource frame.

The executable cache hit or miss is still represented by the existing
`LazyLetStepSimulates` theorem. This wrapper adds only the proof-side facts
that its continuation-polymorphic WP contract intentionally omits: the
checked destination write, witness/header and ordinary-token transport,
immutable-table preservation, and residual allocation budget.
-/
structure BudgetedCapacityPreservingLazyStep
    (path : LazyCachePath)
    (facts : ReuseCapacityFacts)
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (decl : LCNF.LetDecl .impure)
    (continuation : LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (initial nextStore : Wasm.Store Host)
    (locals nextLocals : Wasm.Locals)
    (resultIndex : Nat)
    (initialWitness nextWitness : RefinementWitness)
    (physical : Wasm.Value)
    (stepCost : Nat) : Prop where
  simulates :
    LazyLetStepSimulates path context sourceFunction module hostEnv
      sourceExternals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue initial nextStore locals nextLocals resultIndex
      initialWitness nextWitness
  targetSet :
    locals.set? resultIndex physical = some nextLocals
  ordinaryFrame :
    ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime
      nextRuntime sourceEnv sourceValue
  witnessTransport :
    WitnessTransport initialWitness nextWitness
  capacityTransport :
    HeaderCapacityTransport initial.host.runtime.heap
      nextStore.host.runtime.heap initialWitness
  externalsPreserved :
    nextStore.host.externals = initial.host.externals
  hostDescriptorsPreserved :
    nextStore.host.closureDescriptors =
      initial.host.closureDescriptors
  witnessDescriptorsPreserved :
    nextWitness.closureDescriptors =
      initialWitness.closureDescriptors
  residualBudget :
    ∀ remainingBytes,
      stepCost ≤ remainingBytes →
        initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
          nextStore.host.runtime.heap.AddressSpaceBudget
            (remainingBytes - stepCost)

/--
The generated cache-hit path is a zero-allocation budgeted lazy step.

The populated flag/value globals select and identify the cached physical
value. The only target mutation is the checked caller-local write; host state,
the heap, and the representation witness are unchanged.
-/
theorem BudgetedCapacityPreservingLazyStep.hit
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {missBody : Wasm.Program}
    {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness : RefinementWitness}
    {physical : Wasm.Value}
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv
        decl continuation sourceRuntime sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (flagPublished :
      initial.globals.globals[flagIndex]? = some (.i32 1))
    (valuePublished :
      initial.globals.globals[valueIndex]? = some physical)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (nextRelated :
      StateRelated sourceFunction sourceRuntime
        (bind sourceEnv decl.fvarId sourceValue) initial nextLocals
        initialWitness) :
    BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime sourceRuntime sourceEnv sourceValue initial initial locals
      nextLocals resultIndex initialWitness initialWitness physical 0 := by
  refine {
    simulates := lazyLetStepSimulates_hit sourceStep initialRelated
      flagPublished valuePublished targetSet rfl nextRelated
    targetSet
    ordinaryFrame :=
      ReuseTokenOrdinaryBindTransport.ofOrdinaryPersistence
        (OrdinaryPersistenceTransport.refl sourceRuntime)
    witnessTransport := WitnessTransport.refl initialWitness
    capacityTransport :=
      HeaderCapacityTransport.refl initial.host.runtime.heap initialWitness
    externalsPreserved := rfl
    hostDescriptorsPreserved := rfl
    witnessDescriptorsPreserved := rfl
    residualBudget := ?_
  }
  intro remainingBytes _ budget
  simpa using budget

/--
Package a proved cache-miss execution with its proof-side resource
transports. The executable miss block remains supplied by the existing
compiler-anchored lazy-cache theorem; this constructor centralizes the
additional W6 frame obligations and path-dependent cost.
-/
theorem BudgetedCapacityPreservingLazyStep.miss
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial nextStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {resultIndex stepCost : Nat}
    {initialWitness nextWitness : RefinementWitness}
    {physical : Wasm.Value}
    (simulates :
      LazyLetStepSimulates .miss context sourceFunction module hostEnv
        sourceExternals decl continuation targetValue sourceRuntime nextRuntime
        sourceEnv sourceValue initial nextStore locals nextLocals resultIndex
        initialWitness nextWitness)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (ordinaryFrame :
      ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime
        nextRuntime sourceEnv sourceValue)
    (witnessTransport :
      WitnessTransport initialWitness nextWitness)
    (capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap
        nextStore.host.runtime.heap initialWitness)
    (externalsPreserved :
      nextStore.host.externals = initial.host.externals)
    (hostDescriptorsPreserved :
      nextStore.host.closureDescriptors =
        initial.host.closureDescriptors)
    (witnessDescriptorsPreserved :
      nextWitness.closureDescriptors =
        initialWitness.closureDescriptors)
    (residualBudget :
      ∀ remainingBytes,
        stepCost ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            nextStore.host.runtime.heap.AddressSpaceBudget
              (remainingBytes - stepCost)) :
    BudgetedCapacityPreservingLazyStep .miss facts context sourceFunction module
      hostEnv sourceExternals decl continuation targetValue sourceRuntime
      nextRuntime sourceEnv sourceValue initial nextStore locals nextLocals
      resultIndex initialWitness nextWitness physical stepCost := {
  simulates
  targetSet
  ordinaryFrame
  witnessTransport
  capacityTransport
  externalsPreserved
  hostDescriptorsPreserved
  witnessDescriptorsPreserved
  residualBudget
}

/--
Close the exact compiler-generated lazy miss from a hereditary declaration
body, concrete `cacheSet`, and the two Wasm global publications, then attach
the W6 resource transports.

Unlike `BudgetedCapacityPreservingLazyStep.miss`, this theorem does not accept
an already assembled lazy simulation. It invokes the existing
compiler-anchored miss-body theorem and the surrounding flag conditional
directly.
-/
theorem BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {kind : AbiKind}
    {declarationId cacheSetId : Nat}
    {imp : Wasm.ImportDecl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCall afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness nextWitness : RefinementWitness}
    {physical oldValue oldFlag : Wasm.Value}
    {flagIndex valueIndex resultIndex stepCost : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (initialRelated :
      StateRelated callerFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (flagEmpty :
      initial.globals.globals[flagIndex]? = some (.i32 0))
    (body :
      CachedDeclarationBodyWP context sourceModule calleeFunction module
        hostEnv sourceRuntime sourceCode targetFunction initial afterCall
        initialWitness physical)
    (notImport :
      module.imports[declarationId]? = none)
    (functionFound :
      module.funcs[declarationId - module.imports.length]? =
        some targetFunction)
    (importFound :
      module.imports[cacheSetId]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : cacheSetId < module.imports.length)
    (contractFound :
      spec.contracts[cacheSetId]? =
        some (cacheSetContract declaration kind))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueGlobal :
      afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (flagGlobal :
      valueStore.globals.globals[flagIndex]? = some oldFlag)
    (distinct : valueIndex ≠ flagIndex)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (nextRelated :
      StateRelated callerFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue)
        (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals
        nextWitness)
    (ordinaryFrame :
      ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime
        nextRuntime sourceEnv sourceValue)
    (witnessTransport :
      WitnessTransport initialWitness nextWitness)
    (capacityTransport :
      HeaderCapacityTransport initial.host.runtime.heap
        (writeWasmGlobal valueStore flagIndex (.i32 1)).host.runtime.heap
        initialWitness)
    (externalsPreserved :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.externals =
        initial.host.externals)
    (hostDescriptorsPreserved :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.closureDescriptors =
        initial.host.closureDescriptors)
    (witnessDescriptorsPreserved :
      nextWitness.closureDescriptors =
        initialWitness.closureDescriptors)
    (residualBudget :
      ∀ remainingBytes,
        stepCost ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            ((writeWasmGlobal valueStore flagIndex
                (.i32 1)).host.runtime.heap).AddressSpaceBudget
              (remainingBytes - stepCost)) :
    BudgetedCapacityPreservingLazyStep .miss facts context callerFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex,
        .iff 0 0 [] [
          .call declarationId,
          .call cacheSetId,
          .globalSet valueIndex,
          .const 1,
          .globalSet flagIndex],
        .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue initial
      (writeWasmGlobal valueStore flagIndex (.i32 1)) locals nextLocals
      resultIndex initialWitness nextWitness physical stepCost := by
  have missBody :
      LazyMissBodySimulates module hostEnv
        [.call declarationId, .call cacheSetId, .globalSet valueIndex,
          .const 1, .globalSet flagIndex]
        valueIndex resultIndex initial
        (writeWasmGlobal valueStore flagIndex (.i32 1))
        locals nextLocals :=
    lazyMissBodySimulates_of_bodyWP_cacheSet body notImport functionFound
      importFound hostSatisfies importInBounds contractFound parameterCount
      resultCount operation valueGlobal valueStoreEq flagGlobal distinct
      targetSet
  have simulates :
      LazyLetStepSimulates .miss context callerFunction module hostEnv
        sourceExternals decl continuation
        [.globalGet flagIndex,
          .iff 0 0 [] [
            .call declarationId,
            .call cacheSetId,
            .globalSet valueIndex,
            .const 1,
            .globalSet flagIndex],
          .globalGet valueIndex]
        sourceRuntime nextRuntime sourceEnv sourceValue initial
        (writeWasmGlobal valueStore flagIndex (.i32 1)) locals nextLocals
        resultIndex initialWitness nextWitness :=
    lazyLetStepSimulates_miss sourceStep initialRelated flagEmpty missBody
      nextRelated
  exact .miss simulates targetSet ordinaryFrame witnessTransport
    capacityTransport externalsPreserved hostDescriptorsPreserved
    witnessDescriptorsPreserved residualBudget

/--
A budgeted hereditary nullary declaration plus a nonallocating cache
publication closes the complete lazy miss resource boundary.

The declaration consumes the path's allocation cost. `cacheSet` may update
persistence metadata and semantic globals but must preserve already mapped
header extents. The source post-state is the exact semantic publication, and
retained reuse tokens must be disjoint from the published ownership closure.
Its exact heap-frontier preservation is proved from the implementation, so
the residual address-space budget and the two Wasm `global.set`s require no
additional resource premise.
-/
theorem
    BudgetedCapacityPreservingLazyStep.miss_of_budgetedDeclaration_cacheSet
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {calleeCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {kind resultKind : AbiKind}
    {declarationId cacheSetId : Nat}
    {imp : Wasm.ImportDecl}
    {cacheSlot : ConcreteGlobalSlot}
    {sourceRuntime callRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCall afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness callWitness : RefinementWitness}
    {physical oldValue oldFlag : Wasm.Value}
    {flagIndex valueIndex resultIndex stepCost : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (initialRelated :
      StateRelated callerFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (flagEmpty :
      initial.globals.globals[flagIndex]? = some (.i32 0))
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclaration context sourceModule
        calleeFunction module hostEnv sourceExternals sourceRuntime callRuntime
        [] calleeCode targetFunction declarationId initial afterCall
        initialWitness callWitness [] resultKind sourceValue physical stepCost)
    (importFound :
      module.imports[cacheSetId]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : cacheSetId < module.imports.length)
    (contractFound :
      spec.contracts[cacheSetId]? =
        some (cacheSetContract declaration kind))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueGlobal :
      afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (flagGlobal :
      valueStore.globals.globals[flagIndex]? = some oldFlag)
    (distinct : valueIndex ≠ flagIndex)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (nextRelated :
      StateRelated callerFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue)
        (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals
        callWitness)
    (publicationRuntimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue)
    (publicationDisjoint :
      ReuseTokenPublicationDisjoint facts callRuntime sourceEnv sourceValue)
    (resultKindEq : resultKind = kind)
    (cacheFound :
      afterCall.host.runtime.globals.find? declaration = some cacheSlot)
    (cacheKindEq : cacheSlot.kind = kind)
    (cacheDescriptorsEq :
      afterCall.host.closureDescriptors = callWitness.closureDescriptors)
    (publicationExternals :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.externals =
        afterCall.host.externals)
    (publicationDescriptors :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.closureDescriptors =
        afterCall.host.closureDescriptors)
    : BudgetedCapacityPreservingLazyStep .miss facts context callerFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex,
        .iff 0 0 [] [
          .call declarationId,
          .call cacheSetId,
          .globalSet valueIndex,
          .const 1,
          .globalSet flagIndex],
        .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue initial
      (writeWasmGlobal valueStore flagIndex (.i32 1)) locals nextLocals
      resultIndex initialWitness callWitness physical stepCost := by
  subst nextRuntime
  apply BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet sourceStep
    initialRelated flagEmpty
    callee.capacityPreserving.successful.cachedBody
    callee.capacityPreserving.successful.notImport
    callee.capacityPreserving.successful.functionFound
    importFound hostSatisfies importInBounds contractFound parameterCount
    resultCount operation valueGlobal valueStoreEq flagGlobal distinct
    targetSet nextRelated
  · intro ordinary
    exact ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint declaration
      publicationDisjoint (ordinary.transport callee.ordinaryTransport)
  · exact callee.capacityPreserving.witnessTransport
  · apply callee.capacityPreserving.capacityTransport.transAcross
      callee.capacityPreserving.witnessTransport
    simpa [writeWasmGlobal, valueStoreEq] using
      cacheSetStep_preserves_mappedHeaderCapacity_of_related
        callee.capacityPreserving.successful.runtimeRelated
        (by simpa [resultKindEq] using
          callee.capacityPreserving.successful.valueRelated)
        cacheFound cacheKindEq cacheDescriptorsEq operation
  · exact publicationExternals.trans callee.externalsPreserved
  · exact publicationDescriptors.trans callee.hostDescriptorsPreserved
  · exact callee.witnessDescriptorsPreserved
  · intro remainingBytes stepFits budget
    exact cachePublication_preserves_addressSpaceBudget operation valueStoreEq
      (callee.residualBudget stepFits budget)

/--
A budgeted lazy result re-establishes the canonical mixed facts-indexed
frame, erasing only the destination's stale reuse fact.

This is the common hit/miss resource proof. Path-specific implementation
theorems need only build `BudgetedCapacityPreservingLazyStep`; they do not
repeat fact-map, local-frame, handler-table, descriptor, or budget
reconstruction.
-/
theorem
    ConcreteReuseCapacityPureExternalOwnershipFrame.ofLazyCacheResult
    {path : LazyCachePath}
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial nextStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness nextWitness : RefinementWitness}
    {physical : Wasm.Value}
    (invariant :
      ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
    (step :
      BudgetedCapacityPreservingLazyStep path facts context sourceFunction
        module hostEnv sourceExternals decl continuation targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore locals
        nextLocals resultIndex initialWitness nextWitness physical stepCost)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    ∃ resultStore resultLocals resultWitness nextFacts,
      LazyLetStepSimulates path context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue initial resultStore locals
          resultLocals resultIndex initialWitness resultWitness ∧
        resultStore.host.externals = initial.host.externals ∧
          resultStore.host.closureDescriptors =
              initial.host.closureDescriptors ∧
            resultWitness.closureDescriptors =
                initialWitness.closureDescriptors ∧
              reuseCapacityLetFacts? facts decl = some nextFacts ∧
                ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
                  sourceExternals nextFacts (remainingBytes - stepCost)
                  nextRuntime (bind sourceEnv decl.fvarId sourceValue)
                  resultStore resultLocals resultWitness := by
  rcases invariant with
    ⟨⟨⟨initialRelated, ordinaryTokens, frameAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩
  have nextRelated :
      ReuseCapacityStateRelated
        (eraseReuseCapacityFact facts decl.fvarId) sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness :=
    initialRelated.eraseResult step.simulates.2.2.1
      resultFound
      (localUpdate_of_set? step.targetSet) step.witnessTransport
      step.capacityTransport
  have nextOrdinary :
      ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts decl.fvarId)
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) := by
    exact step.ordinaryFrame ordinaryTokens
  have lengths := FirTalos.Correctness.locals_lengths_of_set? step.targetSet
  have nextFrameAligned :
      ConcreteLocalFrameAligned sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness :=
    ⟨lengths.1.trans frameAligned.1, lengths.2.trans frameAligned.2⟩
  have nextBudget :
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - stepCost) :=
    step.residualBudget remainingBytes stepFits budget
  have nextDescriptorAgreement :
      nextStore.host.closureDescriptors =
        nextWitness.closureDescriptors :=
    step.hostDescriptorsPreserved.trans
      (descriptorAgreement.trans step.witnessDescriptorsPreserved.symm)
  exact ⟨nextStore, nextLocals, nextWitness,
    eraseReuseCapacityFact facts decl.fvarId, step.simulates,
    step.externalsPreserved, step.hostDescriptorsPreserved,
    step.witnessDescriptorsPreserved, transfer,
    ⟨⟨⟨nextRelated, nextOrdinary, nextFrameAligned, nextBudget⟩,
      by rw [step.externalsPreserved]; exact integerImplementation,
      by rw [step.externalsPreserved]; exact naturalImplementation,
      by rw [step.externalsPreserved]; exact scalarImplementation⟩,
      nextDescriptorAgreement⟩⟩

/--
Uniform implementation condition for compiler-generated lazy declarations.

From the source path/admission and the actual compiler/adapter outputs, the
generated-program theorem selects one budgeted hit or miss result. This is a
declaration-environment property, not a caller-provided target execution
certificate.
-/
def LazyCacheImplementation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop) : Prop :=
  ∀ {path : LazyCachePath}
      {facts : ReuseCapacityFacts}
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
    LazySupported path sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      SourceLazyLetResult path context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue →
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        initial locals initialWitness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex →
      ∃ nextStore nextLocals nextWitness physical,
        BudgetedCapacityPreservingLazyStep path facts context sourceFunction
            module hostEnv sourceExternals decl continuation targetValue
            sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
            locals nextLocals resultIndex initialWitness nextWitness physical
            stepCost ∧
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId)

/-- A uniform lazy-declaration implementation instantiates the generic cache
law for the canonical mixed frame. -/
theorem LazyCacheImplementation.runtimeRefines
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    (implementation :
      LazyCacheImplementation context sourceModule sourceFunction labels module
        hostEnv sourceExternals LazySupported) :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels module hostEnv sourceExternals LazySupported
      (ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
        sourceExternals) := by
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals resultIndex remainingBytes
    stepCost initialWitness supported stepFits invariant sourceStep
    valueCompiled valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, physical, step, transfer⟩ :=
    implementation supported sourceStep invariant.1.1.1 valueCompiled
      valueAdapted resultFound
  exact invariant.ofLazyCacheResult stepFits step resultFound transfer

end FirTalos.Concrete
