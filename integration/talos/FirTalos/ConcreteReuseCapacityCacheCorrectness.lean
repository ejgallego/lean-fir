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

/-- The concrete cache host call changes only host-owned runtime state.
Physical Wasm globals are left for the generated `global.set` suffix. -/
theorem cacheSetStep_preserves_wasmGlobals
    {declaration : Name} {kind : AbiKind}
    {initial after : Wasm.Store Host} {physical : Wasm.Value}
    (operation :
      cacheSetStep declaration kind initial [physical] =
        .Return [physical] after) :
    after.globals.globals = initial.globals.globals := by
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
          rfl

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
One populated lazy-cache slot relates the semantic source cache entry to the
two physical Wasm globals selected by lowering.

`StateRelated` already relates the semantic cache to the typed concrete-host
cache used by `cacheSet`; it deliberately says nothing about Wasm module
globals. This relation supplies that missing generated-state layer: the flag
is populated, the value global contains the cached lane, and that lane refines
the exact semantic entry at the declaration's checked result kind.
-/
structure PopulatedLazyCacheSlotRel
    (witness : RefinementWitness)
    (runtime : RuntimeState)
    (store : Wasm.Store Host)
    (declaration : Name)
    (kind : AbiKind)
    (flagIndex valueIndex : Nat)
    (sourceValue : Value)
    (physical : Wasm.Value) : Prop where
  semanticFound :
    findGlobal? runtime.globals declaration = some sourceValue
  flagPublished :
    store.globals.globals[flagIndex]? = some (.i32 1)
  valuePublished :
    store.globals.globals[valueIndex]? = some physical
  valueRelated :
    PhysicalValueRel witness kind physical sourceValue

/--
The exact miss-publication suffix establishes the populated slot relation
consumed by the next hit. This connects the source `setGlobal` transition to
the two Wasm `global.set`s without folding cache globals into `StateRelated`.
-/
theorem PopulatedLazyCacheSlotRel.ofPublication
    {witness : RefinementWitness}
    {callRuntime nextRuntime : RuntimeState}
    {afterCache valueStore : Wasm.Store Host}
    {declaration : Name}
    {kind : AbiKind}
    {flagIndex valueIndex : Nat}
    {sourceValue : Value}
    {physical oldValue oldFlag : Wasm.Value}
    (runtimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue)
    (valueRelated :
      PhysicalValueRel witness kind physical sourceValue)
    (valueGlobal :
      afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (flagGlobal :
      valueStore.globals.globals[flagIndex]? = some oldFlag)
    (distinct : valueIndex ≠ flagIndex) :
    PopulatedLazyCacheSlotRel witness nextRuntime
      (writeWasmGlobal valueStore flagIndex (.i32 1)) declaration kind
      flagIndex valueIndex sourceValue physical := by
  subst nextRuntime
  obtain ⟨flagPublished, valuePublished⟩ :=
    cachePublication_globals valueGlobal valueStoreEq flagGlobal distinct
  exact {
    semanticFound := by
      simp [RuntimeState.setGlobal]
    flagPublished
    valuePublished
    valueRelated }

/--
Checked generated layout for every lazy-cache declaration.

Lowering assigns each initializer exactly two globals: an `i32` publication
flag at `2 * index` and the declaration's singleton result lane at
`2 * index + 1`. Keeping this fact explicit lets the cache-state relation be
used independently of how validation or lowering established it.
-/
structure LazyCacheTableLayout (source : Fir.Wasm.Module) : Prop where
  slot :
    ∀ {index : Nat} {declaration : Name},
      source.initializers[index]? = some declaration →
        ∃ kind,
          (source.callSignature? (.declaration declaration)).bind
              (·.results[0]?) = some kind ∧
            source.cacheGlobalKinds[2 * index]? = some .uint32 ∧
            source.cacheGlobalKinds[2 * index + 1]? = some kind

/-- The two global kinds contributed by one well-formed lazy initializer. -/
private def lazyCacheEntryKinds
    (source : Fir.Wasm.Module) (declaration : Name) : List AbiKind :=
  match
      (source.callSignature? (.declaration declaration)).bind
        (·.results[0]?) with
  | some kind => [.uint32, kind]
  | none => []

/--
The source-facing initializer condition needed to derive physical cache
layout. Successful validation is expected to expose this condition; all
offset arithmetic remains a W6 theorem over the executable layout function.
-/
def LazyCacheInitializerSignatures (source : Fir.Wasm.Module) : Prop :=
  ∀ {declaration : Name},
    declaration ∈ source.initializers.toList →
      ∃ kind,
        (source.callSignature? (.declaration declaration)).bind
            (·.results[0]?) = some kind

/-- The executable cache-global fold is a concatenation of the initializer
entries. This algebraic form is the basis for all physical index proofs. -/
private theorem lazyCacheKindsFold_toList
    (source : Fir.Wasm.Module)
    (names : List Name)
    (initial : Array AbiKind) :
    (names.foldl (init := initial) fun kinds declaration =>
      match source.callSignature? (.declaration declaration) with
      | some signature =>
          match signature.results[0]? with
          | some kind => (kinds.push .uint32).push kind
          | none => kinds
      | none => kinds).toList =
        initial.toList ++ names.flatMap (lazyCacheEntryKinds source) := by
  induction names generalizing initial with
  | nil =>
      simp
  | cons declaration rest ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      cases signature : source.callSignature? (.declaration declaration) with
      | none =>
          simp [signature, lazyCacheEntryKinds, ih]
      | some found =>
          cases result : found.results[0]? with
          | none =>
              simp [signature, result, lazyCacheEntryKinds, ih]
          | some kind =>
              simp [signature, result, lazyCacheEntryKinds, ih]

/-- A list view of the executable global-layout fold. -/
private theorem cacheGlobalKinds_toList
    (source : Fir.Wasm.Module) :
    source.cacheGlobalKinds.toList =
      source.initializers.toList.flatMap (lazyCacheEntryKinds source) := by
  unfold Fir.Wasm.Module.cacheGlobalKinds
  rw [← Array.foldl_toList]
  convert
    (lazyCacheKindsFold_toList source source.initializers.toList #[]) using 1
  · congr 1
  · simp

/-- Every well-formed initializer contributes exactly its even flag and odd
value lane to the concatenated cache-global table. -/
private theorem lazyCacheEntryKinds_flatMap_get?
    (source : Fir.Wasm.Module)
    {names : List Name}
    (signatures :
      ∀ {declaration : Name},
        declaration ∈ names →
          ∃ kind,
            (source.callSignature? (.declaration declaration)).bind
                (·.results[0]?) = some kind)
    {index : Nat}
    {declaration : Name}
    (found : names[index]? = some declaration) :
    ∃ kind,
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind ∧
        (names.flatMap (lazyCacheEntryKinds source))[2 * index]? =
            some .uint32 ∧
          (names.flatMap (lazyCacheEntryKinds source))[2 * index + 1]? =
            some kind := by
  induction names generalizing index declaration with
  | nil =>
      simp at found
  | cons head rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst declaration
          obtain ⟨kind, signature⟩ :=
            signatures (declaration := head) (by simp)
          exact ⟨kind, signature, by
            simp [lazyCacheEntryKinds, signature]⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          obtain ⟨headKind, headSignature⟩ :=
            signatures (declaration := head) (by simp)
          have restSignatures :
              ∀ {member : Name},
                member ∈ rest →
                  ∃ kind,
                    (source.callSignature? (.declaration member)).bind
                        (·.results[0]?) = some kind :=
            fun {member} memberFound =>
              signatures (declaration := member) (by simp [memberFound])
          obtain ⟨kind, signature, flagKind, valueKind⟩ :=
            ih restSignatures found
          refine ⟨kind, signature, ?_, ?_⟩
          · simp only [List.flatMap_cons, lazyCacheEntryKinds, headSignature]
            simpa [Nat.mul_succ] using flagKind
          · simp only [List.flatMap_cons, lazyCacheEntryKinds, headSignature]
            simpa [Nat.mul_succ] using valueKind

/-- Singleton initializer signatures determine the complete physical cache
layout; no separate layout certificate is needed. -/
theorem LazyCacheTableLayout.ofSignatures
    {source : Fir.Wasm.Module}
    (signatures : LazyCacheInitializerSignatures source) :
    LazyCacheTableLayout source := by
  refine ⟨?_⟩
  intro index declaration found
  have foundList :
      source.initializers.toList[index]? = some declaration := by
    simpa using found
  obtain ⟨kind, signature, flagKind, valueKind⟩ :=
    lazyCacheEntryKinds_flatMap_get? source signatures foundList
  refine ⟨kind, signature, ?_, ?_⟩
  · have flagKindList :
        source.cacheGlobalKinds.toList[2 * index]? =
          some (.uint32 : AbiKind) := by
      rw [cacheGlobalKinds_toList]
      exact flagKind
    simpa using flagKindList
  · have valueKindList :
        source.cacheGlobalKinds.toList[2 * index + 1]? = some kind := by
      rw [cacheGlobalKinds_toList]
      exact valueKind
    simpa using valueKindList

/--
The complete validation-facing boundary for generated lazy caches.

The integration-owned validator only needs to expose its executable
uniqueness result and singleton-signature loop. W6 derives all physical
flag/value offsets from those facts and carries them through execution.
-/
structure LazyCacheValidationFacts (source : Fir.Wasm.Module) : Prop where
  initializerUnique :
    Fir.Wasm.listAllUnique source.initializers.toList = true
  signatures : LazyCacheInitializerSignatures source

theorem LazyCacheValidationFacts.layout
    {source : Fir.Wasm.Module}
    (checked : LazyCacheValidationFacts source) :
    LazyCacheTableLayout source :=
  LazyCacheTableLayout.ofSignatures checked.signatures

/--
The one uniform fact the integration-owned symbolic validator must expose for
generated lazy caches.

This is a theorem about the validator implementation, not a per-module
certificate: one proof discharges the condition for every successfully
validated module. W6 keeps this boundary explicit until the monolithic
`validateModuleShape` initializer loop has an authoritative accessor.
-/
def LazyCacheValidatorSound : Prop :=
  ∀ {source : Fir.Wasm.Module},
    Fir.Wasm.validateModule source = .ok () →
      LazyCacheValidationFacts source

/--
Static result-kind agreement between generated lazy-cache operations and the
declaration signatures that determine their physical value lanes.

This is intentionally stronger than source-level named-call admission:
`AbiKind.refines` permits an `.object` declaration result at a `.tobject`
call site, while one generated Wasm global has one exact symbolic kind. See
`FIR-BUG-wasm-none-lazy-cache-result-refinement`.
-/
def LazyCacheResultKindsAligned
    (context : Fir.Wasm.Context) (source : Fir.Wasm.Module) : Prop :=
  ∀ {type : Expr} {declaration : Name} {target : LCNF.Decl .impure}
      {kind : AbiKind} {index : Nat},
    Fir.Wasm.checkedAbiKind type = .ok kind →
    context.program.findDecl? declaration = some target →
    target.params.isEmpty = true →
    context.cachedDeclarations.findIdx? (· == declaration) = some index →
    (source.callSignature? (.declaration declaration)).bind
        (·.results[0]?) = some kind

/--
One environment-wide static boundary for generated lazy caches.

Lowering must use the same ordered cache-name table as the emitted module,
validation supplies unique singleton-result initializer signatures, and the
generated cache operation kind must equal the declaration signature kind.
Dynamic hit/miss theorems consume this relation instead of independent
per-call initializer and signature certificates.
-/
structure LazyCacheGeneratedEnvironment
    (context : Fir.Wasm.Context) (source : Fir.Wasm.Module) : Prop where
  checked : LazyCacheValidationFacts source
  cacheNames :
    context.cachedDeclarations = source.initializers
  resultKinds :
    LazyCacheResultKindsAligned context source

/-- Successful supported lowering exposes the underlying production lowering
equation; no proof-side lowering function is introduced. -/
theorem LazyCacheGeneratedEnvironment.lower_of_lowerSupported
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lowerSupported program = .ok source) :
    Fir.Wasm.lower program = .ok source := by
  unfold Fir.Wasm.lowerSupported at lowered
  cases validation : Fir.Wasm.validateSupported program with
  | error error =>
      simp only [validation] at lowered
      change
        Except.error (Fir.Wasm.SupportedLoweringError.validation error) =
          Except.ok source at lowered
      contradiction
  | ok value =>
      cases value
      simp only [validation, pure, Except.pure] at lowered
      cases lowering : Fir.Wasm.lower program with
      | error error =>
          simp only [lowering] at lowered
          change
            Except.error (Fir.Wasm.SupportedLoweringError.lowering error) =
              Except.ok source at lowered
          contradiction
      | ok module =>
          simpa [lowering] using lowered

/--
Production lowering emits exactly the ordered cache-name table computed once
for every declaration context. This removes an independent
`context.cachedDeclarations = source.initializers` certificate from the
generated-cache boundary.
-/
theorem LazyCacheGeneratedEnvironment.initializers_of_lower
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source) :
    source.initializers = Fir.Wasm.cachedDeclarationNames program := by
  unfold Fir.Wasm.lower at lowered
  dsimp only at lowered
  generalize functionsEq :
      program.decls.filterMapM
          (Fir.Wasm.lowerDecl program
            (Fir.Wasm.cachedDeclarationNames program)) =
        functionsResult at lowered
  cases functionsResult with
  | error error =>
      contradiction
  | ok functions =>
      simp only [Bind.bind, Except.bind] at lowered
      by_cases operations :
          (Fir.Wasm.collectRuntimeOps functions).all
              Fir.Wasm.RuntimeOp.abiWellFormed = true
      · simp only [operations, ↓reduceIte] at lowered
        generalize externalsEq :
            (program.decls.filterMapM (fun decl =>
              match decl.value with
              | .extern _ => do
                  match Fir.Wasm.externalImport decl with
                  | .ok import_ => return some import_
                  | .error error =>
                      throw (Fir.Wasm.CompileError.abi error)
              | .code _ => pure none) :
                Except Fir.Wasm.CompileError (Array Fir.Wasm.Import)) =
              externalsResult at lowered
        cases externalsResult with
        | error error =>
            contradiction
        | ok externals =>
            simp only [pure, Except.pure, Except.ok.injEq] at lowered
            subst source
            rfl
      · simp [operations] at lowered

/-- Successful production adaptation exposes successful symbolic validation. -/
theorem LazyCacheGeneratedEnvironment.validated_of_adapt
    {source : Fir.Wasm.Module}
    {target : FirTalos.AdaptedModule}
    (adapted : FirTalos.adapt source = .ok target) :
    Fir.Wasm.validateModule source = .ok () := by
  unfold FirTalos.adapt at adapted
  cases sourceValid : Fir.Wasm.validateModule source with
  | error error =>
      simp only [sourceValid] at adapted
      change
        Except.error (FirTalos.AdapterError.invalidModule error) =
          Except.ok target at adapted
      contradiction
  | ok value =>
      have valueEq : value = () := Subsingleton.elim _ _
      rw [valueEq] at sourceValid

/--
Canonical whole-pipeline constructor for the generated lazy-cache environment.

Supported lowering fixes the emitted initializer order, adaptation supplies
symbolic validation, and the uniform validator theorem supplies the checked
layout facts. The only cache-specific static condition left is exact result
kind agreement, currently false for the refinement case recorded by
`FIR-BUG-wasm-none-lazy-cache-result-refinement`.
-/
theorem LazyCacheGeneratedEnvironment.ofSupportedPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {source : Fir.Wasm.Module}
    {target : FirTalos.AdaptedModule}
    (validatorSound : LazyCacheValidatorSound)
    (lowered : Fir.Wasm.lowerSupported program = .ok source)
    (adapted : FirTalos.adapt source = .ok target)
    (contextCacheNames :
      context.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program)
    (resultKinds : LazyCacheResultKindsAligned context source) :
    LazyCacheGeneratedEnvironment context source := by
  have ordinaryLowering :
      Fir.Wasm.lower program = .ok source :=
    LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered
  have emittedNames :
      source.initializers =
        Fir.Wasm.cachedDeclarationNames program :=
    LazyCacheGeneratedEnvironment.initializers_of_lower ordinaryLowering
  exact {
    checked :=
      validatorSound
        (LazyCacheGeneratedEnvironment.validated_of_adapt adapted)
    cacheNames := contextCacheNames.trans emittedNames.symm
    resultKinds }

/--
Specialize the pipeline theorem to the exact context shape constructed and
threaded by production lowering. Cache-name alignment is then definitional,
not a caller-provided equality.
-/
theorem LazyCacheGeneratedEnvironment.ofCanonicalSupportedPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    {target : FirTalos.AdaptedModule}
    (localKinds : Fir.Wasm.LocalKinds)
    (joins : Fir.Wasm.JoinPoints)
    (validatorSound : LazyCacheValidatorSound)
    (lowered : Fir.Wasm.lowerSupported program = .ok source)
    (adapted : FirTalos.adapt source = .ok target)
    (resultKinds :
      LazyCacheResultKindsAligned {
        program
        localKinds
        joins
        cachedDeclarations :=
          Fir.Wasm.cachedDeclarationNames program } source) :
    LazyCacheGeneratedEnvironment {
      program
      localKinds
      joins
      cachedDeclarations :=
        Fir.Wasm.cachedDeclarationNames program } source := by
  apply LazyCacheGeneratedEnvironment.ofSupportedPipeline validatorSound
    lowered adapted rfl resultKinds

/--
Select the exact emitted initializer slot and its physical value kind from
one compiler cache lookup. The lookup index remains the production
`findIdx?`; no proof-side cache enumeration is introduced.
-/
theorem LazyCacheGeneratedEnvironment.select
    {context : Fir.Wasm.Context}
    {source : Fir.Wasm.Module}
    (generated : LazyCacheGeneratedEnvironment context source)
    {type : Expr}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {kind : AbiKind}
    {index : Nat}
    (kindEq : Fir.Wasm.checkedAbiKind type = .ok kind)
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == declaration) = some index) :
    source.initializers[index]? = some declaration ∧
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind := by
  obtain ⟨inBounds, selected, _⟩ :=
    Array.findIdx?_eq_some_iff_getElem.mp cacheEq
  have selectedEq :
      context.cachedDeclarations[index] = declaration := by
    simpa using selected
  have cacheFound :
      context.cachedDeclarations[index]? = some declaration := by
    rw [Array.getElem?_eq_getElem inBounds, selectedEq]
  rw [generated.cacheNames] at cacheFound
  exact ⟨cacheFound,
    generated.resultKinds kindEq targetEq paramsEq cacheEq⟩

/-- The validator's executable uniqueness check is exactly `List.Nodup` under
the lawful Boolean equality used by module names. -/
theorem listAllUnique_eq_true_iff_nodup
    {α : Type} [BEq α] [LawfulBEq α] (values : List α) :
    Fir.Wasm.listAllUnique values = true ↔ values.Nodup := by
  induction values with
  | nil =>
      simp [Fir.Wasm.listAllUnique]
  | cons value rest ih =>
      simp [Fir.Wasm.listAllUnique, ih]

/--
One generated lazy-cache slot is either unpublished on both sides or
populated on both sides.

The unpublished value lane is semantically unconstrained, but it must be
physically present. This is exactly the fact needed to justify the generated
`global.set` when a declaration body has evolved unrelated cache slots—or has
recursively populated the same slot—before the outer publication suffix.
The populated case carries the full semantic/physical value relation needed
by the hit theorem.
-/
inductive LazyCacheSlotRel
    (witness : RefinementWitness)
    (runtime : RuntimeState)
    (store : Wasm.Store Host)
    (declaration : Name)
    (kind : AbiKind)
    (flagIndex valueIndex : Nat) : Prop where
  | empty
      (semanticEmpty :
        findGlobal? runtime.globals declaration = none)
      (flagEmpty :
        store.globals.globals[flagIndex]? = some (.i32 0))
      (valuePresent :
        ∃ physical,
          store.globals.globals[valueIndex]? = some physical)
  | populated
      {sourceValue : Value} {physical : Wasm.Value}
      (related :
        PopulatedLazyCacheSlotRel witness runtime store declaration kind
          flagIndex valueIndex sourceValue physical)

/--
Whole generated lazy-cache table relation.

Besides a pointwise empty/populated relation, `semanticCovered` rules out
semantic cache entries for which lowering emitted no physical slot. This is
the state invariant that can be threaded through the program proof rather
than rediscovering one isolated populated slot at each cache hit.
-/
structure LazyCacheGlobalsRel
    (witness : RefinementWitness)
    (source : Fir.Wasm.Module)
    (runtime : RuntimeState)
    (store : Wasm.Store Host) : Prop where
  checked : LazyCacheValidationFacts source
  semanticCovered :
    ∀ {declaration : Name} {value : Value},
      findGlobal? runtime.globals declaration = some value →
        declaration ∈ source.initializers.toList
  slots :
    ∀ {index : Nat} {declaration : Name},
      source.initializers[index]? = some declaration →
        ∃ kind,
          (source.callSignature? (.declaration declaration)).bind
              (·.results[0]?) = some kind ∧
            LazyCacheSlotRel witness runtime store declaration kind
              (2 * index) (2 * index + 1)

theorem LazyCacheGlobalsRel.layout
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    (related : LazyCacheGlobalsRel witness source runtime store) :
    LazyCacheTableLayout source :=
  related.checked.layout

/-- The generated flag at a checked cache index is zero in Talos's initial
store whenever the adapted target carries the canonical global declarations. -/
theorem initialStore_cacheFlag_zero
    {source : Fir.Wasm.Module}
    {target : Wasm.Module}
    {index : Nat}
    (targetGlobals : target.globals = FirTalos.globalDecls source)
    (flagKind :
      source.cacheGlobalKinds[2 * index]? = some (.uint32 : AbiKind)) :
    (initialStore source target).globals.globals[2 * index]? =
      some (.i32 0) := by
  have flagKindList :
      source.cacheGlobalKinds.toList[2 * index]? =
        some (.uint32 : AbiKind) := by
    simpa using flagKind
  change (target.globals.map (·.init))[2 * index]? = some (.i32 0)
  rw [targetGlobals]
  simp only [FirTalos.globalDecls, List.map_append, List.map_map]
  rw [List.getElem?_append_left]
  · simp [flagKindList, FirTalos.zeroValue, FirTalos.abiKind,
      FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
  · simpa using (List.getElem?_eq_some_iff.mp flagKindList).1

/-- Every checked value lane is physically present in Talos's initial store.
Its zero representation is deliberately not related to a semantic value until
the paired publication flag is set. -/
theorem initialStore_cacheValue_present
    {source : Fir.Wasm.Module}
    {target : Wasm.Module}
    {index : Nat}
    {kind : AbiKind}
    (targetGlobals : target.globals = FirTalos.globalDecls source)
    (valueKind :
      source.cacheGlobalKinds[2 * index + 1]? = some kind) :
    ∃ value,
      (initialStore source target).globals.globals[2 * index + 1]? =
        some value := by
  have valueKindList :
      source.cacheGlobalKinds.toList[2 * index + 1]? = some kind := by
    simpa using valueKind
  refine ⟨FirTalos.zeroValue kind, ?_⟩
  change (target.globals.map (·.init))[2 * index + 1]? =
    some (FirTalos.zeroValue kind)
  rw [targetGlobals]
  simp only [FirTalos.globalDecls, List.map_append, List.map_map]
  rw [List.getElem?_append_left]
  · simp [valueKindList]
  · simpa using (List.getElem?_eq_some_iff.mp valueKindList).1

/-- Empty semantic globals and physically allocated generated lanes establish
the complete table relation, independently of resident globals appended after
the cache prefix. -/
theorem LazyCacheGlobalsRel.empty
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    (checked : LazyCacheValidationFacts source)
    (runtimeEmpty : runtime.globals = [])
    (flagsEmpty :
      ∀ {index : Nat} {declaration : Name},
        source.initializers[index]? = some declaration →
          store.globals.globals[2 * index]? = some (.i32 0))
    (valuesPresent :
      ∀ {index : Nat} {declaration : Name},
        source.initializers[index]? = some declaration →
          ∃ physical,
            store.globals.globals[2 * index + 1]? = some physical) :
    LazyCacheGlobalsRel witness source runtime store := by
  refine {
    checked
    semanticCovered := ?_
    slots := ?_ }
  · intro declaration value found
    rw [runtimeEmpty] at found
    simp [findGlobal?] at found
  · intro index declaration found
    obtain ⟨kind, signature, _, _⟩ := checked.layout.slot found
    exact ⟨kind, signature, .empty (by simp [runtimeEmpty, findGlobal?])
      (flagsEmpty found) (valuesPresent found)⟩

/--
Whole-table empty relation for the actual adapter and Talos initial-store
path. Resident-runtime globals may follow the cache prefix; they do not affect
the cache indices.
-/
theorem LazyCacheGlobalsRel.adaptedInitial
    {source : Fir.Wasm.Module}
    {target : FirTalos.AdaptedModule}
    (checked : LazyCacheValidationFacts source)
    (adapted : FirTalos.adapt source = .ok target)
    (witness : RefinementWitness)
    (externals : Fir.Wasm.Concrete.ConcreteExternalImpl :=
      rejectExternalImpl) :
    LazyCacheGlobalsRel witness source ({} : RuntimeState)
      (initialStore source target.wasmModule externals) := by
  obtain ⟨functions, _, targetEq⟩ :=
    FirTalos.Correctness.adapt_preserves_module_layout adapted
  have targetGlobals :
      target.wasmModule.globals = FirTalos.globalDecls source := by
    rw [targetEq]
  apply LazyCacheGlobalsRel.empty checked rfl
  · intro index declaration found
    obtain ⟨kind, _, flagKind, _⟩ := checked.layout.slot found
    exact initialStore_cacheFlag_zero targetGlobals flagKind
  · intro index declaration found
    obtain ⟨kind, _, _, valueKind⟩ := checked.layout.slot found
    exact initialStore_cacheValue_present targetGlobals valueKind

/-- Pointwise transport for one cache slot. This is the form used when a
publication changes one pair of globals but preserves the two indices owned
by every other slot. -/
theorem LazyCacheSlotRel.transportAt
    {beforeWitness afterWitness : RefinementWitness}
    {beforeRuntime afterRuntime : RuntimeState}
    {beforeStore afterStore : Wasm.Store Host}
    {declaration : Name}
    {kind : AbiKind}
    {flagIndex valueIndex : Nat}
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (semanticLookup :
      findGlobal? afterRuntime.globals declaration =
        findGlobal? beforeRuntime.globals declaration)
    (flagLookup :
      afterStore.globals.globals[flagIndex]? =
        beforeStore.globals.globals[flagIndex]?)
    (valueLookup :
      afterStore.globals.globals[valueIndex]? =
        beforeStore.globals.globals[valueIndex]?)
    (related :
      LazyCacheSlotRel beforeWitness beforeRuntime beforeStore declaration
        kind flagIndex valueIndex) :
    LazyCacheSlotRel afterWitness afterRuntime afterStore declaration
      kind flagIndex valueIndex := by
  cases related with
  | empty semanticEmpty flagEmpty valuePresent =>
      exact .empty (semanticLookup.trans semanticEmpty)
        (flagLookup.trans flagEmpty)
        (by
          obtain ⟨physical, found⟩ := valuePresent
          exact ⟨physical, valueLookup.trans found⟩)
  | populated related =>
      exact .populated {
        semanticFound := semanticLookup.trans related.semanticFound
        flagPublished := flagLookup.trans related.flagPublished
        valuePublished := valueLookup.trans related.valuePublished
        valueRelated :=
          related.valueRelated.witnessTransport witnessTransport }

/-- Cache-slot relations transport through any transition that preserves the
semantic and physical global tables and transports the representation
witness. -/
theorem LazyCacheSlotRel.transport
    {beforeWitness afterWitness : RefinementWitness}
    {beforeRuntime afterRuntime : RuntimeState}
    {beforeStore afterStore : Wasm.Store Host}
    {declaration : Name}
    {kind : AbiKind}
    {flagIndex valueIndex : Nat}
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (runtimeGlobals :
      afterRuntime.globals = beforeRuntime.globals)
    (storeGlobals :
      afterStore.globals.globals = beforeStore.globals.globals)
    (related :
      LazyCacheSlotRel beforeWitness beforeRuntime beforeStore declaration
        kind flagIndex valueIndex) :
    LazyCacheSlotRel afterWitness afterRuntime afterStore declaration
      kind flagIndex valueIndex := by
  apply related.transportAt witnessTransport
  · simp [runtimeGlobals]
  · simp [storeGlobals]
  · simp [storeGlobals]

/-- The complete cache table is an ordinary frame: operations that leave both
global tables unchanged preserve it, even when allocation or reset/reuse
changes the representation witness. -/
theorem LazyCacheGlobalsRel.transport
    {beforeWitness afterWitness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {beforeRuntime afterRuntime : RuntimeState}
    {beforeStore afterStore : Wasm.Store Host}
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (runtimeGlobals :
      afterRuntime.globals = beforeRuntime.globals)
    (storeGlobals :
      afterStore.globals.globals = beforeStore.globals.globals)
    (related :
      LazyCacheGlobalsRel beforeWitness source beforeRuntime beforeStore) :
    LazyCacheGlobalsRel afterWitness source afterRuntime afterStore := by
  refine {
    checked := related.checked
    semanticCovered := ?_
    slots := ?_ }
  · intro declaration value found
    apply related.semanticCovered
    simpa [runtimeGlobals] using found
  · intro index declaration found
    obtain ⟨kind, signature, slot⟩ := related.slots found
    exact ⟨kind, signature,
      slot.transport witnessTransport runtimeGlobals storeGlobals⟩

/-- A successful concrete-host cache write preserves the physical Wasm cache
table. The semantic publication and physical value/flag writes are accounted
for by the subsequent generated suffix. -/
theorem LazyCacheGlobalsRel.afterCacheSet
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {beforeStore afterStore : Wasm.Store Host}
    {declaration : Name}
    {kind : AbiKind}
    {physical : Wasm.Value}
    (related :
      LazyCacheGlobalsRel witness source runtime beforeStore)
    (operation :
      cacheSetStep declaration kind beforeStore [physical] =
        .Return [physical] afterStore) :
    LazyCacheGlobalsRel witness source runtime afterStore :=
  related.transport (WitnessTransport.refl witness) rfl
    (cacheSetStep_preserves_wasmGlobals operation)

/-- A semantic cache hit forces the corresponding whole-table slot into its
populated branch and recovers the exact physical lane required by generated
hit code. -/
theorem LazyCacheGlobalsRel.populatedSlot
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    {index : Nat}
    {declaration : Name}
    {kind : AbiKind}
    {sourceValue : Value}
    (related : LazyCacheGlobalsRel witness source runtime store)
    (initializerFound :
      source.initializers[index]? = some declaration)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (semanticFound :
      findGlobal? runtime.globals declaration = some sourceValue) :
    ∃ physical,
      PopulatedLazyCacheSlotRel witness runtime store declaration kind
        (2 * index) (2 * index + 1) sourceValue physical := by
  obtain ⟨slotKind, slotSignature, slot⟩ :=
    related.slots initializerFound
  have kindEq : slotKind = kind := by
    rw [signature] at slotSignature
    exact Option.some.inj slotSignature.symm
  subst slotKind
  cases slot with
  | empty semanticEmpty _ _ =>
      rw [semanticFound] at semanticEmpty
      contradiction
  | populated slotRelated =>
      have valueEq := slotRelated.semanticFound
      rw [semanticFound] at valueEq
      cases valueEq
      exact ⟨_, slotRelated⟩

/-- If the semantic side has no cached value, the corresponding whole-table
slot must be in its empty branch and its generated flag is exactly zero. -/
theorem LazyCacheGlobalsRel.emptySlot
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    {index : Nat}
    {declaration : Name}
    {kind : AbiKind}
    (related : LazyCacheGlobalsRel witness source runtime store)
    (initializerFound :
      source.initializers[index]? = some declaration)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (semanticEmpty :
      findGlobal? runtime.globals declaration = none) :
    store.globals.globals[2 * index]? = some (.i32 0) := by
  obtain ⟨slotKind, slotSignature, slot⟩ :=
    related.slots initializerFound
  have kindEq : slotKind = kind := by
    rw [signature] at slotSignature
    exact Option.some.inj slotSignature.symm
  subst slotKind
  cases slot with
  | empty _ flagEmpty _ =>
      exact flagEmpty
  | populated slotRelated =>
      rw [slotRelated.semanticFound] at semanticEmpty
      contradiction

/-- Both physical lanes of every generated cache slot remain allocated,
independently of whether the semantic slot is empty or populated. -/
theorem LazyCacheGlobalsRel.slotLanesPresent
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    {index : Nat}
    {declaration : Name}
    {kind : AbiKind}
    (related : LazyCacheGlobalsRel witness source runtime store)
    (initializerFound :
      source.initializers[index]? = some declaration)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind) :
    ∃ oldFlag oldValue,
      store.globals.globals[2 * index]? = some oldFlag ∧
        store.globals.globals[2 * index + 1]? = some oldValue := by
  obtain ⟨slotKind, slotSignature, slot⟩ :=
    related.slots initializerFound
  have kindEq : slotKind = kind := by
    rw [signature] at slotSignature
    exact Option.some.inj slotSignature.symm
  subst slotKind
  cases slot with
  | empty _ flagEmpty valuePresent =>
      obtain ⟨oldValue, valueFound⟩ := valuePresent
      exact ⟨.i32 0, oldValue, flagEmpty, valueFound⟩
  | populated slotRelated =>
      exact ⟨.i32 1, _, slotRelated.flagPublished,
        slotRelated.valuePublished⟩

/--
Publishing one generated lazy-cache miss updates exactly one whole-table slot.

The semantic `setGlobal` and the two physical `global.set`s establish the
published slot through `PopulatedLazyCacheSlotRel.ofPublication`. Initializer
uniqueness makes every other declaration name distinct, while the even/odd
pair layout makes both of its physical indices distinct from the two writes.
Thus every other empty or populated slot transports unchanged. The selected
slot may itself have become populated during a nested declaration execution;
the outer publication soundly overwrites either state.
-/
theorem LazyCacheGlobalsRel.publish
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {beforeRuntime nextRuntime : RuntimeState}
    {beforeStore valueStore : Wasm.Store Host}
    {index : Nat}
    {declaration : Name}
    {kind : AbiKind}
    {sourceValue : Value}
    {physical : Wasm.Value}
    (related :
      LazyCacheGlobalsRel witness source beforeRuntime beforeStore)
    (initializerFound :
      source.initializers[index]? = some declaration)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (runtimeEq :
      nextRuntime = beforeRuntime.setGlobal declaration sourceValue)
    (valueRelated :
      PhysicalValueRel witness kind physical sourceValue)
    (valueStoreEq :
      valueStore =
        writeWasmGlobal beforeStore (2 * index + 1) physical) :
    LazyCacheGlobalsRel witness source nextRuntime
      (writeWasmGlobal valueStore (2 * index) (.i32 1)) := by
  obtain ⟨oldFlag, oldValue, flagBefore, valueGlobal⟩ :=
    related.slotLanesPresent initializerFound signature
  have valueFlagDistinct : 2 * index + 1 ≠ 2 * index := by
    omega
  have flagAfterValue :
      valueStore.globals.globals[2 * index]? = some oldFlag := by
    rw [valueStoreEq]
    exact (writeWasmGlobal_get_ne valueFlagDistinct).trans flagBefore
  have published :
      PopulatedLazyCacheSlotRel witness nextRuntime
        (writeWasmGlobal valueStore (2 * index) (.i32 1)) declaration kind
        (2 * index) (2 * index + 1) sourceValue physical :=
    PopulatedLazyCacheSlotRel.ofPublication runtimeEq valueRelated valueGlobal
      valueStoreEq flagAfterValue valueFlagDistinct
  refine {
    checked := related.checked
    semanticCovered := ?_
    slots := ?_ }
  · intro other value found
    by_cases sameDeclaration : other = declaration
    · subst other
      simpa using Array.mem_of_getElem? initializerFound
    · apply related.semanticCovered
      rw [runtimeEq] at found
      have foundInserted :
          findGlobal?
              (insertGlobal beforeRuntime.globals declaration sourceValue)
              other = some value := by
        simpa [RuntimeState.setGlobal] using found
      exact
        (findGlobal_insert_other beforeRuntime.globals declaration other
          sourceValue sameDeclaration).symm.trans foundInserted
  · intro otherIndex otherDeclaration otherFound
    by_cases sameIndex : otherIndex = index
    · subst otherIndex
      have declarationEq : declaration = otherDeclaration :=
        Option.some.inj (initializerFound.symm.trans otherFound)
      subst otherDeclaration
      exact ⟨kind, signature, .populated published⟩
    · obtain ⟨otherKind, otherSignature, otherSlot⟩ :=
        related.slots otherFound
      have initializerFoundList :
          source.initializers.toList[index]? = some declaration := by
        simpa using initializerFound
      have otherFoundList :
          source.initializers.toList[otherIndex]? =
            some otherDeclaration := by
        simpa using otherFound
      have initializerNodup : source.initializers.toList.Nodup :=
        (listAllUnique_eq_true_iff_nodup
          source.initializers.toList).mp related.checked.initializerUnique
      have differentDeclaration : otherDeclaration ≠ declaration := by
        intro declarationEq
        subst otherDeclaration
        have lookupEq :
            source.initializers.toList[otherIndex]? =
              source.initializers.toList[index]? := by
          rw [otherFoundList, initializerFoundList]
        have indexEq : otherIndex = index :=
          (List.getElem?_inj
            (List.getElem?_eq_some_iff.mp otherFoundList).1
            initializerNodup).mp lookupEq
        exact sameIndex indexEq
      have semanticLookup :
          findGlobal? nextRuntime.globals otherDeclaration =
            findGlobal? beforeRuntime.globals otherDeclaration := by
        rw [runtimeEq]
        simpa [RuntimeState.setGlobal] using
          findGlobal_insert_other beforeRuntime.globals declaration
            otherDeclaration sourceValue differentDeclaration
      have flagLookup :
          (writeWasmGlobal valueStore (2 * index)
              (.i32 1)).globals.globals[2 * otherIndex]? =
            beforeStore.globals.globals[2 * otherIndex]? := by
        calc
          _ = valueStore.globals.globals[2 * otherIndex]? :=
            writeWasmGlobal_get_ne (by omega)
          _ = beforeStore.globals.globals[2 * otherIndex]? := by
            rw [valueStoreEq]
            exact writeWasmGlobal_get_ne (by omega)
      have valueLookup :
          (writeWasmGlobal valueStore (2 * index)
              (.i32 1)).globals.globals[2 * otherIndex + 1]? =
            beforeStore.globals.globals[2 * otherIndex + 1]? := by
        calc
          _ = valueStore.globals.globals[2 * otherIndex + 1]? :=
            writeWasmGlobal_get_ne (by omega)
          _ = beforeStore.globals.globals[2 * otherIndex + 1]? := by
            rw [valueStoreEq]
            exact writeWasmGlobal_get_ne (by omega)
      exact ⟨otherKind, otherSignature,
        otherSlot.transportAt (WitnessTransport.refl witness) semanticLookup
          flagLookup valueLookup⟩

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
One source interpreter step in a declaration body cannot discharge both the
callee cache frame and its caller binding frame.
-/
private theorem executeStep_code_frames_ne_nil
    {externals : ExternalImpl}
    {state next : MachineState}
    {code : LCNF.Code .impure}
    {first second : Frame}
    {rest : List Frame}
    (transition :
      executeStep externals {
          state with
          control := .code code
          frames := first :: second :: rest } = .next next) :
    next.frames ≠ [] := by
  intro empty
  cases next with
  | mk nextProgram nextControl nextEnv nextJoins nextFrames nextRuntime =>
      simp only at empty
      subst nextFrames
      cases code <;>
        simp_all [executeStep, coreStep, fail, observe, pushBindFrame,
          resumeExternal] <;>
        grind

/--
One yielded source step consumes at most one frame, so a cache frame followed
by a caller binding frame cannot reach an empty stack.
-/
private theorem executeStep_yielded_frames_ne_nil
    {externals : ExternalImpl}
    {state next : MachineState}
    {value : Value}
    {first second : Frame}
    {rest : List Frame}
    (transition :
      executeStep externals {
          state with
          control := .yielded value
          frames := first :: second :: rest } = .next next) :
    next.frames ≠ [] := by
  intro empty
  cases next with
  | mk nextProgram nextControl nextEnv nextJoins nextFrames nextRuntime =>
      simp only at empty
      subst nextFrames
      cases first <;> simp_all [executeStep, coreStep]

/--
A complete three-step source cache hit determines both semantic facts used by
the generated hit proof: the source runtime is unchanged and the named global
already contains the returned value.

The declaration lookup and empty-parameter facts exclude malformed or partial
calls. If the semantic cache lookup were empty, an internal declaration would
still have both its cache and caller-binding frames, while an external
declaration could consume at most the cache frame. Neither can reach the
empty-frame caller continuation in the third step.
-/
theorem SourceLazyLetResult.hit_cacheFacts
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {fvarId : FVarId}
    {type : Expr}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv {
          fvarId
          binderName := fvarId.name
          type
          value := .fap declaration #[] }
        continuation nextRuntime sourceValue) :
    nextRuntime = sourceRuntime ∧
      findGlobal? sourceRuntime.globals declaration = some sourceValue := by
  unfold SourceLazyLetResult at sourceStep
  cases sourceStep with
  | step first rest =>
      cases rest with
      | step second rest =>
          cases rest with
          | step third rest =>
              cases rest
              simp [executeStep, coreStep, evalLetValue, evalArgs, pure,
                Except.pure, pushBindFrame] at first
              cases first
              have targetParamsEmpty : target.params = #[] :=
                Array.isEmpty_iff.mp paramsEq
              cases found :
                  findGlobal? sourceRuntime.globals declaration with
              | none =>
                  simp [executeStep, coreStep, found, invokeDecl, targetEq,
                    targetParamsEmpty, bindParams] at second
                  cases valueEq : target.value with
                  | code code =>
                      simp [valueEq] at second
                      cases second
                      have third' :
                          executeStep sourceExternals {
                            program := context.program
                            control := .code code
                            frames := [
                              .cache declaration,
                              .bind fvarId continuation sourceEnv []]
                            runtime := sourceRuntime } =
                          .next {
                            program := context.program
                            control := .code continuation
                            env := bind sourceEnv fvarId sourceValue
                            runtime := nextRuntime } := by
                        simpa using third
                      exact (executeStep_code_frames_ne_nil
                        (state := {
                          program := context.program
                          control := .code code
                          runtime := sourceRuntime })
                        (next := {
                          program := context.program
                          control := .code continuation
                          env := bind sourceEnv fvarId sourceValue
                          runtime := nextRuntime })
                        (first := .cache declaration)
                        (second := .bind fvarId continuation sourceEnv [])
                        (rest := [])
                        third') rfl |>.elim
                  | extern externAttr =>
                      simp [valueEq] at second
                      cases callResult :
                          sourceExternals.call {
                            name := declaration
                            paramTypes := #[]
                            resultType := target.type
                            args := #[] } sourceRuntime with
                      | error fault =>
                          simp [callResult] at second
                      | ok response =>
                        simp [callResult, resumeExternal] at second
                        cases second
                        have third' :
                          executeStep sourceExternals {
                            program := context.program
                            control := .yielded response.value
                            frames := [
                              .cache declaration,
                              .bind fvarId continuation sourceEnv []]
                            runtime := {
                              heap := response.heap
                              nextLocation := response.nextLocation
                              globals := sourceRuntime.globals
                              world := response.world
                              trace := sourceRuntime.trace.push {
                                name := declaration
                                args := #[]
                                result := response.value } } } =
                          .next {
                            program := context.program
                            control := .code continuation
                            env := bind sourceEnv fvarId sourceValue
                            runtime := nextRuntime } := by
                          simpa [MachineState.withValue] using third
                        exact (executeStep_yielded_frames_ne_nil
                          (state := {
                            program := context.program
                            control := .yielded response.value
                            runtime := {
                              heap := response.heap
                              nextLocation := response.nextLocation
                              globals := sourceRuntime.globals
                              world := response.world
                              trace := sourceRuntime.trace.push {
                                name := declaration
                                args := #[]
                                result := response.value } } })
                          (next := {
                            program := context.program
                            control := .code continuation
                            env := bind sourceEnv fvarId sourceValue
                            runtime := nextRuntime })
                          (value := response.value)
                          (first := .cache declaration)
                          (second := .bind fvarId continuation sourceEnv [])
                          (rest := [])
                          third') rfl |>.elim
              | some cached =>
                  simp [executeStep, coreStep, found] at second
                  cases second
                  simp [executeStep, coreStep] at third
                  rcases third with ⟨valueEq, runtimeEq⟩
                  change (fvarId, cached) :: sourceEnv =
                    (fvarId, sourceValue) :: sourceEnv at valueEq
                  injection valueEq with cachedEq
                  have sourceValueEq : cached = sourceValue := by
                    simpa using congrArg Prod.snd cachedEq
                  subst sourceValue
                  subst nextRuntime
                  exact ⟨rfl, rfl⟩

/--
A structured source cache miss determines the two semantic facts consumed by
generated miss publication: the named global was absent in the initial
runtime, and the post-runtime is exactly the declaration-call runtime followed
by `RuntimeState.setGlobal`.

The failed lookup is derived from the invocation step entering a state with a
cache frame. The publication equation is derived from the explicit
cache-frame transition after the declaration's arbitrary finite execution.
-/
theorem SourceLazyLetResult.miss_cacheFacts
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {fvarId : FVarId}
    {binderName : Name}
    {type : Expr}
    {declaration : Name}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv {
          fvarId
          binderName
          type
          value := .fap declaration #[] }
        continuation nextRuntime sourceValue) :
    ∃ callRuntime : RuntimeState,
      findGlobal? sourceRuntime.globals declaration = none ∧
        nextRuntime =
          callRuntime.setGlobal declaration sourceValue := by
  unfold SourceLazyLetResult SourceLazyMissResult at sourceStep
  rcases sourceStep with
    ⟨missDeclaration, calleeControl, calleeEnv, calleeJoins, calleeRuntime,
      resultEnv, resultJoins, callRuntime, calleeSteps, staged, entered,
      evaluated, published, bound⟩
  have declarationEq : missDeclaration = declaration := by
    simp [executeStep, coreStep, evalLetValue, evalArgs, Bind.bind,
      Except.bind, pure, Except.pure, pushBindFrame] at staged
    exact staged.symm
  subst missDeclaration
  have semanticEmpty :
      findGlobal? sourceRuntime.globals declaration = none := by
    cases found : findGlobal? sourceRuntime.globals declaration with
    | none => rfl
    | some cached =>
        simp [executeStep, coreStep, found] at entered
  have runtimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue := by
    simp [executeStep, coreStep] at published
    exact published.symm
  exact ⟨callRuntime, semanticEmpty, runtimeEq⟩

/--
Generic-let adapter for `miss_cacheFacts`. Compiler inversion normally exposes
the declaration call as a value equation, so callers need not reconstruct the
`LetDecl` record to use the structured miss theorem.
-/
theorem SourceLazyLetResult.miss_cacheFacts_of_valueEq
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {declaration : Name}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (valueEq : decl.value = .fap declaration #[])
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue) :
    ∃ callRuntime : RuntimeState,
      findGlobal? sourceRuntime.globals declaration = none ∧
        nextRuntime =
          callRuntime.setGlobal declaration sourceValue := by
  cases decl with
  | mk fvarId binderName type value =>
      simp only at valueEq
      subst value
      exact SourceLazyLetResult.miss_cacheFacts sourceStep

/--
The structured source miss and the hereditary declaration theorem have the
same deterministic callee run. Consequently the declaration result runtime is
exactly the miss runtime immediately before cache publication.

The source declaration lookup and body equations are static compiler facts.
No equality between final runtimes is supplied by the caller, and unrelated
cache slots may evolve during the callee execution.
-/
theorem SourceLazyLetResult.miss_cacheFacts_of_callee
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {calleeCode continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (declValue : decl.value = .fap declaration #[])
    (declarationFound :
      context.program.findDecl? declaration = some target)
    (targetParams : target.params = #[])
    (targetBody : target.value = .code calleeCode)
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (calleeResult :
      SourceCodeResult context sourceExternals sourceRuntime [] calleeCode
        resultRuntime sourceValue) :
    findGlobal? sourceRuntime.globals declaration = none ∧
      nextRuntime =
        resultRuntime.setGlobal declaration sourceValue := by
  cases decl with
  | mk fvarId binderName type value =>
      simp only at declValue
      subst value
      unfold SourceLazyLetResult SourceLazyMissResult at sourceStep
      rcases sourceStep with
        ⟨missDeclaration, calleeControl, calleeEnv, calleeJoins, calleeRuntime,
          resultEnv, resultJoins, callRuntime, calleeSteps, staged, entered,
          evaluated, published, bound⟩
      have declarationEq : missDeclaration = declaration := by
        simp [executeStep, coreStep, evalLetValue, evalArgs, Bind.bind,
          Except.bind, pure, Except.pure, pushBindFrame] at staged
        exact staged.symm
      subst missDeclaration
      have semanticEmpty :
          findGlobal? sourceRuntime.globals declaration = none := by
        cases found : findGlobal? sourceRuntime.globals declaration with
        | none => rfl
        | some cached =>
            simp [executeStep, coreStep, found] at entered
      have enteredExpected :
          executeStep sourceExternals {
              program := context.program
              control := .invokeName declaration #[]
              env := sourceEnv
              frames := [.bind fvarId continuation sourceEnv []]
              runtime := sourceRuntime } =
            .next {
              program := context.program
              control := .code calleeCode
              env := []
              frames := [
                .cache declaration,
                .bind fvarId continuation sourceEnv []]
              runtime := sourceRuntime } := by
        simp [executeStep, coreStep, semanticEmpty, invokeDecl,
          declarationFound, targetParams, targetBody, bindParams]
      rw [enteredExpected] at entered
      injection entered with protectedEq
      cases protectedEq
      obtain ⟨resultSteps, calleeResultEnv, resultExecution⟩ := calleeResult
      have sourceDone :
          executeStep sourceExternals {
              program := context.program
              control := .yielded sourceValue
              env := resultEnv
              joins := resultJoins
              runtime := callRuntime } =
            .done (ReturnedObservation callRuntime sourceValue) := by
        rfl
      have resultDone :
          executeStep sourceExternals
              (sourceYieldState context resultRuntime calleeResultEnv
                sourceValue) =
            .done (ReturnedObservation resultRuntime sourceValue) := by
        rfl
      have finalEq :=
        FirTalos.Correctness.ExecSteps.final_eq_of_done evaluated sourceDone
          resultExecution resultDone
      have callRuntimeEq : callRuntime = resultRuntime :=
        congrArg (fun state : MachineState => state.runtime) finalEq
      have publication :
          nextRuntime = callRuntime.setGlobal declaration sourceValue := by
        simp [executeStep, coreStep] at published
        exact published.symm
      exact ⟨semanticEmpty, by simpa [callRuntimeEq] using publication⟩

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
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (valueRelated :
      PhysicalValueRel initialWitness resultKind physical sourceValue) :
    BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction module
      hostEnv sourceExternals decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime sourceRuntime sourceEnv sourceValue initial initial locals
      nextLocals resultIndex initialWitness initialWitness physical 0 := by
  have nextRelated :
      StateRelated sourceFunction sourceRuntime
        (bind sourceEnv decl.fvarId sourceValue) initial nextLocals
        initialWitness := by
    have bound := initialRelated.bindPhysical resultFound resultKindAt
      valueRelated targetSet
    rw [initialRelated.clearFailure] at bound
    exact bound
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
A populated cache-slot relation plus the canonical local-frame invariant
constructs the complete zero-cost hit step. The checked destination update and
post-binding state relation are derived rather than supplied as execution
evidence.
-/
theorem BudgetedCapacityPreservingLazyStep.hit_of_populatedSlot
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {missBody : Wasm.Program}
    {declaration : Name}
    {kind : AbiKind}
    {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {initialWitness : RefinementWitness}
    {physical : Wasm.Value}
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv
        decl continuation sourceRuntime sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals initialWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some kind)
    (slot :
      PopulatedLazyCacheSlotRel initialWitness sourceRuntime initial declaration
        kind flagIndex valueIndex sourceValue physical) :
    ∃ nextLocals,
      BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction
        module hostEnv sourceExternals decl continuation
        [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
        sourceRuntime sourceRuntime sourceEnv sourceValue initial initial locals
        nextLocals resultIndex initialWitness initialWitness physical 0 := by
  obtain ⟨nextLocals, targetSet, _⟩ :=
    frameAligned.set? (nextRuntime := sourceRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := initial) (nextWitness := initialWitness)
      (physical := physical) resultFound
  exact ⟨nextLocals,
    BudgetedCapacityPreservingLazyStep.hit sourceStep initialRelated
      slot.flagPublished slot.valuePublished targetSet resultFound resultKindAt
      slot.valueRelated⟩

/--
Compiler-anchored populated-cache hit.

The lowering and adapter equations fix the exact flag/value indices and miss
body from the production pipeline. The cache-slot relation and local-frame
invariant then construct the zero-cost hit step for that generated program.
-/
theorem BudgetedCapacityPreservingLazyStep.hit_of_compiledCache
    {facts : ReuseCapacityFacts}
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (fvarId : FVarId) (type : Expr) (declaration : Name)
    (target : LCNF.Decl .impure)
    (resultKind : AbiKind)
    (cacheIndex declarationId cacheSetId resultIndex : Nat)
    (continuation : LCNF.Code .impure)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (initial : Wasm.Store Host)
    (locals : Wasm.Locals)
    (initialWitness : RefinementWitness)
    (physical : Wasm.Value)
    (kindEq : Fir.Wasm.checkedAbiKind type = .ok resultKind)
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == declaration) =
        some cacheIndex)
    (declarationFound :
      callIndex? sourceModule (.declaration declaration) = some declarationId)
    (cacheSetFound :
      callIndex? sourceModule
        (.runtime (.cacheSet declaration resultKind)) = some cacheSetId)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv {
          fvarId
          binderName := fvarId.name
          type
          value := .fap declaration #[] }
        continuation sourceRuntime sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals initialWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (slot :
      PopulatedLazyCacheSlotRel initialWitness sourceRuntime initial declaration
        resultKind (2 * cacheIndex) (2 * cacheIndex + 1) sourceValue physical) :
    let decl : LCNF.LetDecl .impure := {
      fvarId
      binderName := fvarId.name
      type
      value := .fap declaration #[] }
    ∃ nextLocals,
      Fir.Wasm.compileLetValue context decl = .ok [
          .globalGet (2 * cacheIndex) .uint32,
          .ifElse [] [
            .call (.declaration declaration),
            .call (.runtime (.cacheSet declaration resultKind)),
            .globalSet (2 * cacheIndex + 1) resultKind,
            .i32Const .uint32 1,
            .globalSet (2 * cacheIndex) .uint32],
          .globalGet (2 * cacheIndex + 1) resultKind] ∧
        instructions sourceModule sourceFunction labels [
          .globalGet (2 * cacheIndex) .uint32,
          .ifElse [] [
            .call (.declaration declaration),
            .call (.runtime (.cacheSet declaration resultKind)),
            .globalSet (2 * cacheIndex + 1) resultKind,
            .i32Const .uint32 1,
            .globalSet (2 * cacheIndex) .uint32],
          .globalGet (2 * cacheIndex + 1) resultKind] = .ok [
            .globalGet (2 * cacheIndex),
            .iff 0 0 [] [
              .call declarationId,
              .call cacheSetId,
              .globalSet (2 * cacheIndex + 1),
              .const 1,
              .globalSet (2 * cacheIndex)],
            .globalGet (2 * cacheIndex + 1)] ∧
          BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction
            module hostEnv sourceExternals decl continuation
            [.globalGet (2 * cacheIndex),
              .iff 0 0 [] [
                .call declarationId,
                .call cacheSetId,
                .globalSet (2 * cacheIndex + 1),
                .const 1,
                .globalSet (2 * cacheIndex)],
              .globalGet (2 * cacheIndex + 1)]
            sourceRuntime sourceRuntime sourceEnv sourceValue initial initial
            locals nextLocals resultIndex initialWitness initialWitness physical
            0 := by
  dsimp
  obtain ⟨compiled, adapted⟩ :=
    compileCachedLetValue_adapted context sourceModule sourceFunction labels
      fvarId type declaration target resultKind cacheIndex declarationId
      cacheSetId kindEq targetEq paramsEq cacheEq declarationFound cacheSetFound
  obtain ⟨nextLocals, hit⟩ :=
    BudgetedCapacityPreservingLazyStep.hit_of_populatedSlot sourceStep
      initialRelated frameAligned resultFound resultKindAt slot
  exact ⟨nextLocals, compiled, adapted, hit⟩

/--
Compiler-anchored hit derived from the whole generated cache environment.

The compiler lookup is interpreted once by `LazyCacheGeneratedEnvironment`;
callers no longer supply separate initializer/signature equations. Source
inversion derives the semantic cache lookup; `LazyCacheGlobalsRel` then rules
out the empty physical branch, recovers the cached lane, and feeds the
existing per-slot theorem.
-/
theorem BudgetedCapacityPreservingLazyStep.hit_of_compiledCacheTable
    {facts : ReuseCapacityFacts}
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (fvarId : FVarId) (type : Expr) (declaration : Name)
    (target : LCNF.Decl .impure)
    (resultKind : AbiKind)
    (cacheIndex declarationId cacheSetId resultIndex : Nat)
    (continuation : LCNF.Code .impure)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (initial : Wasm.Store Host)
    (locals : Wasm.Locals)
    (initialWitness : RefinementWitness)
    (kindEq : Fir.Wasm.checkedAbiKind type = .ok resultKind)
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == declaration) =
        some cacheIndex)
    (declarationFound :
      callIndex? sourceModule (.declaration declaration) = some declarationId)
    (cacheSetFound :
      callIndex? sourceModule
        (.runtime (.cacheSet declaration resultKind)) = some cacheSetId)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv {
          fvarId
          binderName := fvarId.name
          type
          value := .fap declaration #[] }
        continuation sourceRuntime sourceValue)
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (frameAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv initial
        locals initialWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (cacheTable :
      LazyCacheGlobalsRel initialWitness sourceModule sourceRuntime initial) :
    let decl : LCNF.LetDecl .impure := {
      fvarId
      binderName := fvarId.name
      type
      value := .fap declaration #[] }
    ∃ physical nextLocals,
      Fir.Wasm.compileLetValue context decl = .ok [
          .globalGet (2 * cacheIndex) .uint32,
          .ifElse [] [
            .call (.declaration declaration),
            .call (.runtime (.cacheSet declaration resultKind)),
            .globalSet (2 * cacheIndex + 1) resultKind,
            .i32Const .uint32 1,
            .globalSet (2 * cacheIndex) .uint32],
          .globalGet (2 * cacheIndex + 1) resultKind] ∧
        instructions sourceModule sourceFunction labels [
          .globalGet (2 * cacheIndex) .uint32,
          .ifElse [] [
            .call (.declaration declaration),
            .call (.runtime (.cacheSet declaration resultKind)),
            .globalSet (2 * cacheIndex + 1) resultKind,
            .i32Const .uint32 1,
            .globalSet (2 * cacheIndex) .uint32],
          .globalGet (2 * cacheIndex + 1) resultKind] = .ok [
            .globalGet (2 * cacheIndex),
            .iff 0 0 [] [
              .call declarationId,
              .call cacheSetId,
              .globalSet (2 * cacheIndex + 1),
              .const 1,
              .globalSet (2 * cacheIndex)],
            .globalGet (2 * cacheIndex + 1)] ∧
          BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction
            module hostEnv sourceExternals decl continuation
            [.globalGet (2 * cacheIndex),
              .iff 0 0 [] [
                .call declarationId,
                .call cacheSetId,
                .globalSet (2 * cacheIndex + 1),
                .const 1,
                .globalSet (2 * cacheIndex)],
              .globalGet (2 * cacheIndex + 1)]
            sourceRuntime sourceRuntime sourceEnv sourceValue initial initial
            locals nextLocals resultIndex initialWitness initialWitness physical
            0 := by
  dsimp
  obtain ⟨initializerFound, signature⟩ :=
    generated.select kindEq targetEq paramsEq cacheEq
  obtain ⟨_, semanticFound⟩ :=
    SourceLazyLetResult.hit_cacheFacts targetEq paramsEq sourceStep
  obtain ⟨physical, slot⟩ :=
    cacheTable.populatedSlot initializerFound signature semanticFound
  obtain ⟨nextLocals, compiled, adapted, hit⟩ :=
    BudgetedCapacityPreservingLazyStep.hit_of_compiledCache
      context sourceModule sourceFunction labels module hostEnv sourceExternals
      fvarId type declaration target resultKind cacheIndex declarationId
      cacheSetId resultIndex continuation sourceRuntime sourceEnv sourceValue
      initial locals initialWitness physical kindEq targetEq paramsEq cacheEq
      declarationFound cacheSetFound sourceStep initialRelated frameAligned
      resultFound resultKindAt slot
  exact ⟨physical, nextLocals, compiled, adapted, hit⟩

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
    {cacheIndex flagIndex valueIndex resultIndex stepCost : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (declValue : decl.value = .fap declaration #[])
    (initialRelated :
      StateRelated callerFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (cacheTable :
      LazyCacheGlobalsRel initialWitness sourceModule sourceRuntime initial)
    (initializerFound :
      sourceModule.initializers[cacheIndex]? = some declaration)
    (signature :
      (sourceModule.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (flagIndexEq : flagIndex = 2 * cacheIndex)
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
  obtain ⟨_, semanticEmpty, _⟩ :=
    SourceLazyLetResult.miss_cacheFacts_of_valueEq declValue sourceStep
  have flagEmptyAt :
      initial.globals.globals[2 * cacheIndex]? = some (.i32 0) :=
    cacheTable.emptySlot initializerFound signature semanticEmpty
  have flagEmpty :
      initial.globals.globals[flagIndex]? = some (.i32 0) := by
    simpa [flagIndexEq] using flagEmptyAt
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
    {sourceDeclaration : LCNF.Decl .impure}
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
    {cacheIndex flagIndex valueIndex resultIndex stepCost : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (declValue : decl.value = .fap declaration #[])
    (initialRelated :
      StateRelated callerFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (cacheTable :
      LazyCacheGlobalsRel initialWitness sourceModule sourceRuntime initial)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (kindEq :
      Fir.Wasm.checkedAbiKind decl.type = .ok kind)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == declaration) =
        some cacheIndex)
    (flagIndexEq : flagIndex = 2 * cacheIndex)
    (declarationFound :
      context.program.findDecl? declaration = some sourceDeclaration)
    (declarationParams : sourceDeclaration.params = #[])
    (declarationBody : sourceDeclaration.value = .code calleeCode)
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
  have paramsEq : sourceDeclaration.params.isEmpty = true := by
    simp [declarationParams]
  obtain ⟨initializerFound, signature⟩ :=
    generated.select kindEq declarationFound paramsEq cacheEq
  have publicationRuntimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue :=
    (SourceLazyLetResult.miss_cacheFacts_of_callee declValue declarationFound
      declarationParams declarationBody sourceStep
      callee.capacityPreserving.successful.sourceResult).2
  subst nextRuntime
  apply BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet sourceStep
    declValue initialRelated cacheTable initializerFound signature flagIndexEq
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
Attach the whole-table publication update to an already proved exact generated
miss. The miss and table conclusions share the same semantic post-state,
representation witness, and final store, so the program proof can consume
them as one vertical result.
-/
theorem
    BudgetedCapacityPreservingLazyStep.withPublishedCacheTable
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime callRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {resultIndex stepCost cacheIndex : Nat}
    {initialWitness nextWitness : RefinementWitness}
    {declaration : Name}
    {kind : AbiKind}
    {physical : Wasm.Value}
    (step :
      BudgetedCapacityPreservingLazyStep .miss facts context sourceFunction
        module hostEnv sourceExternals decl continuation targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue initial
        (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) locals
        nextLocals resultIndex initialWitness nextWitness physical stepCost)
    (cacheTable :
      LazyCacheGlobalsRel nextWitness sourceModule callRuntime afterCache)
    (initializerFound :
      sourceModule.initializers[cacheIndex]? = some declaration)
    (signature :
      (sourceModule.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (runtimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue)
    (valueRelated :
      PhysicalValueRel nextWitness kind physical sourceValue)
    (valueStoreEq :
      valueStore =
        writeWasmGlobal afterCache (2 * cacheIndex + 1) physical) :
    BudgetedCapacityPreservingLazyStep .miss facts context sourceFunction
          module hostEnv sourceExternals decl continuation targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue initial
          (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) locals
          nextLocals resultIndex initialWitness nextWitness physical stepCost ∧
      LazyCacheGlobalsRel nextWitness sourceModule nextRuntime
        (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) := by
  exact ⟨step, cacheTable.publish initializerFound signature
    runtimeEq valueRelated valueStoreEq⟩

/--
Compose the concrete-host cache write and the generated physical publication
suffix into the successor whole-cache relation.

The pre-host table may already contain nested cache evolution. Host
publication preserves its Wasm lanes; the final value/flag writes then replace
the selected slot without requiring it to remain semantically empty.
-/
theorem
    BudgetedCapacityPreservingLazyStep.withCacheSetPublishedTable
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime callRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCall afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {resultIndex stepCost cacheIndex : Nat}
    {initialWitness nextWitness : RefinementWitness}
    {declaration : Name}
    {kind : AbiKind}
    {physical : Wasm.Value}
    (step :
      BudgetedCapacityPreservingLazyStep .miss facts context sourceFunction
        module hostEnv sourceExternals decl continuation targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue initial
        (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) locals
        nextLocals resultIndex initialWitness nextWitness physical stepCost)
    (cacheTable :
      LazyCacheGlobalsRel nextWitness sourceModule callRuntime afterCall)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (initializerFound :
      sourceModule.initializers[cacheIndex]? = some declaration)
    (signature :
      (sourceModule.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind)
    (runtimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue)
    (valueRelated :
      PhysicalValueRel nextWitness kind physical sourceValue)
    (valueStoreEq :
      valueStore =
        writeWasmGlobal afterCache (2 * cacheIndex + 1) physical) :
    BudgetedCapacityPreservingLazyStep .miss facts context sourceFunction
          module hostEnv sourceExternals decl continuation targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue initial
          (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) locals
          nextLocals resultIndex initialWitness nextWitness physical stepCost ∧
      LazyCacheGlobalsRel nextWitness sourceModule nextRuntime
        (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) := by
  exact step.withPublishedCacheTable
    (cacheTable.afterCacheSet operation) initializerFound signature runtimeEq
    valueRelated valueStoreEq

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
Canonical W6 program frame with generated lazy-cache state.

This is the existing reuse-capacity, pure-external, and ownership frame plus
the whole source/Wasm cache-table relation. Keeping the cache relation as the
last conjunct lets non-cache operations use its ordinary transport theorem,
while hit/miss operations supply their path-specific table transition.
-/
def ConcreteReuseCapacityCacheFrame
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (externals : ExternalImpl)
    (facts : ReuseCapacityFacts)
    (remainingBytes : Nat)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction externals
      facts remainingBytes sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    LazyCacheGlobalsRel witness sourceModule sourceRuntime targetStore

/-- Lift an existing canonical entry frame to the cache-augmented invariant
for the production adapter/Talos initial store. -/
theorem ConcreteReuseCapacityCacheFrame.adaptedInitial
    {sourceModule : Fir.Wasm.Module}
    {targetModule : FirTalos.AdaptedModule}
    {sourceFunction : Fir.Wasm.Function}
    {sourceExternals : ExternalImpl}
    {concreteExternals : Fir.Wasm.Concrete.ConcreteExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    (core :
      ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
        sourceExternals facts remainingBytes ({} : RuntimeState) sourceEnv
        (initialStore sourceModule targetModule.wasmModule concreteExternals)
        locals witness)
    (checked : LazyCacheValidationFacts sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok targetModule) :
    ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
      sourceExternals facts remainingBytes ({} : RuntimeState) sourceEnv
      (initialStore sourceModule targetModule.wasmModule concreteExternals)
      locals witness := by
  exact ⟨core,
    LazyCacheGlobalsRel.adaptedInitial checked adapted witness
      concreteExternals⟩

/--
Exact lazy-result reconstruction for the cache-augmented canonical frame.

`cacheTransport` is the only additional operation-specific obligation beyond
the existing budgeted lazy step. Hits instantiate it with whole-table
transport; misses instantiate it with the pointwise publication theorem.
The result uses the actual post-store and witness rather than an existential
execution certificate.
-/
theorem ConcreteReuseCapacityCacheFrame.ofLazyCacheResult
    {path : LazyCachePath}
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
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
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
    (step :
      BudgetedCapacityPreservingLazyStep path facts context sourceFunction
        module hostEnv sourceExternals decl continuation targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore locals
        nextLocals resultIndex initialWitness nextWitness physical stepCost)
    (cacheTransport :
      LazyCacheGlobalsRel initialWitness sourceModule sourceRuntime initial →
        LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    LazyLetStepSimulates path context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue initial nextStore locals nextLocals
          resultIndex initialWitness nextWitness ∧
      nextStore.host.externals = initial.host.externals ∧
        nextStore.host.closureDescriptors =
            initial.host.closureDescriptors ∧
          nextWitness.closureDescriptors =
              initialWitness.closureDescriptors ∧
            reuseCapacityLetFacts? facts decl =
                some (eraseReuseCapacityFact facts decl.fvarId) ∧
              ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                sourceExternals (eraseReuseCapacityFact facts decl.fvarId)
                (remainingBytes - stepCost) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
                nextWitness := by
  rcases invariant with
    ⟨⟨⟨⟨initialRelated, ordinaryTokens, frameAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩, initialCache⟩
  have nextRelated :
      ReuseCapacityStateRelated
        (eraseReuseCapacityFact facts decl.fvarId) sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness :=
    initialRelated.eraseResult step.simulates.2.2.1 resultFound
      (localUpdate_of_set? step.targetSet) step.witnessTransport
      step.capacityTransport
  have nextOrdinary :
      ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts decl.fvarId)
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) :=
    step.ordinaryFrame ordinaryTokens
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
  have nextCache :
      LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore :=
    cacheTransport initialCache
  exact ⟨step.simulates, step.externalsPreserved,
    step.hostDescriptorsPreserved, step.witnessDescriptorsPreserved, transfer,
    ⟨⟨⟨⟨nextRelated, nextOrdinary, nextFrameAligned, nextBudget⟩,
      by rw [step.externalsPreserved]; exact integerImplementation,
      by rw [step.externalsPreserved]; exact naturalImplementation,
      by rw [step.externalsPreserved]; exact scalarImplementation⟩,
      nextDescriptorAgreement⟩, nextCache⟩⟩

/--
Uniform implementation condition for compiler-generated lazy declarations.

From the source path/admission and the actual compiler/adapter outputs, the
generated-program theorem selects one budgeted hit or miss result. The
canonical reuse-capacity frame supplies both semantic refinement and the
checked local-frame bounds needed to construct the destination write. This is
a declaration-environment property, not a caller-provided target execution
certificate. Its static cache table and kind alignment are retained once for
the whole environment.
-/
structure LazyCacheImplementation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop) : Prop where
  generated :
    LazyCacheGeneratedEnvironment context sourceModule
  step :
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
      {remainingBytes : Nat}
      {initialWitness : RefinementWitness},
      LazySupported path sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      SourceLazyLetResult path context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue →
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness →
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
              some (eraseReuseCapacityFact facts decl.fvarId) ∧
            LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore

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
      (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals) := by
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals resultIndex remainingBytes
    stepCost initialWitness supported stepFits invariant sourceStep
    valueCompiled valueAdapted resultFound
  obtain ⟨nextStore, nextLocals, nextWitness, physical, step, transfer,
      nextCache⟩ :=
    implementation.step supported sourceStep invariant valueCompiled
      valueAdapted resultFound
  have reconstructed :=
    invariant.ofLazyCacheResult stepFits step (fun _ => nextCache) resultFound
      transfer
  exact ⟨nextStore, nextLocals, nextWitness,
    eraseReuseCapacityFact facts decl.fvarId, reconstructed⟩

end FirTalos.Concrete
