import FirTalos.ConcreteReuseCapacityCallCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
Two declaration-entry compiler contexts belong to the same generated module.

Top-level declarations share the source program and the module-wide lazy-cache
table. Their `localKinds` and transient `joins` are deliberately absent:
`lowerDecl` computes those fields independently for each declaration body.
This is the coherence carried across recursive calls without identifying a
callee's declaration-local compiler context with its caller's context.
-/
structure DeclarationContextsCoherent
    (caller callee : Fir.Wasm.Context) : Prop where
  program : caller.program = callee.program
  cachedDeclarations :
    caller.cachedDeclarations = callee.cachedDeclarations

/--
Exact source execution transports from a declaration-local callee context to
any coherent caller context. Source machine states observe only the shared
program; compiler-local kinds, joins, and cache-indexing metadata do not occur
in `SourceCodeResult`.
-/
theorem DeclarationContextsCoherent.sourceCodeResult
    {caller callee : Fir.Wasm.Context}
    (contexts : DeclarationContextsCoherent caller callee)
    {sourceExternals : ExternalImpl}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {sourceValue : Value}
    (result :
      SourceCodeResult callee sourceExternals sourceRuntime sourceEnv
        sourceCode resultRuntime sourceValue) :
    SourceCodeResult caller sourceExternals sourceRuntime sourceEnv sourceCode
      resultRuntime sourceValue := by
  rcases result with ⟨count, terminalEnv, steps⟩
  exact ⟨count, terminalEnv, by
    simpa [sourceCodeState, sourceYieldState, contexts.program] using steps⟩

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

/-- A successful concrete cache host call preserves the ordered declaration
layout of its named, typed host slots. Only the selected slot's optional
value and reachable heap persistence metadata may change. -/
theorem cacheSetStep_preserves_hostStaticLayout
    {declaration : Name} {kind : AbiKind}
    {initial after : Wasm.Store Host} {physical : Wasm.Value}
    (operation :
      cacheSetStep declaration kind initial [physical] =
        .Return [physical] after) :
    after.host.runtime.globals.staticLayout =
      initial.host.runtime.globals.staticLayout := by
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
            ConcreteRuntimeState.writeGlobal_preserves_staticLayout published

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
Concrete cache publication plus the checked caller-local write reconstructs
the complete post-binding state relation.

The callee supplies the related pre-publication runtime and witness
transport. `cacheSetStep_of_refines` constructs the semantic `setGlobal`
transition; the generated Wasm global writes leave the host unchanged.
Consequently callers provide only compiler-derived local index/kind facts,
not an opaque post-state relation.
-/
theorem StateRelated.bindAfterCacheSet
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime callRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial afterCall afterCache valueStore : Wasm.Store Host}
    {locals nextLocals : Wasm.Locals}
    {initialWitness callWitness : RefinementWitness}
    {result : FVarId}
    {declaration : Name}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {sourceValue : Value}
    {cacheSlot : ConcreteGlobalSlot}
    {valueIndex flagIndex resultIndex : Nat}
    (initialRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        initialWitness)
    (calleeRelated :
      ConcreteRuntimeRel afterCall.host.runtime callWitness callRuntime)
    (witnessTransport :
      WitnessTransport initialWitness callWitness)
    (valueRelated :
      PhysicalValueRel callWitness kind physical sourceValue)
    (cacheFound :
      afterCall.host.runtime.globals.find? declaration = some cacheSlot)
    (cacheKindEq : cacheSlot.kind = kind)
    (cacheDescriptorsEq :
      afterCall.host.closureDescriptors = callWitness.closureDescriptors)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some kind)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals) :
    StateRelated sourceFunction
      (callRuntime.setGlobal declaration sourceValue)
      (bind sourceEnv result sourceValue)
      (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals
      callWitness := by
  obtain ⟨runtimeAfter, implementationOperation, runtimeRelated, _, _⟩ :=
    cacheSetStep_of_refines calleeRelated valueRelated cacheFound cacheKindEq
      cacheDescriptorsEq
  rw [operation] at implementationOperation
  have afterCacheEq :
      afterCache = replaceRuntime afterCall runtimeAfter := by
    injection implementationOperation
  subst afterCache
  apply initialRelated.bindAfterTransport witnessTransport
  · simpa [writeWasmGlobal, valueStoreEq] using runtimeRelated
  · simp only [writeWasmGlobal, valueStoreEq, replaceRuntime]
    rfl
  · exact resultFound
  · exact resultKindAt
  · exact valueRelated
  · exact targetSet

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
Every exact ABI result kind other than `object` or representation-polymorphic
`tobject` denotes a semantic value with no heap-reference ownership root.

This includes exact tagged values and retained reuse tokens: both may carry a
physical word associated with an allocation, but neither is a semantic
`.object (.heap _)` root for cache persistence.
-/
theorem PhysicalValueRel.isNonHeapReference_of_kind
    {witness : RefinementWitness} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel witness kind physical semantic)
    (notObject : kind ≠ .object) (notTObject : kind ≠ .tobject) :
    IsNonHeapReference semantic := by
  cases related with
  | word32 related =>
      cases related <;> simp_all [IsNonHeapReference]
  | word64 related =>
      cases related <;> simp_all [IsNonHeapReference]
  | float32Bits related => cases related
  | float64Bits related => cases related

/-- Publishing a non-heap semantic value changes only the global table. -/
theorem RuntimeState.setGlobal_heap_eq_of_nonHeapReference
    (runtime : RuntimeState) (name : Name) (value : Value)
    (nonHeap : IsNonHeapReference value) :
    (runtime.setGlobal name value).heap = runtime.heap := by
  cases value with
  | object reference =>
      cases reference with
      | tagged payload => rfl
      | heap location => contradiction
  | usize | scalar | erased | reuseToken => rfl

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

/-- One typed concrete-host declaration selected by the same signature query
used by `cacheDeclarations`. Keeping this helper proof-local exposes the
static list algebra without introducing another runtime representation. -/
private def cacheDeclaration?
    (source : Fir.Wasm.Module) (declaration : Name) :
    Option (Name × AbiKind) := do
  let signature ← source.callSignature? (.declaration declaration)
  let kind ← signature.results[0]?
  return (declaration, kind)

private theorem cacheDeclarations_eq_filterMap
    (source : Fir.Wasm.Module) :
    cacheDeclarations source =
      source.initializers.toList.filterMap (cacheDeclaration? source) := by
  rfl

private theorem cacheDeclaration?_eq_some_of_signature
    {source : Fir.Wasm.Module}
    {declaration : Name}
    {kind : AbiKind}
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind) :
    cacheDeclaration? source declaration = some (declaration, kind) := by
  unfold cacheDeclaration?
  cases signatureFound :
      source.callSignature? (.declaration declaration) with
  | none =>
      simp [signatureFound] at signature
  | some found =>
      cases resultFound : found.results[0]? with
      | none =>
          simp [signatureFound, resultFound] at signature
      | some foundKind =>
          simp [signatureFound, resultFound] at signature
          subst foundKind
          simp [resultFound]

/-- Under the validator's singleton-signature condition, filtering the
initializers into typed host declarations drops no name and preserves their
exact order. -/
private theorem cacheDeclarationNames_aux
    (source : Fir.Wasm.Module)
    (names : List Name)
    (signatures :
      ∀ {declaration : Name},
        declaration ∈ names →
          ∃ kind,
            (source.callSignature? (.declaration declaration)).bind
                (·.results[0]?) = some kind) :
    (names.filterMap (cacheDeclaration? source)).map Prod.fst = names := by
  induction names with
  | nil =>
      rfl
  | cons head rest ih =>
      obtain ⟨headKind, headSignature⟩ :=
        signatures (declaration := head) (by simp)
      have headSelected :
          cacheDeclaration? source head = some (head, headKind) :=
        cacheDeclaration?_eq_some_of_signature headSignature
      have restSignatures :
          ∀ {declaration : Name},
            declaration ∈ rest →
              ∃ kind,
                (source.callSignature? (.declaration declaration)).bind
                    (·.results[0]?) = some kind :=
        fun {declaration} member =>
          signatures (declaration := declaration) (by simp [member])
      simp [headSelected, ih restSignatures]

private theorem cacheDeclarations_names
    {source : Fir.Wasm.Module}
    (signatures : LazyCacheInitializerSignatures source) :
    (cacheDeclarations source).map Prod.fst =
      source.initializers.toList := by
  rw [cacheDeclarations_eq_filterMap]
  exact
    cacheDeclarationNames_aux source source.initializers.toList signatures

private theorem cacheDeclarations_mem_of_signature
    {source : Fir.Wasm.Module}
    {declaration : Name}
    {kind : AbiKind}
    (initializerMember :
      declaration ∈ source.initializers.toList)
    (signature :
      (source.callSignature? (.declaration declaration)).bind
          (·.results[0]?) = some kind) :
    (declaration, kind) ∈ cacheDeclarations source := by
  rw [cacheDeclarations_eq_filterMap]
  apply List.mem_filterMap.mpr
  exact ⟨declaration, initializerMember,
    cacheDeclaration?_eq_some_of_signature signature⟩

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

/-- Generated cache evidence is module-wide: coherent declaration contexts
share exactly the program and ordered cache-name table on which it depends. -/
theorem LazyCacheGeneratedEnvironment.ofCoherent
    {caller callee : Fir.Wasm.Context}
    {source : Fir.Wasm.Module}
    (generated : LazyCacheGeneratedEnvironment caller source)
    (contexts : DeclarationContextsCoherent caller callee) :
    LazyCacheGeneratedEnvironment callee source := by
  refine ⟨generated.checked, ?_, ?_⟩
  · rw [← contexts.cachedDeclarations]
    exact generated.cacheNames
  · intro type declaration target kind index kindEq targetEq paramsEq
      cacheEq
    exact generated.resultKinds kindEq
      (by simpa [contexts.program] using targetEq) paramsEq
      (by simpa [contexts.cachedDeclarations] using cacheEq)

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
semantic cache entries for which lowering emitted no physical slot.
`hostLayout` retains the ordered named/type declarations used by the concrete
`cacheSet` host, so every generated initializer has its host slot without a
per-call lookup premise. This is the state invariant that can be threaded
through the program proof rather than rediscovering one isolated populated
slot at each cache hit.
-/
structure LazyCacheGlobalsRel
    (witness : RefinementWitness)
    (source : Fir.Wasm.Module)
    (runtime : RuntimeState)
    (store : Wasm.Store Host) : Prop where
  checked : LazyCacheValidationFacts source
  hostLayout :
    store.host.runtime.globals.staticLayout = cacheDeclarations source
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

/--
Hereditary declaration correctness for code that may evaluate lazy globals.

The ordinary budgeted declaration theorem accounts for the source and target
execution, returned value, resources, and immutable host tables. This
cache-aware theorem additionally returns the evolved whole-cache relation at
the exact callee post-state. It is an induction hypothesis over generated
declarations, not a caller-provided execution certificate: nested lazy
initializers may populate any generated slot before the caller publishes its
own result.
-/
structure BudgetedCapacityPreservingSuccessfulDeclarationWithCache
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
    (stepCost : Nat) : Prop where
  declaration :
    BudgetedCapacityPreservingSuccessfulDeclaration context sourceModule
      sourceFunction module hostEnv sourceExternals sourceRuntime resultRuntime
      sourceEnv sourceCode targetFunction functionIndex initial afterCall
      initialWitness resultWitness parameters resultKind resultValue physical
      stepCost
  cacheTable :
    LazyCacheGlobalsRel resultWitness sourceModule resultRuntime afterCall

/--
Reinterpret a cache-aware declaration at a refined caller-facing ABI kind.
The whole-cache postcondition is independent of the physical result kind.
-/
theorem
    BudgetedCapacityPreservingSuccessfulDeclarationWithCache.ofRefines
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
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction module hostEnv sourceExternals sourceRuntime
        resultRuntime sourceEnv sourceCode targetFunction functionIndex initial
        afterCall initialWitness resultWitness parameters actualKind resultValue
        physical stepCost)
    (refines : actualKind.refines expectedKind = true) :
    BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
      sourceModule sourceFunction module hostEnv sourceExternals sourceRuntime
      resultRuntime sourceEnv sourceCode targetFunction functionIndex initial
      afterCall initialWitness resultWitness parameters expectedKind resultValue
      physical stepCost := {
  declaration := declaration.declaration.ofRefines refines
  cacheTable := declaration.cacheTable }

theorem LazyCacheGlobalsRel.layout
    {witness : RefinementWitness}
    {source : Fir.Wasm.Module}
    {runtime : RuntimeState}
    {store : Wasm.Store Host}
    (related : LazyCacheGlobalsRel witness source runtime store) :
    LazyCacheTableLayout source :=
  related.checked.layout

/-- The selected generated initializer has a concrete named host slot at its
checked singleton result kind. Slot existence follows from the canonical
ordered host layout and validator uniqueness, rather than from a dynamic
caller premise. -/
theorem LazyCacheGlobalsRel.hostSlot
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
    ∃ slot,
      store.host.runtime.globals.find? declaration = some slot ∧
        slot.kind = kind := by
  have initializerMember :
      declaration ∈ source.initializers.toList := by
    simpa using Array.mem_of_getElem? initializerFound
  have declarationMember :
      (declaration, kind) ∈ cacheDeclarations source :=
    cacheDeclarations_mem_of_signature initializerMember signature
  have hostMember :
      (declaration, kind) ∈
        store.host.runtime.globals.staticLayout := by
    rw [related.hostLayout]
    exact declarationMember
  have initializerNodup : source.initializers.toList.Nodup :=
    (listAllUnique_eq_true_iff_nodup
      source.initializers.toList).mp related.checked.initializerUnique
  have hostNamesUnique :
      (store.host.runtime.globals.staticLayout.map Prod.fst).Nodup := by
    rw [related.hostLayout,
      cacheDeclarations_names related.checked.signatures]
    exact initializerNodup
  exact ConcreteGlobals.find?_of_staticLayout_mem hostNamesUnique hostMember

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
    (hostLayout :
      store.host.runtime.globals.staticLayout = cacheDeclarations source)
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
    hostLayout
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
  · simp [initialStore, initialHost]
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
    (hostStaticLayout :
      afterStore.host.runtime.globals.staticLayout =
        beforeStore.host.runtime.globals.staticLayout)
    (related :
      LazyCacheGlobalsRel beforeWitness source beforeRuntime beforeStore) :
    LazyCacheGlobalsRel afterWitness source afterRuntime afterStore := by
  refine {
    checked := related.checked
    hostLayout := hostStaticLayout.trans related.hostLayout
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
    (cacheSetStep_preserves_hostStaticLayout operation)

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
    hostLayout := by
      simpa [writeWasmGlobal, valueStoreEq] using related.hostLayout
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
    (stepCost : Nat) : Prop
    extends ClosureTablesTransport initial nextStore initialWitness
      nextWitness where
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
    {binderName : Name}
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
          binderName
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
Generic-`LetDecl` adapter for `hit_cacheFacts`. Binder metadata is irrelevant
to the source transition, so compiler inversion needs only the exact nullary
call value.
-/
theorem SourceLazyLetResult.hit_cacheFacts_of_valueEq
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (valueEq : decl.value = .fap declaration #[])
    (targetEq : context.program.findDecl? declaration = some target)
    (paramsEq : target.params.isEmpty = true)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue) :
    nextRuntime = sourceRuntime ∧
      findGlobal? sourceRuntime.globals declaration = some sourceValue := by
  cases decl with
  | mk fvarId binderName type value =>
      simp only at valueEq
      subst value
      exact SourceLazyLetResult.hit_cacheFacts targetEq paramsEq sourceStep

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
    hostDispatchPreserved := rfl
    witnessDispatchPreserved := rfl
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
    (hostDispatchPreserved :
      nextStore.host.closureDispatch =
        initial.host.closureDispatch)
    (witnessDispatchPreserved :
      nextWitness.closureDispatch =
        initialWitness.closureDispatch)
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
  hostDispatchPreserved
  witnessDispatchPreserved
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
    {calleeContext : Fir.Wasm.Context}
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
      CachedDeclarationBodyWP calleeContext sourceModule calleeFunction module
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
    (hostDispatchPreserved :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.closureDispatch =
        initial.host.closureDispatch)
    (witnessDispatchPreserved :
      nextWitness.closureDispatch =
        initialWitness.closureDispatch)
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
    capacityTransport externalsPreserved hostDispatchPreserved
    witnessDispatchPreserved hostDescriptorsPreserved
    witnessDescriptorsPreserved residualBudget

/--
A budgeted hereditary nullary declaration plus a nonallocating cache
publication closes the complete lazy miss resource boundary.

The declaration consumes the path's allocation cost. `cacheSet` may update
persistence metadata and semantic globals but must preserve already mapped
header extents. The source post-state is the exact semantic publication.
The only ordinary-token premise is the facts-aware transport across result
publication and binding; reachability disjointness and alias-invalidating
fact transfer are sufficient implementations of that boundary. Exact
heap-frontier preservation is proved from the implementation, so the residual
address-space budget and the two Wasm `global.set`s require no additional
resource premise.
-/
theorem
    BudgetedCapacityPreservingLazyStep.miss_of_budgetedDeclaration_cacheSet
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
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
    (contexts : DeclarationContextsCoherent context calleeContext)
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclaration calleeContext
        sourceModule calleeFunction module hostEnv sourceExternals
        sourceRuntime callRuntime [] calleeCode targetFunction declarationId
        initial afterCall initialWitness callWitness [] resultKind sourceValue
        physical stepCost)
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
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some kind)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (publicationOrdinary :
      ReuseTokenOrdinaryBindTransport facts decl.fvarId callRuntime
        (callRuntime.setGlobal declaration sourceValue) sourceEnv sourceValue)
    (resultKindEq : resultKind = kind)
    (cacheFound :
      afterCall.host.runtime.globals.find? declaration = some cacheSlot)
    (cacheKindEq : cacheSlot.kind = kind)
    (cacheDescriptorsEq :
      afterCall.host.closureDescriptors = callWitness.closureDescriptors)
    (publicationExternals :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.externals =
        afterCall.host.externals)
    (publicationDispatch :
      (writeWasmGlobal valueStore flagIndex (.i32 1)).host.closureDispatch =
        afterCall.host.closureDispatch)
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
      (contexts.sourceCodeResult
        callee.capacityPreserving.successful.sourceResult)).2
  subst nextRuntime
  have nextRelated :
      StateRelated callerFunction
        (callRuntime.setGlobal declaration sourceValue)
        (bind sourceEnv decl.fvarId sourceValue)
        (writeWasmGlobal valueStore flagIndex (.i32 1)) nextLocals
        callWitness :=
    initialRelated.bindAfterCacheSet
      callee.capacityPreserving.successful.runtimeRelated
      callee.capacityPreserving.witnessTransport
      (by simpa [resultKindEq] using
        callee.capacityPreserving.successful.valueRelated)
      cacheFound cacheKindEq cacheDescriptorsEq operation valueStoreEq
      resultFound resultKindAt targetSet
  apply BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet sourceStep
    declValue initialRelated cacheTable initializerFound signature flagIndexEq
    callee.capacityPreserving.successful.cachedBody
    callee.capacityPreserving.successful.notImport
    callee.capacityPreserving.successful.functionFound
    importFound hostSatisfies importInBounds contractFound parameterCount
    resultCount operation valueGlobal valueStoreEq flagGlobal distinct
    targetSet nextRelated
  · intro ordinary
    exact publicationOrdinary
      (ordinary.transport callee.ordinaryTransport)
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
  · exact
      publicationDispatch.trans callee.hostDispatchPreserved
  · exact callee.witnessDispatchPreserved
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
Close a generated lazy miss and its successor whole-cache invariant from one
cache-aware hereditary declaration theorem.

The callee may populate arbitrary lazy globals while it executes. Its
hereditary result returns that evolved table at `afterCall`; concrete
`cacheSet` preserves the Wasm lanes, and the generated value/flag suffix
publishes the selected slot. This is the recursive miss theorem required by
the uniform compiler proof: no caller-supplied target execution certificate
or unchanged-cache premise remains.
-/
theorem
    BudgetedCapacityPreservingLazyStep.miss_of_cachedDeclaration_cacheSet
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
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
    {cacheIndex resultIndex stepCost : Nat}
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
    (declarationFound :
      context.program.findDecl? declaration = some sourceDeclaration)
    (declarationParams : sourceDeclaration.params = #[])
    (declarationBody : sourceDeclaration.value = .code calleeCode)
    (contexts : DeclarationContextsCoherent context calleeContext)
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache calleeContext
        sourceModule calleeFunction module hostEnv sourceExternals
        sourceRuntime callRuntime [] calleeCode targetFunction declarationId
        initial afterCall initialWitness callWitness [] resultKind sourceValue
        physical stepCost)
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
      afterCache.globals.globals[2 * cacheIndex + 1]? = some oldValue)
    (valueStoreEq :
      valueStore =
        writeWasmGlobal afterCache (2 * cacheIndex + 1) physical)
    (flagGlobal :
      valueStore.globals.globals[2 * cacheIndex]? = some oldFlag)
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some kind)
    (targetSet :
      locals.set? resultIndex physical = some nextLocals)
    (publicationOrdinary :
      ReuseTokenOrdinaryBindTransport facts decl.fvarId callRuntime
        (callRuntime.setGlobal declaration sourceValue) sourceEnv sourceValue)
    (resultKindEq : resultKind = kind)
    (cacheFound :
      afterCall.host.runtime.globals.find? declaration = some cacheSlot)
    (cacheKindEq : cacheSlot.kind = kind)
    (cacheDescriptorsEq :
      afterCall.host.closureDescriptors = callWitness.closureDescriptors)
    (publicationExternals :
      (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)).host.externals =
        afterCall.host.externals)
    (publicationDispatch :
      (writeWasmGlobal valueStore (2 * cacheIndex)
          (.i32 1)).host.closureDispatch =
        afterCall.host.closureDispatch)
    (publicationDescriptors :
      (writeWasmGlobal valueStore (2 * cacheIndex)
          (.i32 1)).host.closureDescriptors =
        afterCall.host.closureDescriptors) :
    BudgetedCapacityPreservingLazyStep .miss facts context callerFunction module
          hostEnv sourceExternals decl continuation
          [.globalGet (2 * cacheIndex),
            .iff 0 0 [] [
              .call declarationId,
              .call cacheSetId,
              .globalSet (2 * cacheIndex + 1),
              .const 1,
              .globalSet (2 * cacheIndex)],
            .globalGet (2 * cacheIndex + 1)]
          sourceRuntime nextRuntime sourceEnv sourceValue initial
          (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) locals
          nextLocals resultIndex initialWitness callWitness physical stepCost ∧
      LazyCacheGlobalsRel callWitness sourceModule nextRuntime
        (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) := by
  have paramsEq : sourceDeclaration.params.isEmpty = true := by
    simp [declarationParams]
  obtain ⟨initializerFound, signature⟩ :=
    generated.select kindEq declarationFound paramsEq cacheEq
  have publicationRuntimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue :=
    (SourceLazyLetResult.miss_cacheFacts_of_callee declValue declarationFound
      declarationParams declarationBody sourceStep
      (contexts.sourceCodeResult
        callee.declaration.capacityPreserving.successful.sourceResult)).2
  have step :
      BudgetedCapacityPreservingLazyStep .miss facts context callerFunction
        module hostEnv sourceExternals decl continuation
        [.globalGet (2 * cacheIndex),
          .iff 0 0 [] [
            .call declarationId,
            .call cacheSetId,
            .globalSet (2 * cacheIndex + 1),
            .const 1,
            .globalSet (2 * cacheIndex)],
          .globalGet (2 * cacheIndex + 1)]
        sourceRuntime nextRuntime sourceEnv sourceValue initial
        (writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)) locals
        nextLocals resultIndex initialWitness callWitness physical stepCost :=
    BudgetedCapacityPreservingLazyStep.miss_of_budgetedDeclaration_cacheSet
      sourceStep declValue initialRelated cacheTable generated kindEq cacheEq
      rfl declarationFound declarationParams declarationBody
      contexts callee.declaration importFound hostSatisfies importInBounds
      contractFound parameterCount resultCount operation valueGlobal
      valueStoreEq flagGlobal (by omega) resultFound resultKindAt targetSet
      publicationOrdinary resultKindEq cacheFound cacheKindEq cacheDescriptorsEq
      publicationExternals publicationDispatch publicationDescriptors
  exact step.withCacheSetPublishedTable callee.cacheTable operation
    initializerFound signature publicationRuntimeEq
    (by simpa [resultKindEq] using
      callee.declaration.capacityPreserving.successful.valueRelated)
    valueStoreEq

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
the whole source/Wasm cache-table relation and explicit agreement of both
immutable closure tables. Non-cache operations transport the cache table and
closure tables independently; hit/miss operations additionally supply their
path-specific cache transition.
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
    LazyCacheGlobalsRel witness sourceModule sourceRuntime targetStore ∧
    ClosureTablesAgree targetStore witness

/-- The canonical cache frame retains the facts-indexed concrete/source state
relation used by every structural operation family. -/
theorem ConcreteReuseCapacityCacheFrame.stateRelated
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness) :
    ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness :=
  invariant.1.1.1.1

/-- The resource index of the canonical cache frame is the concrete wasm32
address-space headroom owned by the current execution suffix. -/
theorem ConcreteReuseCapacityCacheFrame.budget
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness) :
    targetStore.host.runtime.heap.AddressSpaceBudget remainingBytes :=
  invariant.1.1.1.2.2.2

/--
Replace only the address-space resource index of a canonical cache frame.

All representation, ownership, handler, cache, and immutable-table fields are
independent of the numeric budget. This constructor lets a hereditary proof
re-run the same generated declaration with arbitrary caller-owned slack.
-/
theorem ConcreteReuseCapacityCacheFrame.withBudget
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {beforeBytes afterBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts beforeBytes sourceRuntime sourceEnv targetStore targetLocals
        witness)
    (budget :
      targetStore.host.runtime.heap.AddressSpaceBudget afterBytes) :
    ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals facts
      afterBytes sourceRuntime sourceEnv targetStore targetLocals witness := by
  rcases invariant with
    ⟨⟨⟨⟨related, ordinary, aligned, _⟩, integer, natural, scalar⟩,
      descriptors⟩, cache, closureTables⟩
  exact
    ⟨⟨⟨⟨related, ordinary, aligned, budget⟩, integer, natural, scalar⟩,
      descriptors⟩, cache, closureTables⟩

/--
The canonical cache frame resolves an exact generated closure matcher without
an additional host/witness table premise.

This is the direct regression boundary for closure dispatch inside a cached
declaration body: the ordinary state relation supplies the local/address
mapping and the frame supplies both immutable table equations.
-/
theorem ConcreteReuseCapacityCacheFrame.resolveClosureMatcher
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : FVarId}
    {closureIndex : Nat}
    {closureKind : AbiKind}
    {location : Location}
    {cell : HeapCell}
    {function expectedFunction : Name}
    {arity expectedArity expectedFixed : Nat}
    {captures : Array Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (sourceLookup :
      lookup sourceEnv closureId = some (.object (.heap location)))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (closureKindAt :
      (functionBindings sourceFunction)[closureIndex]?.map Prod.snd =
        some closureKind)
    (cellFound : findCell? sourceRuntime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures) :
    ∃ address : Word32,
      locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        (∀ results next,
          closureMatchesStep expectedFunction expectedArity expectedFixed initial
              [.i32 (UInt32.ofNat address.value)] = .Return results next →
            results = [
              .i32 (if function == expectedFunction && arity == expectedArity &&
                captures.size == expectedFixed then 1 else 0)]) ∧
        closureData sourceRuntime (.object (.heap location)) =
          .ok (function, arity, captures) :=
  invariant.1.1.1.1.stateRelated.resolveClosureMatcher
    invariant.2.2.dispatch invariant.2.2.descriptors.symm sourceLookup
    closureFound closureKindAt cellFound cellLive cellObjectEq

/-- Execute one known successful closure matcher and re-establish the complete
cache/ownership frame at the semantic post-consumption runtime. In particular,
the resulting store is generally *not* the initial store: exclusive and
shared applications update ownership, while the closure snapshot records the
fixed captures used by the generated projection prefix. -/
theorem ConcreteReuseCapacityCacheFrame.closureMatchesStep_hit
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {location : Location}
    {address : Word32}
    {cell : HeapCell}
    {function expectedFunction : Name}
    {arity expectedArity expectedFixed : Nat}
    {captures : Array Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (identityTrue :
      (function == expectedFunction && arity == expectedArity &&
        captures.size == expectedFixed) = true)
    (sharedCapacity : ∀ parentRuntime,
      setCell sourceRuntime location { cell with rc := cell.rc - 1 } =
          .ok parentRuntime →
        ClosureRetainCapacity parentRuntime captures.toList)
    (semanticOperation :
      Fir.LeanIR.Impure.takeClosureApplication sourceRuntime location =
        .ok (nextRuntime, function, arity, captures)) :
    ∃ (next : Wasm.Store Host) (application : ClosureApplication)
        (captureKinds : Array AbiKind),
      closureMatchesStep expectedFunction expectedArity expectedFixed initial
          [.i32 (UInt32.ofNat address.value)] =
        .Return [.i32 1] next ∧
      next.host.closureApplication? = some application ∧
      ClosureApplicationRel witness application address function arity
        captureKinds captures ∧
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes nextRuntime sourceEnv next locals witness := by
  rcases invariant with
    ⟨⟨⟨⟨related, ordinary, aligned, budget⟩, integer, natural,
      scalar⟩, descriptors⟩, cache, closureTables⟩
  obtain ⟨next, application, captureKinds, concrete, snapshot,
      applicationRelated, runtimeRelated, capacity, cursor, storeFrame⟩ :=
    closureMatchesStep_hit_of_refines related.1.1 closureTables.dispatch
      closureTables.descriptors.symm mapped found live objectEq identityTrue
      sharedCapacity semanticOperation
  have nextRelated :
      ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv next
        locals witness :=
    related.transportSameWitness
      ⟨runtimeRelated, storeFrame.failureClear, related.1.2.2⟩ capacity
  have nextOrdinary :
      ReuseTokenOrdinaryRel facts nextRuntime sourceEnv :=
    ordinary.transport
      (takeClosureApplication_ordinaryPersistenceTransport semanticOperation)
  have nextBudget :
      next.host.runtime.heap.AddressSpaceBudget remainingBytes :=
    budget.of_heapCursor_eq cursor
  have nextInteger :
      next.host.externals.IntegerResultRefines externals := by
    rw [storeFrame.externals]
    exact integer
  have nextNatural :
      ConcreteExternalImpl.NaturalResultRefines next.host.externals
        externals := by
    rw [storeFrame.externals]
    exact natural
  have nextScalar :
      ConcreteExternalImpl.ScalarResultRefines next.host.externals
        externals := by
    rw [storeFrame.externals]
    exact scalar
  have nextDescriptors :
      next.host.closureDescriptors = witness.closureDescriptors :=
    storeFrame.descriptors.trans descriptors
  have runtimeAux := takeClosureApplication_runtimeAux semanticOperation
  have nextCache :
      LazyCacheGlobalsRel witness sourceModule nextRuntime next :=
    cache.transport (WitnessTransport.refl witness) runtimeAux.globals
      storeFrame.wasmGlobals storeFrame.hostStaticLayout
  have nextClosureTables : ClosureTablesAgree next witness := {
    dispatch := closureTables.dispatch.trans storeFrame.dispatch.symm
    descriptors := storeFrame.descriptors.trans closureTables.descriptors }
  exact ⟨next, application, captureKinds, concrete, snapshot,
    applicationRelated,
    ⟨⟨⟨⟨nextRelated, nextOrdinary, aligned, nextBudget⟩, nextInteger,
      nextNatural, nextScalar⟩, nextDescriptors⟩, nextCache,
      nextClosureTables⟩⟩

/-- A candidate selected by the executable matcher has the semantic closure
identity, and its recorded successor store carries the complete
post-consumption frame. This removes the historical `selected.nextStore =
initial` shortcut while retaining the candidate-chain interface. -/
theorem ConcreteReuseCapacityCacheFrame.selectedClosureMatcher
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime callRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : FVarId}
    {closureIndex : Nat}
    {location : Location}
    {address : Word32}
    {cell : HeapCell}
    {function : Name}
    {arity : Nat}
    {captures : Array Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (selected :
      ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? sourceRuntime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (selectedMatches : (selected.matched != 0) = true)
    (sharedCapacity : ∀ parentRuntime,
      setCell sourceRuntime location { cell with rc := cell.rc - 1 } =
          .ok parentRuntime →
        ClosureRetainCapacity parentRuntime captures.toList)
    (semanticOperation :
      Fir.LeanIR.Impure.takeClosureApplication sourceRuntime location =
        .ok (callRuntime, function, arity, captures)) :
    (function == selected.function && arity == selected.arity &&
        captures.size == selected.fixed) = true ∧
      ∃ (application : ClosureApplication) (captureKinds : Array AbiKind),
        selected.nextStore.host.closureApplication? = some application ∧
        ClosureApplicationRel witness application address function arity
          captureKinds captures ∧
        ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
          facts remainingBytes callRuntime sourceEnv selected.nextStore locals
          witness := by
  have matchedEq :=
    selected.matched_eq_of_refines invariant.stateRelated.1.1
      invariant.2.2.dispatch invariant.2.2.descriptors.symm mapped found live
      objectEq
  have identityTrue :
      (function == selected.function && arity == selected.arity &&
        captures.size == selected.fixed) = true := by
    by_contra identityNotTrue
    have identityFalse :
        (function == selected.function && arity == selected.arity &&
          captures.size == selected.fixed) = false :=
      Bool.eq_false_of_not_eq_true identityNotTrue
    rw [matchedEq, identityFalse] at selectedMatches
    simp at selectedMatches
  obtain ⟨next, application, captureKinds, concrete, snapshot,
      applicationRelated, nextInvariant⟩ :=
    invariant.closureMatchesStep_hit mapped found live objectEq identityTrue
      sharedCapacity semanticOperation
  have matchedOne : selected.matched = 1 := by
    rw [matchedEq, identityTrue]
    rfl
  have selectedOperation :
      closureMatchesStep selected.function selected.arity selected.fixed initial
          [.i32 (UInt32.ofNat address.value)] =
        .Return [.i32 1] selected.nextStore := by
    simpa [matchedOne] using selected.operation
  rw [selectedOperation] at concrete
  have nextEq : selected.nextStore = next := by
    injection concrete
  subst next
  exact ⟨identityTrue, application, captureKinds, snapshot,
    applicationRelated, nextInvariant⟩

/--
The canonical cache frame also supplies the complete first-matching split for
a generated candidate family from one semantic identity-coverage fact. No
matcher bit or closure-table equation is a caller premise.
-/
theorem
    ConcreteReuseCapacityCacheFrame.closureCandidates_exists_first_match
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : FVarId}
    {closureIndex : Nat}
    {address : Word32}
    {location : Location}
    {cell : HeapCell}
    {function : Name}
    {arity : Nat}
    {captures : Array Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (mapped : witness.locations.lookup? location = some address)
    (cellFound : findCell? sourceRuntime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures)
    (containsMatch :
      ∃ candidate ∈ candidates,
        (function == candidate.function && arity == candidate.arity &&
          captures.size == candidate.fixed) = true) :
    ∃ before selected suffix,
      candidates = before ++ selected :: suffix ∧
        (∀ candidate, candidate ∈ before →
          candidate.matched = (0 : UInt32)) ∧
          (selected.matched != 0) = true :=
  closureCandidates_exists_first_match_of_refines candidates
    invariant.1.1.1.1.stateRelated.1 invariant.2.2.dispatch
    invariant.2.2.descriptors.symm mapped cellFound cellLive cellObjectEq
    containsMatch

/--
Lift a transport-strengthened direct-operation family through both the
whole-cache invariant and one fixed execution entry.

Direct readers and allocators do not publish lazy globals. Their concrete
proofs expose the witness, header-capacity, ordinaryness, source-global,
physical-global, and host-layout transports needed to preserve the complete
cache table and extend the hereditary entry relation.
-/
theorem
    ReuseCapacityDirectLetRuntimeRefinesWithCost.reuseCapacityEntryRelativeCache
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {Supported : ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {letCost : LCNF.LetDecl .impure → Nat}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness}
    (runtimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels module hostEnv Supported letCost
        (ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
          externals)) :
    ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels module hostEnv Supported letCost
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl sourceValue valueCode
    targetValue targetStore targetLocals resultIndex remainingBytes witness
    supported stepFits invariant sourceStep valueCompiled valueAdapted
    resultFound
  rcases invariant with
    ⟨⟨baseInvariant, cacheTable, closureTables⟩, entryTransports⟩
  obtain ⟨nextStore, nextLocals, nextWitness, nextFacts, step,
      externalsPreserved, hostDescriptorsPreserved,
      witnessDescriptorsPreserved, transports, factsTransfer,
      nextBaseInvariant⟩ :=
    runtimeRefines supported stepFits baseInvariant sourceStep valueCompiled
      valueAdapted resultFound
  have nextCache :
      LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore :=
    cacheTable.transport transports.witnessTransport transports.sourceGlobals
      transports.wasmGlobals transports.hostStaticLayout
  have nextClosureTables :
      ClosureTablesAgree nextStore nextWitness :=
    transports.toClosureTablesTransport.agree closureTables
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        nextStore entryWitness nextWitness :=
    entryTransports.step transports.witnessTransport transports.capacity
      transports.ordinary externalsPreserved
      transports.toClosureTablesTransport
  exact ⟨nextStore, nextLocals, nextWitness, nextFacts, step,
    externalsPreserved, hostDescriptorsPreserved, witnessDescriptorsPreserved,
    transports, factsTransfer,
    ⟨⟨nextBaseInvariant, nextCache, nextClosureTables⟩, nextEntry⟩⟩

/--
The production direct fragment instantiates the entry-relative whole-cache
law. This is the direct-operation premise used by hereditary generated
declaration proofs; target execution and cache transports are derived from
the compiler/runtime theorem.
-/
theorem
    ConcreteSupportedFunction.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    (externals : ExternalImpl)
    {labels : List FVarId}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels target.wasmModule hosts.env
      (ReuseBudgetedDirectSupported context) directLetAllocationCost
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness) :=
  ReuseCapacityDirectLetRuntimeRefinesWithCost.reuseCapacityEntryRelativeCache
    (spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership
      externals)

/--
Lift the transport-strengthened pure-external family through both the
whole-cache invariant and one fixed execution entry.

Pure result handlers may allocate a fresh `Nat`, `Int`, or scalar
representation, but they preserve the semantic global table, the physical
Wasm globals, and the concrete host's static cache layout. Those three facts
transport `LazyCacheGlobalsRel`; the existing witness, header-capacity,
ordinaryness, and immutable-table facts extend
`ReuseCapacityCodeEntryTransports`. Thus external calls can occur inside a
hereditary cached declaration without weakening or rediscovering the cache
relation.
-/
theorem
    ExternalLetRuntimeRefinesWithCostAndTransports.reuseCapacityEntryRelativeCache
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness}
    (runtimeRefines :
      ExternalLetRuntimeRefinesWithCostAndTransports context sourceModule
        sourceFunction labels module hostEnv externals ExternalSupported
        (ConcreteBudgetedPureExternalFrame sourceFunction externals))
    (factsTransfer :
      ∀ {facts : ReuseCapacityFacts}
          {sourceRuntime nextRuntime : RuntimeState}
          {sourceEnv : Env} {decl : LCNF.LetDecl .impure}
          {continuation : LCNF.Code .impure}
          {sourceValue : Value} {stepCost : Nat},
        ExternalSupported sourceRuntime sourceEnv decl continuation nextRuntime
            sourceValue stepCost →
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId)) :
    ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels module hostEnv externals ExternalSupported
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue targetStore targetLocals resultIndex remainingBytes
    stepCost witness supported stepFits invariant sourceStep valueCompiled
    valueAdapted resultFound
  rcases invariant with
    ⟨⟨⟨⟨⟨capacityRelated, ordinaryTokens, frameAligned, budget⟩,
          integerImplementation, naturalImplementation,
          scalarImplementation⟩, descriptorAgreement⟩, cacheTable,
        initialClosureTables⟩,
      entryTransports⟩
  obtain ⟨nextStore, nextLocals, nextWitness, resultPhysical, step,
      externalsPreserved, closureTables, localUpdate, witnessTransport,
      capacityTransport, ordinaryTransport, runtimeGlobals, storeGlobals,
      hostStaticLayout, nextInvariant⟩ :=
    runtimeRefines supported stepFits
      ⟨⟨frameAligned, budget⟩, integerImplementation,
        naturalImplementation, scalarImplementation⟩
      sourceStep capacityRelated.1 valueCompiled valueAdapted resultFound
  rcases nextInvariant with
    ⟨⟨nextFrameAligned, nextBudget⟩, nextIntegerImplementation,
      nextNaturalImplementation, nextScalarImplementation⟩
  let nextFacts := eraseReuseCapacityFact facts decl.fvarId
  have nextCapacity :
      ReuseCapacityStateRelated nextFacts sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness := by
    simpa [nextFacts] using
      capacityRelated.eraseResult step.2.2.1 resultFound localUpdate
        witnessTransport capacityTransport
  have nextOrdinary :
      ReuseTokenOrdinaryRel nextFacts nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) := by
    simpa [nextFacts] using ordinaryTokens.eraseBind ordinaryTransport
  have nextDescriptorAgreement :
      nextStore.host.closureDescriptors =
        nextWitness.closureDescriptors :=
    closureTables.hostDescriptorsPreserved.trans
      (descriptorAgreement.trans
        closureTables.witnessDescriptorsPreserved.symm)
  have nextCache :
      LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore :=
    cacheTable.transport witnessTransport runtimeGlobals storeGlobals
      hostStaticLayout
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        nextStore entryWitness nextWitness :=
    entryTransports.step witnessTransport capacityTransport ordinaryTransport
      externalsPreserved closureTables
  have nextClosureTables :
      ClosureTablesAgree nextStore nextWitness :=
    closureTables.agree initialClosureTables
  exact ⟨nextStore, nextLocals, nextWitness, nextFacts, step,
    externalsPreserved, closureTables.hostDescriptorsPreserved,
    closureTables.witnessDescriptorsPreserved,
    factsTransfer supported,
    ⟨⟨⟨⟨nextCapacity, nextOrdinary, nextFrameAligned, nextBudget⟩,
          nextIntegerImplementation, nextNaturalImplementation,
          nextScalarImplementation⟩, nextDescriptorAgreement⟩, nextCache,
        nextClosureTables⟩,
      nextEntry⟩

/--
Production pure externals instantiate the entry-relative whole-cache law.

This is the external operation-family argument expected by
`codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelativeWithSlack` when a
generated internal declaration is proved from its actual compiler output.
-/
theorem
    ConcreteSupportedFunction.reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    (externals : ExternalImpl)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
      sourceFunction [] target.wasmModule hosts.env externals
      (PureExternalSupported context externals)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness) :=
  ExternalLetRuntimeRefinesWithCostAndTransports.reuseCapacityEntryRelativeCache
    (spec.externalLetRuntimeRefinesWithCostAndTransports_pureExternal externals)
    (fun supported => supported.reuseCapacityLetFacts? _)

/--
Lift any transport-strengthened no-result effect family through both the
whole-cache invariant and one fixed execution entry.

Effects do not bind a destination or change the validator fact map. Their
transport package proves that both cache global tables and the host cache
layout are unchanged, while its witness/header/ordinaryness and descriptor
facts extend the hereditary entry relation. The result is the ordinary
structural effect law over the entry-relative cache frame; callers provide an
operation-family theorem, never a target execution.
-/
theorem
    EffectRuntimeRefinesWithTransports.reuseCapacityEntryRelativeCache
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {EffectSupported : EffectSupportedPredicate}
    {facts : ReuseCapacityFacts}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness}
    (runtimeRefines :
      EffectRuntimeRefinesWithTransports context sourceModule sourceFunction
        labels module hostEnv EffectSupported
        (ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
          externals facts)) :
    EffectRuntimeRefines context sourceModule sourceFunction labels module
      hostEnv EffectSupported
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts) := by
  intro sourceRuntime nextRuntime sourceEnv code continuation target targetStore
    targetLocals remainingBytes witness supported sourceStep stateRelated
    invariant adapted
  rcases invariant with
    ⟨⟨baseInvariant, cacheTable, closureTables⟩, entryTransports⟩
  obtain ⟨targetRest, nextStore, nextWitness, continuationAdapted, step,
      externalsPreserved, transports, nextBaseInvariant⟩ :=
    runtimeRefines supported sourceStep stateRelated baseInvariant adapted
  have nextCache :
      LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore :=
    cacheTable.transport transports.witnessTransport transports.sourceGlobals
      transports.wasmGlobals transports.hostStaticLayout
  have nextClosureTables :
      ClosureTablesAgree nextStore nextWitness :=
    transports.toClosureTablesTransport.agree closureTables
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        nextStore entryWitness nextWitness :=
    entryTransports.step transports.witnessTransport transports.capacity
      transports.ordinary externalsPreserved
      transports.toClosureTablesTransport
  exact ⟨targetRest, nextStore, nextWitness, continuationAdapted, step,
    externalsPreserved,
    ⟨⟨nextBaseInvariant, nextCache, nextClosureTables⟩, nextEntry⟩⟩

/--
The complete production no-result family instantiates the entry-relative
whole-cache effect law.

This is the effect premise consumed by hereditary generated declaration
proofs. All execution, compiler inversion, and representation transport come
from the reusable production operation theorems.
-/
theorem
    ConcreteSupportedFunction.effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    (externals : ExternalImpl)
    {labels : List FVarId}
    {facts : ReuseCapacityFacts}
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    EffectRuntimeRefines context sourceModule sourceFunction labels
      target.wasmModule hosts.env
      (OwnershipTagAndAllFieldMutationEffectSupported context)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts) :=
  EffectRuntimeRefinesWithTransports.reuseCapacityEntryRelativeCache
    (spec.effectRuntimeRefinesWithTransports_reuseOwnershipTagAndAllFieldMutation_pureExternal
      externals)

/--
Uniform cache-aware implementation condition for direct generated declaration
calls.

This is the interprocedural analogue of
`DirectDeclarationCallImplementation`: the recursive callee theorem returns
the evolved whole-cache relation together with ordinary declaration
correctness. The caller still supplies only source admission, actual
compiler/adapter outputs, and its current representation/cache relations.
-/
def DirectDeclarationCallImplementationWithCache
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
      {resultIndex remainingBytes stepCost : Nat}
      {initialWitness : RefinementWitness},
    CallSupported sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      stepCost ≤ remainingBytes →
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue →
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule callerFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex →
      ∃ calleeContext : Fir.Wasm.Context,
        ∃ calleeFunction calleeEnv calleeCode targetFunction functionIndex
          argumentTarget afterCall updated resultWitness physicalArgs
          resultKind physical,
        DeclarationContextsCoherent context calleeContext ∧
          targetValue = argumentTarget ++ [.call functionIndex] ∧
          (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
            some resultKind ∧
          ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
            initial locals ∧
          BudgetedCapacityPreservingSuccessfulDeclarationWithCache
            calleeContext sourceModule calleeFunction module hostEnv sourceExternals
            sourceRuntime nextRuntime calleeEnv calleeCode targetFunction
            functionIndex initial afterCall initialWitness resultWitness
            physicalArgs.reverse resultKind sourceValue physical stepCost ∧
          locals.set? resultIndex physical = some updated ∧
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId)

/--
A cache-aware direct declaration implementation supplies the complete call
law over one fixed execution entry.

The callee's evolved table becomes the successor cache invariant. Its
witness, capacity, ordinaryness, and immutable-table transports extend the
entry-to-current package, so no unchanged-global premise or target execution
certificate is introduced.
-/
theorem DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative
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
      DirectDeclarationCallImplementationWithCache context sourceModule
        callerFunction labels module hostEnv sourceExternals CallSupported)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
      callerFunction labels module hostEnv sourceExternals CallSupported
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule callerFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue initial locals resultIndex remainingBytes stepCost
    initialWitness supported stepFits invariant sourceStep valueCompiled
    valueAdapted resultFound
  rcases invariant with ⟨cacheInvariant, entryTransports⟩
  obtain ⟨calleeContext, calleeFunction, calleeEnv, calleeCode, targetFunction,
      functionIndex, argumentTarget, afterCall, updated, resultWitness,
      physicalArgs, resultKind, physical, _contexts, targetEq, resultKindAt,
      assembled, callee, targetSet, transfer⟩ :=
    implementation supported stepFits sourceStep cacheInvariant valueCompiled
      valueAdapted resultFound
  subst targetValue
  obtain ⟨step, externalsPreserved, hostDescriptorsPreserved,
      witnessDescriptorsPreserved, nextTransfer, nextBaseInvariant⟩ :=
    cacheInvariant.1.ofDirectDeclarationCallExact stepFits sourceStep
      resultFound resultKindAt assembled callee.declaration targetSet transfer
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        afterCall entryWitness resultWitness :=
    entryTransports.step
      callee.declaration.capacityPreserving.witnessTransport
      callee.declaration.capacityPreserving.capacityTransport
      callee.declaration.ordinaryTransport
      callee.declaration.externalsPreserved
      callee.declaration.toClosureTablesTransport
  have nextClosureTables :
      ClosureTablesAgree afterCall resultWitness :=
    callee.declaration.toClosureTablesTransport.agree cacheInvariant.2.2
  exact ⟨afterCall, updated, resultWitness,
    eraseReuseCapacityFact facts decl.fvarId, step,
    externalsPreserved, hostDescriptorsPreserved, witnessDescriptorsPreserved,
    nextTransfer,
    ⟨⟨nextBaseInvariant, callee.cacheTable, nextClosureTables⟩, nextEntry⟩⟩

/--
Exact declaration-local data computed by one successful production
`lowerDecl` call.

This is deliberately a view of the executable compiler, not a second lowering
relation. Keeping the declaration-local context explicit lets a hereditary
source derivation name exactly the context that production selection will
recover, rather than merely an arbitrary context coherent with its caller.
-/
structure LoweredInternalDeclaration
    (program : Fir.LeanIR.ImpureProgram)
    (cachedDeclarations : Array Name)
    (declaration : LCNF.Decl .impure)
    (sourceCode : LCNF.Code .impure)
    (sourceFunction : Fir.Wasm.Function) where
  paramLocals : Fir.Wasm.LocalKinds
  bodyLocals : Fir.Wasm.LocalKinds
  symbolicBody : List Fir.Wasm.Instruction
  abiResults : Array AbiKind
  bodyEq : declaration.value = .code sourceCode
  paramsAdded :
    Fir.Wasm.addDeclarationParams program declaration = .ok paramLocals
  localsCollected :
    Fir.Wasm.collectLocals [] sourceCode = .ok bodyLocals
  bodyCompiled :
    Fir.Wasm.compileCode {
        program
        localKinds := paramLocals.reverse ++ bodyLocals.reverse
        cachedDeclarations } sourceCode = .ok symbolicBody
  resultsCompiled :
    Fir.Wasm.resultKinds declaration.type = .ok abiResults
  sourceFunctionEq :
    sourceFunction = {
      name := declaration.name
      params := paramLocals.reverse.toArray
      results := abiResults
      locals := bodyLocals.reverse.toArray
      body := symbolicBody }

/-- The canonical binding row shared by symbolic compilation and adaptation. -/
def LoweredInternalDeclaration.localKinds
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction) : Fir.Wasm.LocalKinds :=
  row.paramLocals.reverse ++ row.bodyLocals.reverse

/-- The exact declaration-local context used by production lowering. -/
def LoweredInternalDeclaration.context
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction) : Fir.Wasm.Context := {
  program
  localKinds := row.localKinds
  cachedDeclarations }

/-- The selected source function body is compiled in its canonical context. -/
theorem LoweredInternalDeclaration.compileCode
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction) :
    Fir.Wasm.compileCode row.context sourceCode =
      .ok sourceFunction.body := by
  change
    Fir.Wasm.compileCode {
        program
        localKinds := row.localKinds
        cachedDeclarations } sourceCode = .ok sourceFunction.body
  have bodyEq : sourceFunction.body = row.symbolicBody := by
    simpa using congrArg Fir.Wasm.Function.body row.sourceFunctionEq
  rw [bodyEq]
  exact row.bodyCompiled

/-- A canonical lowered declaration shares exactly the module-wide context
fields with the caller. -/
theorem LoweredInternalDeclaration.contextsCoherent
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction)
    {caller : Fir.Wasm.Context}
    (callerProgram : caller.program = program)
    (callerCaches : caller.cachedDeclarations = cachedDeclarations) :
    DeclarationContextsCoherent caller row.context := {
  program := callerProgram
  cachedDeclarations := callerCaches }

/--
Source/static admission for one saturated internal named call.

The relation retains the actual `compileArgs` and `evalArgs` equations because
they identify the source parameters, but contains no numeric target index,
physical argument, store, witness, target execution, or translation
certificate. The successful `bindParams` equation rules out both
underapplication and overapplication; `nonCached` separates ordinary calls
from the nullary lazy-cache family.
-/
structure DirectInternalCallSite
    (context : Fir.Wasm.Context)
    (decl : LCNF.LetDecl .impure)
    (sourceEnv : Env) where
  declaration : Name
  sourceDeclaration : LCNF.Decl .impure
  calleeCode : LCNF.Code .impure
  calleeEnv : Env
  resultKind : AbiKind
  parameterKinds : Array AbiKind
  calleeResultKind : AbiKind
  args : Array (LCNF.Arg .impure)
  argumentCode : List Fir.Wasm.Instruction
  argumentKinds : Array AbiKind
  semanticArgs : Array Value
  valueEq : decl.value = .fap declaration args
  kindEq : Fir.Wasm.checkedAbiKind decl.type = .ok resultKind
  declarationFound :
    context.program.findDecl? declaration = some sourceDeclaration
  parametersKnown :
    Fir.Wasm.declarationParameterKinds? context.program sourceDeclaration =
      some parameterKinds
  argumentsRefine :
    Fir.Wasm.kindsRefine argumentKinds parameterKinds = true
  calleeResult :
    Fir.Wasm.directAbiKind? sourceDeclaration.type = some calleeResultKind
  calleeResultRefines : calleeResultKind.refines resultKind = true
  nonCached :
    (args.isEmpty && sourceDeclaration.params.isEmpty) = false
  bodyEq : sourceDeclaration.value = .code calleeCode
  argumentsCompiled :
    Fir.Wasm.compileArgs context args =
      .ok (argumentCode, argumentKinds)
  argumentsEvaluated :
    evalArgs sourceEnv args = .ok semanticArgs
  parametersBound :
    bindParams sourceDeclaration.params semanticArgs = .ok calleeEnv
  resultCompiled :
    Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, resultKind)

private theorem listMapM_length_of_ok_for_directCall
    {α β ε : Type} (items : List α) (action : α → Except ε β)
    (results : List β) (found : items.mapM action = .ok results) :
    results.length = items.length := by
  induction items generalizing results with
  | nil =>
      change Except.ok [] = Except.ok results at found
      have resultsEq : ([] : List β) = results := Except.ok.inj found
      subst results
      rfl
  | cons item items ih =>
      rw [List.mapM_cons] at found
      cases itemResult : action item with
      | error fault =>
          rw [itemResult] at found
          contradiction
      | ok value =>
          rw [itemResult] at found
          cases restResult : items.mapM action with
          | error fault =>
              rw [restResult] at found
              contradiction
          | ok rest =>
              rw [restResult] at found
              have resultsEq : value :: rest = results := Except.ok.inj found
              subst results
              simp [ih rest restResult]

/--
A finite execution of the admitted direct callee reconstructs the ordinary
source call prefix seen by the caller.

The call-site equations supply the two staging steps. The isolated callee
execution is lifted beneath the caller's binding frame, and the final yielded
value resumes the continuation. Thus a hereditary source derivation need not
store a second opaque `SourceCallLetResult` witness beside the callee body.
-/
theorem DirectInternalCallSite.sourceCallLetResult
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    (site : DirectInternalCallSite callerContext decl sourceEnv)
    (contexts : DeclarationContextsCoherent callerContext calleeContext)
    (calleeResult :
      SourceCodeResult calleeContext sourceExternals sourceRuntime
        site.calleeEnv site.calleeCode nextRuntime sourceValue) :
    SourceCallLetResult callerContext sourceExternals sourceRuntime sourceEnv
      decl continuation nextRuntime sourceValue := by
  have argumentSize : site.semanticArgs.size = site.args.size := by
    have evaluated := site.argumentsEvaluated
    unfold evalArgs at evaluated
    rw [Array.mapM_eq_mapM_toList] at evaluated
    cases listResult : site.args.toList.mapM (evalArg sourceEnv) with
    | error fault =>
        rw [listResult] at evaluated
        contradiction
    | ok results =>
        rw [listResult] at evaluated
        have valuesEq : results.toArray = site.semanticArgs :=
          Except.ok.inj evaluated
        rw [← valuesEq]
        simpa using
          listMapM_length_of_ok_for_directCall site.args.toList
            (evalArg sourceEnv) results listResult
  have parameterSize :
      site.semanticArgs.size = site.sourceDeclaration.params.size := by
    by_contra different
    have sizeTest :
        (site.sourceDeclaration.params.size == site.semanticArgs.size) =
          false := beq_eq_false_iff_ne.mpr (Ne.symm different)
    have bound := site.parametersBound
    unfold bindParams at bound
    simp [sizeTest] at bound
  have callArgs :
      site.semanticArgs.extract 0 site.sourceDeclaration.params.size =
        site.semanticArgs := by
    simp [← parameterSize]
  have extraArgs :
      site.semanticArgs.extract site.sourceDeclaration.params.size
          site.semanticArgs.size =
        #[] := by
    simp [← parameterSize]
  have argumentsNonempty : site.semanticArgs.isEmpty = false := by
    simpa [Array.isEmpty, ← argumentSize, ← parameterSize] using site.nonCached
  have staged :
      executeStep sourceExternals {
          program := callerContext.program
          control := .code (.let decl continuation)
          env := sourceEnv
          runtime := sourceRuntime } =
        .next {
          program := callerContext.program
          control := .invokeName site.declaration site.semanticArgs
          env := sourceEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } := by
    simp [executeStep, coreStep, evalLetValue, site.valueEq,
      site.argumentsEvaluated, pushBindFrame]
  have entered :
      executeStep sourceExternals {
          program := callerContext.program
          control := .invokeName site.declaration site.semanticArgs
          env := sourceEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } =
        .next {
          program := callerContext.program
          control := .code site.calleeCode
          env := site.calleeEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } := by
    simp [executeStep, coreStep, invokeDecl, site.declarationFound,
      argumentsNonempty, parameterSize, callArgs, extraArgs,
      site.parametersBound, site.bodyEq]
  have callerResult :=
    DeclarationContextsCoherent.sourceCodeResult contexts calleeResult
  rcases callerResult with ⟨calleeCount, resultEnv, calleeSteps⟩
  have protectedSteps :
      ExecSteps sourceExternals calleeCount {
          program := callerContext.program
          control := .code site.calleeCode
          env := site.calleeEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } {
          program := callerContext.program
          control := .yielded sourceValue
          env := resultEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := nextRuntime } := by
    simpa [sourceCodeState, sourceYieldState, withFrameSuffix] using
      (FirTalos.Correctness.ExecSteps.withFrameSuffix calleeSteps
        (suffix := [.bind decl.fvarId continuation sourceEnv []]))
  have resumed :
      executeStep sourceExternals {
          program := callerContext.program
          control := .yielded sourceValue
          env := resultEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := nextRuntime } =
        .next {
          program := callerContext.program
          control := .code continuation
          env := bind sourceEnv decl.fvarId sourceValue
          runtime := nextRuntime } := by
    simp [executeStep, coreStep]
  have callPrefix :
      ExecSteps sourceExternals 2 {
          program := callerContext.program
          control := .code (.let decl continuation)
          env := sourceEnv
          runtime := sourceRuntime } {
          program := callerContext.program
          control := .code site.calleeCode
          env := site.calleeEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } :=
    .step staged (.step entered (.refl _))
  obtain ⟨withCalleeCount, withCallee⟩ :=
    FirTalos.Correctness.ExecSteps.trans callPrefix protectedSteps
  obtain ⟨count, steps⟩ :=
    FirTalos.Correctness.ExecSteps.trans withCallee
      (.step resumed (.refl _))
  exact ⟨count, steps⟩

/--
Source-only finite evaluation with hereditary direct calls.

Unlike `ReuseCapacityBudgetedCodeEvaluates.callLet`, the direct-call
constructor does not hide the callee behind an arbitrary support predicate.
It contains the admitted source/static call site, a finite derivation of the
callee body at empty entry facts, and a finite derivation of the caller
continuation. Recursive calls use the exact declaration-local context exposed
by the executable source lowerer; the derivation contains no target program,
store, witness, execution, or translation certificate.

The result-ABI index is also source/static evidence. A terminal return records
the ABI kind assigned to its local by `getLocal` and requires that kind to
refine the enclosing declaration's expected result. This is the invariant
needed to relate the returned physical lane at the declaration boundary.

External calls and lazy paths remain explicit source steps for now. Saturated
closure dispatch and hereditary lazy misses will receive analogous nested
constructors after the direct-call induction is closed.
-/
inductive ReuseCapacityDirectHereditaryCodeEvaluates
    (externals : ExternalImpl)
    (DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop)
    (LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop)
    (CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop)
    (EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate)
    (letCost : LCNF.LetDecl .impure → Nat) :
    Fir.Wasm.Context → AbiKind → ReuseCapacityFacts → RuntimeState → Env →
      LCNF.Code .impure → ReuseCapacityFacts → RuntimeState → Env → Value →
        Nat → Prop where
  | ret
      {actualResultKind : AbiKind}
      (sourceLookup : lookup sourceEnv result = some sourceValue)
      (resultCompiled :
        Fir.Wasm.getLocal context result =
          .ok (.localGet result, actualResultKind))
      (resultRefines : actualResultKind.refines expectedResult = true) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv (.return result)
        facts sourceRuntime sourceEnv sourceValue 0
  | letValue
      (supported : DirectSupported context facts decl)
      (sourceStep :
        SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
          sourceValue)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost context expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv
        (.let decl continuation) resultFacts resultRuntime resultEnv resultValue
        (letCost decl + continuationCost)
  | externalLet
      (supported :
        ExternalSupported context sourceRuntime sourceEnv decl continuation
          nextRuntime sourceValue stepCost)
      (sourceStep :
        SourceExternalLetResult context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost context expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv
        (.let decl continuation) resultFacts resultRuntime resultEnv resultValue
        (stepCost + continuationCost)
  | directCallLet
      {calleeFunction : Fir.Wasm.Function}
      (site : DirectInternalCallSite context decl sourceEnv)
      (row :
        LoweredInternalDeclaration context.program context.cachedDeclarations
          site.sourceDeclaration site.calleeCode calleeFunction)
      (callee :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost row.context site.calleeResultKind [] sourceRuntime
          site.calleeEnv site.calleeCode
          calleeResultFacts nextRuntime calleeResultEnv sourceValue stepCost)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost context expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv
        (.let decl continuation) resultFacts resultRuntime resultEnv resultValue
        (stepCost + continuationCost)
  | lazyLet
      (path : LazyCachePath)
      (supported :
        LazySupported context path sourceRuntime sourceEnv decl continuation
          nextRuntime sourceValue stepCost)
      (sourceStep :
        SourceLazyLetResult path context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost context expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv
        (.let decl continuation) resultFacts resultRuntime resultEnv resultValue
        (stepCost + continuationCost)
  | caseOf
      (supported : CaseSupported context sourceRuntime sourceEnv cases selected)
      (sourceStep : SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost context expectedResult facts sourceRuntime sourceEnv selected
          resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv (.cases cases)
        resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | effect
      (supported :
        EffectSupported context sourceRuntime sourceEnv code continuation
          nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost context expectedResult facts nextRuntime sourceEnv continuation
          resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes

/-- The support payload exposed to the generic structural call theorem. -/
inductive ReuseCapacityDirectHereditaryCallSupported
    (externals : ExternalImpl)
    (DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop)
    (LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop)
    (CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop)
    (EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate)
    (letCost : LCNF.LetDecl .impure → Nat)
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (decl : LCNF.LetDecl .impure) (_continuation : LCNF.Code .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) (stepCost : Nat) : Prop where
  | intro
      {calleeFunction : Fir.Wasm.Function}
      {calleeResultFacts : ReuseCapacityFacts}
      {calleeResultEnv : Env}
      (site : DirectInternalCallSite context decl sourceEnv)
      (row :
        LoweredInternalDeclaration context.program context.cachedDeclarations
          site.sourceDeclaration site.calleeCode calleeFunction)
      (callee :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost row.context site.calleeResultKind [] sourceRuntime
          site.calleeEnv site.calleeCode calleeResultFacts nextRuntime
          calleeResultEnv sourceValue stepCost) :
      ReuseCapacityDirectHereditaryCallSupported externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context sourceRuntime sourceEnv decl _continuation nextRuntime
        sourceValue stepCost

/-- Forget nested derivations to the existing mixed finite-evaluation form. -/
theorem ReuseCapacityDirectHereditaryCodeEvaluates.toBudgeted
    {externals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {letCost : LCNF.LetDecl .impure → Nat}
    {context : Fir.Wasm.Context}
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value} {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv sourceCode
        resultFacts resultRuntime resultEnv resultValue requiredBytes) :
    ReuseCapacityBudgetedCodeEvaluates context externals
      (DirectSupported context) (ExternalSupported context)
      (ReuseCapacityDirectHereditaryCallSupported externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context)
      (LazySupported context) (CaseSupported context)
      (EffectSupported context) letCost facts sourceRuntime sourceEnv sourceCode
      resultFacts resultRuntime resultEnv resultValue requiredBytes := by
  induction evaluation with
  | ret sourceLookup _resultCompiled _resultRefines => exact .ret sourceLookup
  | letValue supported sourceStep transfer _ ih =>
      exact .letValue supported sourceStep transfer ih
  | externalLet supported sourceStep transfer _ ih =>
      exact .externalLet supported sourceStep transfer ih
  | @directCallLet callContext decl sourceEnv sourceRuntime calleeResultFacts
      nextRuntime calleeResultEnv sourceValue stepCost facts nextFacts
      expectedResult continuation resultFacts resultRuntime resultEnv resultValue
      continuationCost calleeFunction site row callee transfer continued calleeIH
      continuedIH =>
      have contexts : DeclarationContextsCoherent callContext row.context :=
        row.contextsCoherent rfl rfl
      exact .callLet
        (.intro site row callee)
        (site.sourceCallLetResult contexts calleeIH.sourceResult)
        transfer continuedIH
  | lazyLet path supported sourceStep transfer _ ih =>
      exact .lazyLet path supported sourceStep transfer ih
  | caseOf supported sourceStep _ ih =>
      exact .caseOf supported sourceStep ih
  | effect supported sourceStep _ ih =>
      exact .effect supported sourceStep ih

/-- The hereditary relation remains an exact finite source execution. -/
theorem ReuseCapacityDirectHereditaryCodeEvaluates.sourceResult
    {externals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {letCost : LCNF.LetDecl .impure → Nat}
    {context : Fir.Wasm.Context}
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {sourceCode : LCNF.Code .impure}
    {resultValue : Value} {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context expectedResult facts sourceRuntime sourceEnv sourceCode
        resultFacts resultRuntime resultEnv resultValue requiredBytes) :
    SourceCodeResult context externals sourceRuntime sourceEnv sourceCode
      resultRuntime resultValue :=
  evaluation.toBudgeted.sourceResult

/--
The hereditary return invariant closes the declaration ABI at the concrete
lane boundary.

The compiler and adapter still determine the returned numeric local. The
source/static `getLocal` equation stored in the hereditary derivation
identifies its actual ABI kind, and the stored refinement fact widens that
lane to the enclosing declaration result kind. Arbitrary caller-owned budget
slack is untouched by a return.
-/
theorem codeWP_of_reuseCapacityDirectHereditaryReturn_withSlack
    {context : Fir.Wasm.Context}
    {expectedResult : AbiKind}
    {actualResultKind : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {result : FVarId}
    {resultValue : Value}
    {slack : Nat}
    (sourceLookup : lookup sourceEnv result = some resultValue)
    (resultCompiled :
      Fir.Wasm.getLocal context result =
        .ok (.localGet result, actualResultKind))
    (resultRefines : actualResultKind.refines expectedResult = true)
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {labels : List FVarId}
    {targetCode : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {Frame :
      ReuseCapacityFacts → Nat → RuntimeState → Env → Wasm.Store Host →
        Wasm.Locals → RefinementWitness → Prop}
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels (.return result)
        targetCode)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (invariant :
      Frame facts slack sourceRuntime sourceEnv initial locals witness)
    (frameRelated :
      ∀ {frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness},
        Frame frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
            frameWitness →
          ReuseCapacityStateRelated frameFacts sourceFunction frameRuntime
            frameEnv frameStore frameLocals frameWitness) :
    ∃ resultStore resultLocals resultWitness physical,
      CodeWP context sourceModule sourceFunction labels target.wasmModule
        hosts.env sourceRuntime sourceEnv (.return result) targetCode initial
          locals witness [] (ExactReturnControlPost resultStore physical) ∧
        Frame facts slack sourceRuntime sourceEnv resultStore resultLocals
          resultWitness ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness expectedResult physical resultValue := by
  obtain ⟨kind, resultIndex, localCompiled, resultFound, kindAt, targetEq⟩ :=
    CodeAdapted.return_eq localsAligned adapted
  have kindEq : kind = actualResultKind := by
    rw [resultCompiled] at localCompiled
    exact (congrArg Prod.snd (Except.ok.inj localCompiled)).symm
  subst kind
  have stateRelated := (frameRelated invariant).stateRelated
  obtain ⟨physical, targetLookup, valueRelated⟩ :=
    stateRelated.resolve sourceLookup resultFound kindAt
  subst targetCode
  exact ⟨initial, locals, witness, physical,
    codeWP_return_to_exactControlPost resultCompiled resultFound kindAt
      sourceLookup stateRelated targetLookup,
    invariant, stateRelated.2.1,
    valueRelated.ofRefines resultRefines⟩

/--
Structural target correctness for the ABI-indexed hereditary source judgment.

This theorem is the non-circular compiler core. It consumes uniform runtime
laws for the current generated function, follows the finite source derivation,
and returns the physical value at the enclosing declaration's exact ABI. The
call law is still an explicit parameter here; the generated-declaration
induction discharges it recursively from the nested callee derivation.
-/
theorem codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_exactResult
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {labels : List FVarId}
    {externals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {Frame :
      ReuseCapacityFacts → Nat → RuntimeState → Env → Wasm.Store Host →
        Wasm.Locals → RefinementWitness → Prop}
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {code : LCNF.Code .impure}
    {targetCode : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value} {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported
        directLetAllocationCost context expectedResult facts sourceRuntime
        sourceEnv code resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code targetCode)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (invariant :
      Frame facts requiredBytes sourceRuntime sourceEnv initial locals witness)
    (frameRelated :
      ∀ {frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness},
        Frame frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
            frameWitness →
          ReuseCapacityStateRelated frameFacts sourceFunction frameRuntime
            frameEnv frameStore frameLocals frameWitness)
    (directRuntimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env
        (DirectSupported context) directLetAllocationCost Frame)
    (externalRuntimeRefines :
      ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env externals
        (ExternalSupported context) Frame)
    (callRuntimeRefines :
      ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env externals
        (ReuseCapacityDirectHereditaryCallSupported externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          directLetAllocationCost context)
        Frame)
    (lazyRuntimeRefines :
      ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env externals
        (LazySupported context) Frame)
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction labels
        target.wasmModule hosts.env (CaseSupported context))
    (effectRuntimeRefines :
      ∀ facts,
        EffectRuntimeRefines context sourceModule sourceFunction labels
          target.wasmModule hosts.env (EffectSupported context) (Frame facts)) :
    ∃ resultStore resultLocals resultWitness physical,
      CodeWP context sourceModule sourceFunction labels target.wasmModule
          hosts.env sourceRuntime sourceEnv code targetCode initial locals
          witness [] (ExactReturnControlPost resultStore physical) ∧
        Frame resultFacts 0 resultRuntime resultEnv resultStore resultLocals
          resultWitness ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness expectedResult physical resultValue := by
  induction evaluation generalizing targetCode initial locals witness with
  | ret sourceLookup resultCompiled resultRefines =>
      exact codeWP_of_reuseCapacityDirectHereditaryReturn_withSlack
        (slack := 0) sourceLookup resultCompiled resultRefines adapted
        localsAligned invariant frameRelated
  | @letValue context facts decl sourceRuntime sourceEnv nextRuntime sourceValue
      nextFacts expectedResult continuation resultFacts resultRuntime resultEnv
      resultValue continuationCost supported sourceStep transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          directLetAllocationCost decl ≤
            directLetAllocationCost decl + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, _directTransports, producedTransfer,
          nextInvariant⟩ :=
        directRuntimeRefines supported stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          Frame nextFacts continuationCost nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih continuationAdapted localsAligned continuationInvariant
          directRuntimeRefines externalRuntimeRefines callRuntimeRefines
          lazyRuntimeRefines caseRuntimeRefines effectRuntimeRefines
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_letValue valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @externalLet context sourceRuntime sourceEnv decl continuation nextRuntime
      sourceValue stepCost facts nextFacts expectedResult resultFacts
      resultRuntime resultEnv resultValue continuationCost supported sourceStep
      transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ stepCost + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, producedTransfer, nextInvariant⟩ :=
        externalRuntimeRefines supported stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          Frame nextFacts continuationCost nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih continuationAdapted localsAligned continuationInvariant
          directRuntimeRefines externalRuntimeRefines callRuntimeRefines
          lazyRuntimeRefines caseRuntimeRefines effectRuntimeRefines
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_externalLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @directCallLet context decl sourceEnv sourceRuntime calleeResultFacts
      nextRuntime calleeResultEnv sourceValue stepCost facts nextFacts
      expectedResult continuation resultFacts resultRuntime resultEnv resultValue
      continuationCost calleeFunction site row callee transfer continued calleeIH
      continuedIH =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ stepCost + continuationCost :=
        Nat.le_add_right _ _
      have sourceStep :
          SourceCallLetResult context externals sourceRuntime sourceEnv decl
            continuation nextRuntime sourceValue :=
        site.sourceCallLetResult (row.contextsCoherent rfl rfl)
          callee.sourceResult
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, producedTransfer, nextInvariant⟩ :=
        callRuntimeRefines (.intro site row callee) stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          Frame nextFacts continuationCost nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        continuedIH continuationAdapted localsAligned continuationInvariant
          directRuntimeRefines externalRuntimeRefines callRuntimeRefines
          lazyRuntimeRefines caseRuntimeRefines effectRuntimeRefines
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_callLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @lazyLet context sourceRuntime sourceEnv decl continuation nextRuntime
      sourceValue stepCost facts nextFacts expectedResult resultFacts
      resultRuntime resultEnv resultValue continuationCost path supported
      sourceStep transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ stepCost + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, producedTransfer, nextInvariant⟩ :=
        lazyRuntimeRefines supported stepFits invariant sourceStep valueCompiled
          valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          Frame nextFacts continuationCost nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        simpa using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih continuationAdapted localsAligned continuationInvariant
          directRuntimeRefines externalRuntimeRefines callRuntimeRefines
          lazyRuntimeRefines caseRuntimeRefines effectRuntimeRefines
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_lazyLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @caseOf context sourceRuntime sourceEnv cases selected expectedResult facts
      resultFacts resultRuntime resultEnv resultValue requiredBytes supported
      sourceStep continued ih =>
      obtain ⟨selectedTarget, selectedAdapted, _selected, lift⟩ :=
        caseRuntimeRefines supported sourceStep
          (frameRelated invariant).stateRelated adapted
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih selectedAdapted localsAligned invariant directRuntimeRefines
          externalRuntimeRefines callRuntimeRefines lazyRuntimeRefines
          caseRuntimeRefines effectRuntimeRefines
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        lift [] (ExactReturnControlPost resultStore physical)
          (by
            intro continuation returned
            subst continuation
            rfl)
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @effect context sourceRuntime sourceEnv code continuation nextRuntime
      expectedResult facts resultFacts resultRuntime resultEnv resultValue
      requiredBytes supported sourceStep continued ih =>
      obtain ⟨targetRest, nextStore, nextWitness, continuationAdapted, step,
          _externalsPreserved, nextInvariant⟩ :=
        effectRuntimeRefines _ supported sourceStep
          (frameRelated invariant).stateRelated invariant adapted
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih continuationAdapted localsAligned nextInvariant directRuntimeRefines
          externalRuntimeRefines callRuntimeRefines lazyRuntimeRefines
          caseRuntimeRefines effectRuntimeRefines
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_effect step continuationWP, resultInvariant, failureClear,
        valueRelated⟩

/--
The ABI-indexed hereditary theorem preserves arbitrary caller-owned budget
slack. The source derivation accounts only for the selected path cost; the
shifted operation laws thread the additional budget through every step and
the terminal return therefore retains it unchanged.
-/
theorem codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_withSlack
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {labels : List FVarId}
    {externals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {Frame :
      ReuseCapacityFacts → Nat → RuntimeState → Env → Wasm.Store Host →
        Wasm.Locals → RefinementWitness → Prop}
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {code : LCNF.Code .impure}
    {targetCode : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {resultValue : Value} {requiredBytes slack : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported
        directLetAllocationCost context expectedResult facts sourceRuntime
        sourceEnv code resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code targetCode)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (invariant :
      Frame facts (requiredBytes + slack) sourceRuntime sourceEnv initial locals
        witness)
    (frameRelated :
      ∀ {frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness},
        Frame frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
            frameWitness →
          ReuseCapacityStateRelated frameFacts sourceFunction frameRuntime
            frameEnv frameStore frameLocals frameWitness)
    (directRuntimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env
        (DirectSupported context) directLetAllocationCost Frame)
    (externalRuntimeRefines :
      ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env externals
        (ExternalSupported context) Frame)
    (callRuntimeRefines :
      ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env externals
        (ReuseCapacityDirectHereditaryCallSupported externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          directLetAllocationCost context)
        Frame)
    (lazyRuntimeRefines :
      ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels target.wasmModule hosts.env externals
        (LazySupported context) Frame)
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction labels
        target.wasmModule hosts.env (CaseSupported context))
    (effectRuntimeRefines :
      ∀ facts,
        EffectRuntimeRefines context sourceModule sourceFunction labels
          target.wasmModule hosts.env (EffectSupported context) (Frame facts)) :
    ∃ resultStore resultLocals resultWitness physical,
      CodeWP context sourceModule sourceFunction labels target.wasmModule
          hosts.env sourceRuntime sourceEnv code targetCode initial locals
          witness [] (ExactReturnControlPost resultStore physical) ∧
        Frame resultFacts slack resultRuntime resultEnv resultStore resultLocals
          resultWitness ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness expectedResult physical resultValue := by
  have shiftedInvariant :
      ReuseCapacityBudgetShiftedFrame Frame slack facts requiredBytes
        sourceRuntime sourceEnv initial locals witness := by
    simpa [ReuseCapacityBudgetShiftedFrame] using invariant
  have shiftedFrameRelated :
      ∀ {frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness},
        ReuseCapacityBudgetShiftedFrame Frame slack frameFacts frameBytes
            frameRuntime frameEnv frameStore frameLocals frameWitness →
          ReuseCapacityStateRelated frameFacts sourceFunction frameRuntime
            frameEnv frameStore frameLocals frameWitness := by
    intro frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
      frameWitness related
    exact frameRelated related
  obtain ⟨resultStore, resultLocals, resultWitness, physical, targetWP,
      resultInvariant, failureClear, valueRelated⟩ :=
    codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_exactResult evaluation
      adapted localsAligned shiftedInvariant shiftedFrameRelated
      (directRuntimeRefines.shiftBudget slack)
      (externalRuntimeRefines.shiftBudget slack)
      (callRuntimeRefines.shiftBudget slack)
      (lazyRuntimeRefines.shiftBudget slack) caseRuntimeRefines
      (fun facts =>
        EffectRuntimeRefines.shiftBudget (effectRuntimeRefines facts) slack)
  have resultFrame :
      Frame resultFacts slack resultRuntime resultEnv resultStore resultLocals
        resultWitness := by
    simpa [ReuseCapacityBudgetShiftedFrame] using resultInvariant
  exact ⟨resultStore, resultLocals, resultWitness, physical, targetWP,
    resultFrame, failureClear, valueRelated⟩

/-- The nested body determines the ordinary source call prefix. -/
theorem ReuseCapacityDirectHereditaryCallSupported.sourceStep
    {externals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {letCost : LCNF.LetDecl .impure → Nat}
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value} {stepCost : Nat}
    (supported :
      ReuseCapacityDirectHereditaryCallSupported externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost) :
    SourceCallLetResult context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue := by
  cases supported with
  | intro site row callee =>
      exact site.sourceCallLetResult (row.contextsCoherent rfl rfl)
        callee.sourceResult

/--
Source-facing family of saturated internal named calls.

Runtime endpoints and cost are indices because they are selected by the
actual source execution and hereditary declaration theorem, not stored as
proof artifacts in the call-site admission.
-/
inductive DirectInternalCallSupported (context : Fir.Wasm.Context) :
    RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
      RuntimeState → Value → Nat → Prop where
  | intro
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost : Nat}
      (site :
        DirectInternalCallSite context decl sourceEnv) :
      DirectInternalCallSupported context sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue stepCost

/--
Module-level hereditary theorem required by saturated internal named calls.

Production compilation supplies the numeric declaration index and the
physical arguments related to the admitted source arguments. Declaration
induction must return correctness for that exact function entry together with
the evolved whole-cache table. This is quantified over all executions and
compiler outputs; it is not a per-call target certificate.
-/
def DirectInternalCallDeclarationInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {callerFunction : Fir.Wasm.Function}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost remainingBytes : Nat}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {initialWitness : RefinementWitness}
      (site : DirectInternalCallSite context decl sourceEnv)
      {functionIndex : Nat}
      {physicalArgs : List Wasm.Value},
    SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue →
        stepCost ≤ remainingBytes →
          ConcreteReuseCapacityCacheFrame sourceModule callerFunction
            sourceExternals facts remainingBytes sourceRuntime sourceEnv
            initial locals initialWitness →
          callIndex? sourceModule (.declaration site.declaration) =
              some functionIndex →
            ConstructorArgumentsRelated initialWitness
                site.argumentKinds.toList physicalArgs
                site.semanticArgs.toList →
              ∃ calleeContext : Fir.Wasm.Context,
                ∃ calleeFunction targetFunction afterCall resultWitness
                    physical,
                  DeclarationContextsCoherent context calleeContext ∧
                    BudgetedCapacityPreservingSuccessfulDeclarationWithCache
                      calleeContext sourceModule calleeFunction
                      targetModule.wasmModule hosts.env sourceExternals
                      sourceRuntime nextRuntime site.calleeEnv site.calleeCode
                      targetFunction functionIndex initial afterCall
                      initialWitness resultWitness physicalArgs.reverse
                      site.resultKind sourceValue physical stepCost

/--
Production compiler construction of the cache-aware direct-call law.

Argument code, numeric declaration selection, physical operands, result-local
layout, and the checked destination write are all recovered from
`compileLetValue`, the Talos adapter, and the canonical caller frame. The only
recursive premise is the module-wide declaration induction above.
-/
theorem DirectDeclarationCallImplementationWithCache.ofInternalCompiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction targetModule hosts exportName)
    (declarations :
      DirectInternalCallDeclarationInduction context sourceModule targetModule
        hosts sourceExternals) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      callerFunction labels targetModule.wasmModule hosts.env sourceExternals
      (DirectInternalCallSupported context) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue initial locals resultIndex remainingBytes stepCost
    initialWitness supported stepFits sourceStep invariant valueCompiled
    valueAdapted resultFound
  cases supported with
  | intro site =>
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok (site.argumentCode ++
              [.call (.declaration site.declaration)]) := by
        simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind, site.valueEq,
          site.kindEq, site.argumentsCompiled, site.declarationFound,
          site.nonCached, Bind.bind, Except.bind, pure, Except.pure]
      have valueCodeEq :
          valueCode =
            site.argumentCode ++ [.call (.declaration site.declaration)] := by
        rw [expectedCompiled] at valueCompiled
        exact (Except.ok.inj valueCompiled).symm
      subst valueCode
      obtain ⟨targetArguments, functionIndex, argumentsAdapted, callFound,
          targetValueEq⟩ :=
        instructions_append_declaration_call_eq valueAdapted
      subst targetValue
      obtain ⟨physicalArgs, argumentsReady, _, argumentsRelated⟩ :=
        constructorArgsReady_of_compileArgs spec.localsAligned
          site.argumentsCompiled argumentsAdapted site.argumentsEvaluated
          invariant.1.1.1.1.stateRelated
      have assembled :
          ClosureArgumentAssembly targetModule.wasmModule hosts.env
            targetArguments physicalArgs initial locals :=
        ClosureArgumentAssembly.ofConstructorArgsReady argumentsReady
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned site.resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨calleeContext, calleeFunction, targetFunction, afterCall,
          resultWitness, physical, contexts, callee⟩ :=
        declarations site sourceStep stepFits invariant callFound
          argumentsRelated
      obtain ⟨updated, targetSet, _⟩ :=
        invariant.1.1.1.2.2.1.set?
          (nextRuntime := nextRuntime)
          (nextEnv := bind sourceEnv decl.fvarId sourceValue)
          (nextStore := afterCall)
          (nextWitness := resultWitness)
          (physical := physical) resultFound
      refine
        ⟨calleeContext, calleeFunction, site.calleeEnv, site.calleeCode,
          targetFunction, functionIndex, targetArguments, afterCall, updated,
          resultWitness, physicalArgs, site.resultKind, physical, contexts,
          rfl, resultKindAt, assembled, callee, targetSet, ?_⟩
      simp [Fir.Wasm.reuseCapacityLetFacts?, site.valueEq]

/--
A selected saturated closure candidate reconstructs the cache-augmented
canonical caller frame at the hereditary callee's exact endpoint.

The nonmatching dispatch prefix is read-only. This compatibility theorem also
assumes explicitly that the selected matcher has the unchanged-store case;
under that specialization the selected declaration contributes the same
witness, capacity, ordinaryness, immutable-table, and evolved-cache transports
as a direct named call. The general ownership-threaded selected call is a
separate composition boundary.
-/
theorem ConcreteReuseCapacityCacheFrame.ofSaturatedClosureDeclarationExact
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
    {resultIndex closureIndex remainingBytes stepCost : Nat}
    {closureId : FVarId} {address : Word32}
    {initialWitness resultWitness : RefinementWitness}
    {argumentTarget : Wasm.Program}
    {physicalArgs : List Wasm.Value}
    {resultKind : AbiKind} {physical : Wasm.Value}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (stepFits : stepCost ≤ remainingBytes)
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
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache calleeContext
        sourceModule calleeFunction module hostEnv sourceExternals
        sourceRuntime nextRuntime calleeEnv calleeCode targetFunction
        functionIndex initial afterCall initialWitness resultWitness
        physicalArgs.reverse resultKind sourceValue physical stepCost)
    (targetSet :
      locals.set? resultIndex physical = some updated)
    (transfer :
      reuseCapacityLetFacts? facts decl =
        some (eraseReuseCapacityFact facts decl.fvarId)) :
    CallLetStepSimulates context callerFunction module hostEnv sourceExternals
          decl continuation
          (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
            [.localGet resultIndex])
          sourceRuntime nextRuntime sourceEnv sourceValue initial afterCall
          locals updated resultIndex initialWitness resultWitness ∧
      afterCall.host.externals = initial.host.externals ∧
        afterCall.host.closureDescriptors =
            initial.host.closureDescriptors ∧
          resultWitness.closureDescriptors =
              initialWitness.closureDescriptors ∧
            reuseCapacityLetFacts? facts decl =
                some (eraseReuseCapacityFact facts decl.fvarId) ∧
              ConcreteReuseCapacityCacheFrame sourceModule callerFunction
                sourceExternals (eraseReuseCapacityFact facts decl.fvarId)
                (remainingBytes - stepCost) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) afterCall updated
                resultWitness := by
  have capacityStep :
      ReuseCapacityCallLetStepSimulates facts
        (eraseReuseCapacityFact facts decl.fvarId) context callerFunction module
        hostEnv sourceExternals decl continuation
        (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
          [.localGet resultIndex])
        sourceRuntime nextRuntime sourceEnv sourceValue initial afterCall locals
        updated resultIndex initialWitness resultWitness :=
    ReuseCapacityCallLetStepSimulates.ofSaturatedClosureDeclaration before
      selected suffix sourceStep invariant.1.1.1.1 resultFound resultKindAt
      hClosure hSat beforeNonmatching selectedMatches selectedStore assembled
      selectedBodyEq callee.declaration.capacityPreserving targetSet
  obtain ⟨step, externalsPreserved, hostDescriptorsPreserved,
      witnessDescriptorsPreserved, nextTransfer, nextBaseInvariant⟩ :=
    invariant.1.ofBudgetedCallStepExact stepFits capacityStep
      callee.declaration targetSet transfer
  have nextClosureTables :
      ClosureTablesAgree afterCall resultWitness :=
    callee.declaration.toClosureTablesTransport.agree invariant.2.2
  exact ⟨step, externalsPreserved, hostDescriptorsPreserved,
    witnessDescriptorsPreserved, nextTransfer,
    ⟨nextBaseInvariant, callee.cacheTable, nextClosureTables⟩⟩

/--
Uniform cache-aware implementation condition for saturated generated closure
dispatch.

The implementation must recover the exact compiler candidate list and first
matching candidate, prove the generated capture/argument assembly, and select
the hereditary declaration theorem for that candidate. Returning those facts
from a module-wide implementation keeps target selection out of the
source-facing call admission.
-/
def SaturatedClosureCallImplementationWithCache
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (spec : Wasm.HostSpec Host)
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
      {resultIndex remainingBytes stepCost : Nat}
      {initialWitness : RefinementWitness},
    CallSupported sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost →
      SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue →
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule callerFunction labels valueCode =
        .ok targetValue →
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex →
      ∃ (closureId : FVarId) (closureIndex : Nat) (address : Word32)
          (before : List
            (ClosureCandidateCase sourceModule callerFunction labels module
              spec initial closureId closureIndex address))
          (selected :
            ClosureCandidateCase sourceModule callerFunction labels module spec
              initial closureId closureIndex address)
          (suffix : List
            (ClosureCandidateCase sourceModule callerFunction labels module
              spec initial closureId closureIndex address))
          (calleeContext : Fir.Wasm.Context)
          (calleeFunction : Fir.Wasm.Function) (calleeEnv : Env)
          (calleeCode : LCNF.Code .impure)
          (targetFunction : Wasm.Function) (functionIndex : Nat)
          (argumentTarget : Wasm.Program) (afterCall : Wasm.Store Host)
          (updated : Wasm.Locals) (resultWitness : RefinementWitness)
          (physicalArgs : List Wasm.Value) (resultKind : AbiKind)
          (physical : Wasm.Value),
        DeclarationContextsCoherent context calleeContext ∧
          targetValue =
            resolvedClosureCandidateChain (before ++ selected :: suffix) ++
              [.localGet resultIndex] ∧
          (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
              some resultKind ∧
            locals.get closureIndex =
                some (.i32 (UInt32.ofNat address.value)) ∧
              hostEnv.Satisfies module spec ∧
                (∀ candidate, candidate ∈ before →
                  candidate.matched = (0 : UInt32)) ∧
                  (selected.matched != 0) = true ∧
                    selected.nextStore = initial ∧
                      ClosureArgumentAssembly module hostEnv argumentTarget
                          physicalArgs initial locals ∧
                      selected.targetBody =
                          argumentTarget ++
                            [.call functionIndex, .localSet resultIndex] ∧
                        BudgetedCapacityPreservingSuccessfulDeclarationWithCache
                            calleeContext sourceModule calleeFunction module
                            hostEnv sourceExternals sourceRuntime nextRuntime
                            calleeEnv calleeCode targetFunction functionIndex
                            initial afterCall initialWitness resultWitness
                            physicalArgs.reverse resultKind sourceValue
                            physical stepCost ∧
                          locals.set? resultIndex physical = some updated ∧
                            reuseCapacityLetFacts? facts decl =
                              some
                                (eraseReuseCapacityFact facts decl.fvarId)

/--
A uniform saturated-dispatch implementation supplies the same fixed-entry
call law as direct declaration calls.

The exact cache table returned by the selected hereditary callee becomes the
successor table. Matcher and capture-projection prefixes do not need an
unchanged-cache assumption.
-/
theorem
    SaturatedClosureCallImplementationWithCache.runtimeRefinesEntryRelative
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {sourceExternals : ExternalImpl}
    {CallSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    (implementation :
      SaturatedClosureCallImplementationWithCache context sourceModule
        callerFunction labels module hostEnv spec sourceExternals
        CallSupported)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
      callerFunction labels module hostEnv sourceExternals CallSupported
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule callerFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue initial locals resultIndex remainingBytes stepCost
    initialWitness supported stepFits invariant sourceStep valueCompiled
    valueAdapted resultFound
  rcases invariant with ⟨cacheInvariant, entryTransports⟩
  obtain ⟨closureId, closureIndex, address, before, selected, suffix,
      calleeContext, calleeFunction, calleeEnv, calleeCode, targetFunction,
      functionIndex, argumentTarget, afterCall, updated, resultWitness,
      physicalArgs, resultKind, physical, _contexts, targetEq, resultKindAt,
      hClosure, hSat,
      beforeNonmatching, selectedMatches, selectedStore, assembled,
      selectedBodyEq, callee, targetSet, transfer⟩ :=
    implementation supported sourceStep cacheInvariant valueCompiled
      valueAdapted resultFound
  subst targetValue
  obtain ⟨step, externalsPreserved, hostDescriptorsPreserved,
      witnessDescriptorsPreserved, nextTransfer, nextCacheInvariant⟩ :=
    cacheInvariant.ofSaturatedClosureDeclarationExact stepFits before selected
      suffix sourceStep resultFound resultKindAt hClosure hSat
      beforeNonmatching selectedMatches selectedStore assembled selectedBodyEq
      callee targetSet transfer
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        afterCall entryWitness resultWitness :=
    entryTransports.step
      callee.declaration.capacityPreserving.witnessTransport
      callee.declaration.capacityPreserving.capacityTransport
      callee.declaration.ordinaryTransport
      callee.declaration.externalsPreserved
      callee.declaration.toClosureTablesTransport
  exact ⟨afterCall, updated, resultWitness,
    eraseReuseCapacityFact facts decl.fvarId, step, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextTransfer,
    ⟨nextCacheInvariant, nextEntry⟩⟩

/--
Source/static admission for one nonempty closure application.

The site records the source closure lookup and the executable
compile/evaluation equations for the new arguments. It contains no candidate
list, numeric target index, concrete address, physical value, target body, or
target execution.
-/
structure SaturatedClosureCallSite
    (context : Fir.Wasm.Context)
    (decl : LCNF.LetDecl .impure)
    (sourceEnv : Env) where
  closureId : FVarId
  closureKind : AbiKind
  sourceClosure : Value
  args : Array (LCNF.Arg .impure)
  argumentCode : List Fir.Wasm.Instruction
  argumentKinds : Array AbiKind
  semanticArgs : Array Value
  resultKind : AbiKind
  valueEq : decl.value = .fvar closureId args
  kindEq : Fir.Wasm.checkedAbiKind decl.type = .ok resultKind
  closureCompiled :
    Fir.Wasm.getLocal context closureId =
      .ok (.localGet closureId, closureKind)
  argumentsCompiled :
    Fir.Wasm.compileArgs context args =
      .ok (argumentCode, argumentKinds)
  argumentsEvaluated :
    evalArgs sourceEnv args = .ok semanticArgs
  nonempty : args.isEmpty = false
  sourceLookup : lookup sourceEnv closureId = some sourceClosure
  resultCompiled :
    Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, resultKind)

/--
Source and static resolution of one *exactly saturated* internal closure
application.

The ordinary call site above records compiler/evaluator equations that are
independent of the current heap. This companion boundary identifies the live
semantic closure and the source declaration it resolves to, then states the
ABI equations that distinguish exact saturation from underapplication. It
contains no target module, numeric index, physical address, Wasm value, or
target execution.
-/
structure SaturatedClosureCallResolution
    (context : Fir.Wasm.Context)
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    (sourceRuntime : RuntimeState)
    (site : SaturatedClosureCallSite context decl sourceEnv) where
  location : Location
  cell : HeapCell
  function : Name
  arity : Nat
  captures : Array Value
  target : LCNF.Decl .impure
  parameterKinds : Array AbiKind
  targetResultKind : AbiKind
  calleeEnv : Env
  calleeCode : LCNF.Code .impure
  sourceClosureEq :
    site.sourceClosure = .object (.heap location)
  cellFound :
    findCell? sourceRuntime.heap location = some cell
  cellLive : cell.live = true
  cellObjectEq :
    cell.object = .closure function arity captures
  targetFound :
    context.program.findDecl? function = some target
  parametersKnown :
    Fir.Wasm.declarationParameterKinds? context.program target =
      some parameterKinds
  arityEq : arity = parameterKinds.size
  saturated :
    captures.size + site.argumentKinds.size = parameterKinds.size
  argumentsRefine :
    Fir.Wasm.kindsRefine site.argumentKinds
      (parameterKinds.extract captures.size parameterKinds.size) = true
  targetResult :
    Fir.Wasm.directAbiKind? target.type = some targetResultKind
  targetResultRefines :
    targetResultKind.refines site.resultKind = true
  bodyEq : target.value = .code calleeCode
  parametersBound :
    bindParams target.params (captures ++ site.semanticArgs) = .ok calleeEnv

/-- `compileArgs` emits exactly one ABI kind for every source argument. -/
theorem SaturatedClosureCallSite.argumentKinds_size
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    (site : SaturatedClosureCallSite context decl sourceEnv) :
    site.argumentKinds.size = site.args.size := by
  have characterized :=
    ConstructorArgsCompiled.ofCompileArgs site.argumentsCompiled
  have lengthEq :
      site.argumentKinds.toList.length = site.args.toList.length := by
    have go :
        ∀ {args : List (LCNF.Arg .impure)}
            {code : List Fir.Wasm.Instruction}
            {kinds : List AbiKind},
          ConstructorArgsCompiled context args code kinds →
            kinds.length = args.length := by
      intro args code kinds compiled
      induction compiled with
      | nil => rfl
      | erased _ ih => simp [ih]
      | fvar _ _ ih => simp [ih]
    exact go characterized
  simpa using lengthEq

/-- A nonempty source application has a nonempty compiler ABI argument row. -/
theorem SaturatedClosureCallSite.argumentKinds_nonempty
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    (site : SaturatedClosureCallSite context decl sourceEnv) :
    site.argumentKinds.isEmpty = false := by
  simpa [Array.isEmpty, site.argumentKinds_size] using site.nonempty

/-- Successful source declaration lookup fixes the resolved declaration name. -/
theorem SaturatedClosureCallResolution.targetName
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    {sourceRuntime : RuntimeState}
    {site : SaturatedClosureCallSite context decl sourceEnv}
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site) :
    resolution.target.name = resolution.function := by
  have selected :=
    (Array.find?_eq_some_iff_getElem.mp resolution.targetFound).1
  simpa [Fir.LeanIR.Program.findDecl?] using selected

/-- Successful `Option` traversal preserves list length. Kept near closure
resolution because both source-entry reconstruction and generated parameter
rows consume the same executable classifier fact. -/
private theorem optionListMapM_length
    {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (mapped : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      have ysEq : ys = [] := by simpa using mapped.symm
      subst ys
      rfl
  | cons head tail ih =>
      cases headResult : f head with
      | none => simp [List.mapM_cons, headResult] at mapped
      | some value =>
          cases tailResult : tail.mapM f with
          | none => simp [List.mapM_cons, headResult, tailResult] at mapped
          | some values =>
              have ysEq : ys = value :: values := by
                simpa [List.mapM_cons, headResult, tailResult] using mapped.symm
              subst ys
              simp [ih tailResult]

/-- Successful closure-target parameter classification preserves source
declaration arity. -/
theorem SaturatedClosureCallResolution.parameterKinds_size
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    {sourceRuntime : RuntimeState}
    {site : SaturatedClosureCallSite context decl sourceEnv}
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site) :
    resolution.parameterKinds.size = resolution.target.params.size := by
  have known := resolution.parametersKnown
  unfold Fir.Wasm.declarationParameterKinds? at known
  rw [Array.mapM_eq_mapM_toList] at known
  cases listKnown :
      resolution.target.params.toList.mapM
        (Fir.Wasm.declarationParamKind? context.program resolution.target) with
  | none => simp [listKnown] at known
  | some listKinds =>
      have parameterKindsEq :
          resolution.parameterKinds = listKinds.toArray := by
        simpa [listKnown] using known.symm
      rw [parameterKindsEq]
      simpa using optionListMapM_length listKnown

/-- Source-only hereditary admission for one exactly saturated closure call.

The successful semantic application equation exposes the runtime *after*
closure ownership has been consumed. The nested finite callee derivation
starts from that runtime in the exact declaration-local lowering context.
There is no target candidate, address, matcher execution, or Wasm theorem in
this boundary. -/
inductive SaturatedClosureHereditaryCallSupported
    (externals : ExternalImpl)
    (DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop)
    (LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop)
    (CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop)
    (EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate)
    (letCost : LCNF.LetDecl .impure → Nat)
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (decl : LCNF.LetDecl .impure) (_continuation : LCNF.Code .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) (stepCost : Nat) : Prop where
  | intro
      (callRuntime : RuntimeState)
      (calleeFunction : Fir.Wasm.Function)
      (calleeResultFacts : ReuseCapacityFacts)
      (calleeResultEnv : Env)
      (site : SaturatedClosureCallSite context decl sourceEnv)
      (resolution :
        SaturatedClosureCallResolution context sourceRuntime site)
      (row :
        LoweredInternalDeclaration context.program context.cachedDeclarations
          resolution.target resolution.calleeCode calleeFunction)
      (sharedCapacity : ∀ parentRuntime,
        setCell sourceRuntime resolution.location
            { resolution.cell with rc := resolution.cell.rc - 1 } =
              .ok parentRuntime →
          ClosureRetainCapacity parentRuntime resolution.captures.toList)
      (application :
        Fir.LeanIR.Impure.takeClosureApplication sourceRuntime
            resolution.location =
          .ok (callRuntime, resolution.function, resolution.arity,
            resolution.captures))
      (callee :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported LazySupported CaseSupported EffectSupported
          letCost row.context resolution.targetResultKind [] callRuntime
          resolution.calleeEnv resolution.calleeCode calleeResultFacts
          nextRuntime calleeResultEnv sourceValue stepCost) :
      SaturatedClosureHereditaryCallSupported externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context sourceRuntime sourceEnv decl _continuation nextRuntime
        sourceValue stepCost

/-- The hereditary closure payload reconstructs the exact ordinary source
call step, including the ownership-changing application prefix. -/
theorem SaturatedClosureHereditaryCallSupported.sourceStep
    {externals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {letCost : LCNF.LetDecl .impure → Nat}
    {context : Fir.Wasm.Context}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {sourceValue : Value}
    {stepCost : Nat}
    (supported :
      SaturatedClosureHereditaryCallSupported externals DirectSupported
        ExternalSupported LazySupported CaseSupported EffectSupported letCost
        context sourceRuntime sourceEnv decl continuation nextRuntime
        sourceValue stepCost) :
    SourceCallLetResult context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue := by
  rcases supported with
    ⟨callRuntime, calleeFunction, calleeResultFacts, calleeResultEnv, site,
      resolution, row, _sharedCapacity, application, callee⟩
  have semanticArgumentSize :
      site.semanticArgs.size = site.args.size := by
    have evaluated := site.argumentsEvaluated
    unfold evalArgs at evaluated
    rw [Array.mapM_eq_mapM_toList] at evaluated
    cases listResult :
        site.args.toList.mapM (evalArg sourceEnv) with
    | error fault =>
        rw [listResult] at evaluated
        contradiction
    | ok results =>
        rw [listResult] at evaluated
        have valuesEq : results.toArray = site.semanticArgs :=
          Except.ok.inj evaluated
        rw [← valuesEq]
        simpa using
          listMapM_length_of_ok_for_directCall site.args.toList
            (evalArg sourceEnv) results listResult
  have applicationArgumentSize :
      (resolution.captures ++ site.semanticArgs).size =
        resolution.target.params.size := by
    rw [Array.size_append, semanticArgumentSize,
      ← site.argumentKinds_size, ← resolution.parameterKinds_size]
    exact resolution.saturated
  have callArgs :
      (resolution.captures ++ site.semanticArgs).extract 0
          resolution.target.params.size =
        resolution.captures ++ site.semanticArgs := by
    rw [← applicationArgumentSize]
    exact Array.extract_size
  have extraArgs :
      (resolution.captures ++ site.semanticArgs).extract
          resolution.target.params.size
          (resolution.captures ++ site.semanticArgs).size =
        #[] := by
    simp [← applicationArgumentSize]
  have semanticArgumentsPositive : 0 < site.semanticArgs.size := by
    rw [semanticArgumentSize]
    exact Array.size_pos_iff.mpr
      (Array.isEmpty_eq_false_iff.mp site.nonempty)
  have semanticArgumentsNonempty : site.semanticArgs.isEmpty = false :=
    Array.isEmpty_eq_false_iff.mpr
      (Array.size_pos_iff.mp semanticArgumentsPositive)
  have applicationArgumentsPositive :
      0 < (resolution.captures ++ site.semanticArgs).size := by
    simp only [Array.size_append]
    omega
  have applicationArgumentsNonempty :
      (resolution.captures ++ site.semanticArgs).isEmpty = false := by
    exact Array.isEmpty_eq_false_iff.mpr
      (Array.size_pos_iff.mp applicationArgumentsPositive)
  have staged :
      executeStep externals {
          program := context.program
          control := .code (.let decl continuation)
          env := sourceEnv
          runtime := sourceRuntime } =
        .next {
          program := context.program
          control := .invokeValue site.sourceClosure site.semanticArgs
          env := sourceEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } := by
    simp [executeStep, coreStep, evalLetValue, lookupValue, site.valueEq,
      site.sourceLookup, site.argumentsEvaluated, semanticArgumentsNonempty,
      pushBindFrame, Bind.bind, Except.bind, pure, Except.pure]
  have entered :
      executeStep externals {
          program := context.program
          control := .invokeValue site.sourceClosure site.semanticArgs
          env := sourceEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := sourceRuntime } =
        .next {
          program := context.program
          control := .code resolution.calleeCode
          env := resolution.calleeEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := callRuntime } := by
    simp [executeStep, coreStep, invokeClosure,
      resolution.sourceClosureEq, application, invokeDecl,
      resolution.targetFound, applicationArgumentSize, callArgs, extraArgs,
      applicationArgumentsNonempty, resolution.parametersBound,
      resolution.bodyEq]
  have callerResult :=
    (row.contextsCoherent rfl rfl).sourceCodeResult callee.sourceResult
  rcases callerResult with ⟨calleeCount, resultEnv, calleeSteps⟩
  have protectedSteps :
      ExecSteps externals calleeCount {
          program := context.program
          control := .code resolution.calleeCode
          env := resolution.calleeEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := callRuntime } {
          program := context.program
          control := .yielded sourceValue
          env := resultEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := nextRuntime } := by
    simpa [sourceCodeState, sourceYieldState, withFrameSuffix] using
      (FirTalos.Correctness.ExecSteps.withFrameSuffix calleeSteps
        (suffix := [.bind decl.fvarId continuation sourceEnv []]))
  have resumed :
      executeStep externals {
          program := context.program
          control := .yielded sourceValue
          env := resultEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := nextRuntime } =
        .next {
          program := context.program
          control := .code continuation
          env := bind sourceEnv decl.fvarId sourceValue
          runtime := nextRuntime } := by
    simp [executeStep, coreStep]
  have callPrefix :
      ExecSteps externals 2 {
          program := context.program
          control := .code (.let decl continuation)
          env := sourceEnv
          runtime := sourceRuntime } {
          program := context.program
          control := .code resolution.calleeCode
          env := resolution.calleeEnv
          frames := [.bind decl.fvarId continuation sourceEnv []]
          runtime := callRuntime } :=
    .step staged (.step entered (.refl _))
  obtain ⟨withCalleeCount, withCallee⟩ :=
    FirTalos.Correctness.ExecSteps.trans callPrefix protectedSteps
  obtain ⟨count, steps⟩ :=
    FirTalos.Correctness.ExecSteps.trans withCallee
      (.step resumed (.refl _))
  exact ⟨count, steps⟩

/--
Exact source resolution constructively supplies a compiler-emitted saturated
candidate with the semantic function/arity/fixed matcher identity.

This is the static half of closure dispatch selection. It opens the real
`compileClosureCandidatesForTarget` definition and proves membership in its
range/filter-map; it does not accept a candidate list or matcher outcome.
-/
theorem SaturatedClosureCallResolution.candidateSource_exists
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    {sourceRuntime : RuntimeState}
    (site : SaturatedClosureCallSite context decl sourceEnv)
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site) :
    ∃ candidate ∈
        Fir.Wasm.compileClosureCandidatesForTarget context.program decl.fvarId
          site.closureId
          site.resultKind site.argumentCode site.argumentKinds
          resolution.target,
      candidate.1 = [
        .localGet site.closureId,
        .call (.runtime (.closureMatches resolution.function resolution.arity
          resolution.captures.size))] := by
  have argumentPositive : 0 < site.argumentKinds.size := by
    exact Array.size_pos_iff.mpr
      (Array.isEmpty_eq_false_iff.mp site.argumentKinds_nonempty)
  have saturated := resolution.saturated
  have argumentLe :
      site.argumentKinds.size ≤ resolution.parameterKinds.size := by
    omega
  have fixedLt :
      resolution.captures.size < resolution.parameterKinds.size := by
    omega
  have fixedInRange :
      resolution.captures.size <
        resolution.parameterKinds.size - site.argumentKinds.size + 1 := by
    omega
  let candidate : List Fir.Wasm.Instruction × List Fir.Wasm.Instruction :=
    ([.localGet site.closureId,
      .call (.runtime (.closureMatches resolution.function resolution.arity
        resolution.captures.size))],
     Fir.Wasm.compileFixedClosureFields site.closureId resolution.target
        resolution.arity resolution.captures.size resolution.parameterKinds ++
       site.argumentCode ++
       [.call (.declaration resolution.function), .localSet decl.fvarId])
  have compiled :
      Fir.Wasm.compileClosureCandidateAt decl.fvarId site.closureId
          site.resultKind site.argumentCode site.argumentKinds
          resolution.target resolution.parameterKinds
          resolution.captures.size =
        some candidate := by
    simp [Fir.Wasm.compileClosureCandidateAt, candidate, fixedLt,
      resolution.saturated, resolution.argumentsRefine,
      resolution.targetResult, resolution.targetResultRefines,
      resolution.targetName, resolution.arityEq]
  refine ⟨candidate, ?_, rfl⟩
  unfold Fir.Wasm.compileClosureCandidatesForTarget
  simp only [resolution.parametersKnown]
  simp only [site.argumentKinds_nonempty, Bool.false_or,
    Nat.not_lt.mpr argumentLe]
  apply List.mem_filterMap.mpr
  exact
    ⟨resolution.captures.size, List.mem_range.mpr fixedInRange, compiled⟩

/--
An exact compiler-candidate enumeration contains the semantic matcher
identity selected by the resolved saturated source closure.

The theorem first proves membership in the raw source compiler enumeration,
then transports it across the adapter-facing `ClosureCandidateCase.source`
map. Candidate metadata are recovered by injectivity of the emitted matcher
instruction; they are not additional premises.
-/
theorem SaturatedClosureCallResolution.containsCandidateIdentity
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceEnv : Env}
    {sourceRuntime : RuntimeState}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {closureIndex : Nat}
    {address : Word32}
    (site : SaturatedClosureCallSite context decl sourceEnv)
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site)
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial site.closureId closureIndex address))
    (candidatesEq :
      context.program.decls.toList.flatMap (fun target =>
        Fir.Wasm.compileClosureCandidatesForTarget context.program decl.fvarId
          site.closureId
          site.resultKind site.argumentCode site.argumentKinds target) =
        candidates.map (·.source)) :
    ∃ candidate ∈ candidates,
      (resolution.function == candidate.function &&
        resolution.arity == candidate.arity &&
        resolution.captures.size == candidate.fixed) = true := by
  obtain ⟨source, sourceMem, matcherEq⟩ :=
    resolution.candidateSource_exists site
  have targetMem : resolution.target ∈ context.program.decls.toList := by
    obtain ⟨index, indexLt, targetAt, _⟩ :=
      (Array.find?_eq_some_iff_getElem.mp resolution.targetFound).2
    have found : context.program.decls[index] ∈ context.program.decls :=
      Array.getElem_mem indexLt
    simpa [targetAt] using found
  have generatedMem :
      source ∈ context.program.decls.toList.flatMap (fun target =>
        Fir.Wasm.compileClosureCandidatesForTarget context.program decl.fvarId
          site.closureId
          site.resultKind site.argumentCode site.argumentKinds target) :=
    List.mem_flatMap.mpr ⟨resolution.target, targetMem, sourceMem⟩
  rw [candidatesEq] at generatedMem
  obtain ⟨candidate, candidateMem, candidateSourceEq⟩ :=
    List.mem_map.mp generatedMem
  refine ⟨candidate, candidateMem, ?_⟩
  have matcherLists :
      ([Fir.Wasm.Instruction.localGet site.closureId,
        .call (.runtime (.closureMatches candidate.function candidate.arity
          candidate.fixed))] : List Fir.Wasm.Instruction) =
      [Fir.Wasm.Instruction.localGet site.closureId,
        .call (.runtime (.closureMatches resolution.function resolution.arity
          resolution.captures.size))] :=
    candidate.sourceMatcher.symm.trans
      ((congrArg Prod.fst candidateSourceEq).trans matcherEq)
  have operationEq :
      Fir.Wasm.RuntimeOp.closureMatches candidate.function candidate.arity
          candidate.fixed =
        .closureMatches resolution.function resolution.arity
          resolution.captures.size := by
    have callsEq :=
      congrArg (fun xs : List Fir.Wasm.Instruction => xs[1]?) matcherLists
    simpa using callsEq
  obtain ⟨functionEq, arityEq, fixedEq⟩ :=
    Fir.Wasm.RuntimeOp.closureMatches.inj operationEq
  simp [functionEq, arityEq, fixedEq]

/--
The canonical cache frame resolves the one concrete address represented by an
exact source closure site.

This theorem deliberately precedes executable candidate construction:
`closureMatches` can run successfully at the mapped live closure address, not
at an arbitrary wasm32 word.
-/
theorem ConcreteReuseCapacityCacheFrame.resolveClosureAddress
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureIndex : Nat}
    {closureKind : AbiKind}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (site : SaturatedClosureCallSite context decl sourceEnv)
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site)
    (closureFound :
      findFVar? (functionBindings sourceFunction) site.closureId =
        some closureIndex)
    (closureKindAt :
      (functionBindings sourceFunction)[closureIndex]?.map Prod.snd =
        some closureKind) :
    ∃ address : Word32,
      locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        witness.locations.lookup? resolution.location = some address := by
  have sourceLookup :
      lookup sourceEnv site.closureId =
        some (.object (.heap resolution.location)) := by
    rw [← resolution.sourceClosureEq]
    exact site.sourceLookup
  obtain ⟨physical, localFound, physicalRelated⟩ :=
    invariant.1.1.1.1.stateRelated.resolve sourceLookup closureFound
      closureKindAt
  obtain ⟨address, physicalEq, mapped⟩ := physicalRelated.heapAddress
  subst physical
  exact ⟨address, localFound, mapped⟩

/--
At the mapped closure address, exact source resolution and compiler
enumeration determine the first executable matching candidate.

The physical address and local equation are inputs derived by
`resolveClosureAddress`; executable candidate cases are never quantified over
unmapped words.
-/
theorem
    ConcreteReuseCapacityCacheFrame.closureCandidates_exists_first_match_of_resolution
    {context : Fir.Wasm.Context}
    {decl : LCNF.LetDecl .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureIndex : Nat}
    {address : Word32}
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv initial locals witness)
    (site : SaturatedClosureCallSite context decl sourceEnv)
    (resolution :
      SaturatedClosureCallResolution context sourceRuntime site)
    (closureLocal :
      locals.get closureIndex =
        some (.i32 (UInt32.ofNat address.value)))
    (mapped :
      witness.locations.lookup? resolution.location = some address)
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial site.closureId closureIndex address))
    (candidatesEq :
      context.program.decls.toList.flatMap (fun target =>
        Fir.Wasm.compileClosureCandidatesForTarget context.program decl.fvarId
          site.closureId
          site.resultKind site.argumentCode site.argumentKinds target) =
        candidates.map (·.source)) :
    ∃ (before : List
          (ClosureCandidateCase sourceModule sourceFunction labels module spec
            initial site.closureId closureIndex address))
        (selected :
          ClosureCandidateCase sourceModule sourceFunction labels module spec
            initial site.closureId closureIndex address)
        (suffix : List
          (ClosureCandidateCase sourceModule sourceFunction labels module spec
            initial site.closureId closureIndex address)),
      candidates = before ++ selected :: suffix ∧
        locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        (∀ candidate, candidate ∈ before →
          candidate.matched = (0 : UInt32)) ∧
        (selected.matched != 0) = true ∧
        (resolution.function == selected.function &&
          resolution.arity == selected.arity &&
          resolution.captures.size == selected.fixed) = true := by
  have containsMatch :=
    resolution.containsCandidateIdentity site candidates candidatesEq
  obtain ⟨before, selected, suffix, candidatesSplit, beforeNonmatching,
      selectedMatches⟩ :=
    invariant.closureCandidates_exists_first_match candidates mapped
      resolution.cellFound resolution.cellLive resolution.cellObjectEq
      containsMatch
  have selectedIdentity :
      (resolution.function == selected.function &&
        resolution.arity == selected.arity &&
        resolution.captures.size == selected.fixed) = true := by
    have classified :=
      selected.matched_eq_of_refines invariant.1.1.1.1.stateRelated.1
        invariant.2.2.dispatch invariant.2.2.descriptors.symm mapped
        resolution.cellFound resolution.cellLive resolution.cellObjectEq
    rw [classified] at selectedMatches
    simpa [and_assoc] using selectedMatches
  exact ⟨before, selected, suffix, candidatesSplit, closureLocal,
    beforeNonmatching, selectedMatches, selectedIdentity⟩

/-- Source-facing family of admitted saturated closure applications. -/
inductive SaturatedClosureCallSupported (context : Fir.Wasm.Context) :
    RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
      RuntimeState → Value → Nat → Prop where
  | intro
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost : Nat}
      (site : SaturatedClosureCallSite context decl sourceEnv)
      (resolution :
        SaturatedClosureCallResolution context sourceRuntime site) :
      SaturatedClosureCallSupported context sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue stepCost

/--
Module-level first-match and hereditary-declaration induction for generated
closure dispatch.

The conclusion must enumerate exactly the candidates produced by
`compileClosureDispatch`; the adapter equation is derived later from that
equality. Dynamic representation reasoning supplies the concrete closure
address and first matching candidate, while recursive declaration induction
supplies that candidate's cache-aware callee theorem. Thus neither the source
admission nor the compiler constructor accepts a target execution certificate.
-/
def SaturatedClosureDispatchSelectionInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost remainingBytes : Nat}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {initialWitness : RefinementWitness}
      (site : SaturatedClosureCallSite context decl sourceEnv)
      (_resolution :
        SaturatedClosureCallResolution context sourceRuntime site)
      {closureIndex resultIndex : Nat},
    SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue →
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
          sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
          locals initialWitness →
        findFVar? (functionBindings callerFunction) site.closureId =
            some closureIndex →
          findFVar? (functionBindings callerFunction) decl.fvarId =
              some resultIndex →
            ∃ (address : Word32)
                (before : List
                  (ClosureCandidateCase sourceModule callerFunction labels
                    targetModule.wasmModule hosts.spec initial site.closureId
                    closureIndex address))
                (selected :
                  ClosureCandidateCase sourceModule callerFunction labels
                    targetModule.wasmModule hosts.spec initial site.closureId
                    closureIndex address)
                (suffix : List
                  (ClosureCandidateCase sourceModule callerFunction labels
                    targetModule.wasmModule hosts.spec initial site.closureId
                    closureIndex address))
                (calleeContext : Fir.Wasm.Context)
                (calleeFunction : Fir.Wasm.Function) (calleeEnv : Env)
                (calleeCode : LCNF.Code .impure)
                (targetFunction : Wasm.Function) (functionIndex : Nat)
                (argumentTarget : Wasm.Program)
                (afterCall : Wasm.Store Host) (updated : Wasm.Locals)
                (resultWitness : RefinementWitness)
                (physicalArgs : List Wasm.Value) (physical : Wasm.Value),
              DeclarationContextsCoherent context calleeContext ∧
                context.program.decls.toList.flatMap (fun target =>
                  compileClosureCandidatesForTarget context.program decl.fvarId
                    site.closureId
                    site.resultKind site.argumentCode site.argumentKinds
                    target) =
                  (before ++ selected :: suffix).map (·.source) ∧
                locals.get closureIndex =
                    some (.i32 (UInt32.ofNat address.value)) ∧
                  (∀ candidate, candidate ∈ before →
                    candidate.matched = (0 : UInt32)) ∧
                    (selected.matched != 0) = true ∧
                      selected.nextStore = initial ∧
                        ClosureArgumentAssembly targetModule.wasmModule hosts.env
                            argumentTarget physicalArgs initial locals ∧
                        selected.targetBody =
                            argumentTarget ++
                              [.call functionIndex, .localSet resultIndex] ∧
                          BudgetedCapacityPreservingSuccessfulDeclarationWithCache
                              calleeContext sourceModule calleeFunction
                              targetModule.wasmModule hosts.env sourceExternals
                              sourceRuntime nextRuntime calleeEnv calleeCode
                              targetFunction functionIndex initial afterCall
                              initialWitness resultWitness physicalArgs.reverse
                              site.resultKind sourceValue physical stepCost ∧
                            locals.set? resultIndex physical = some updated

/--
Static resolver and hereditary-body induction for saturated closure dispatch,
with dynamic first-match selection factored out.

The canonical cache frame first derives the actual mapped closure address.
At that address the induction constructs the exact adapter/resolver candidate
list. For the candidate whose metadata matches the resolved source closure it
supplies argument assembly and the hereditary declaration theorem. First-match
selection remains a theorem derived from the executable list; it is not a
premise supplied by the caller.
-/
def SaturatedClosureCandidateResolutionInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost remainingBytes : Nat}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {initialWitness : RefinementWitness}
      (site : SaturatedClosureCallSite context decl sourceEnv)
      (resolution :
        SaturatedClosureCallResolution context sourceRuntime site)
      {closureIndex resultIndex : Nat}
      {address : Word32},
    SourceCallLetResult context sourceExternals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue →
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
          sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
          locals initialWitness →
        findFVar? (functionBindings callerFunction) site.closureId =
            some closureIndex →
          findFVar? (functionBindings callerFunction) decl.fvarId =
              some resultIndex →
            locals.get closureIndex =
                some (.i32 (UInt32.ofNat address.value)) →
              initialWitness.locations.lookup? resolution.location =
                  some address →
                ∃ candidates : List
                (ClosureCandidateCase sourceModule callerFunction labels
                  targetModule.wasmModule hosts.spec initial site.closureId
                  closureIndex address),
                  context.program.decls.toList.flatMap (fun target =>
                      compileClosureCandidatesForTarget context.program decl.fvarId
                        site.closureId site.resultKind site.argumentCode
                        site.argumentKinds target) =
                    candidates.map (·.source) ∧
                ∀ (candidate :
                    ClosureCandidateCase sourceModule callerFunction labels
                      targetModule.wasmModule hosts.spec initial site.closureId
                      closureIndex address),
                candidate ∈ candidates →
                  (resolution.function == candidate.function &&
                    resolution.arity == candidate.arity &&
                    resolution.captures.size == candidate.fixed) = true →
                    ∃ (calleeContext : Fir.Wasm.Context)
                        (calleeFunction : Fir.Wasm.Function)
                        (targetFunction : Wasm.Function) (functionIndex : Nat)
                        (argumentTarget : Wasm.Program)
                        (afterCall : Wasm.Store Host) (updated : Wasm.Locals)
                        (resultWitness : RefinementWitness)
                        (physicalArgs : List Wasm.Value)
                        (physical : Wasm.Value),
                      DeclarationContextsCoherent context calleeContext ∧
                        candidate.nextStore = initial ∧
                          ClosureArgumentAssembly targetModule.wasmModule hosts.env
                            argumentTarget physicalArgs initial locals ∧
                        candidate.targetBody =
                            argumentTarget ++
                              [.call functionIndex, .localSet resultIndex] ∧
                          BudgetedCapacityPreservingSuccessfulDeclarationWithCache
                              calleeContext sourceModule calleeFunction
                              targetModule.wasmModule hosts.env sourceExternals
                              sourceRuntime nextRuntime resolution.calleeEnv
                              resolution.calleeCode targetFunction
                              functionIndex initial afterCall initialWitness
                              resultWitness physicalArgs.reverse
                              site.resultKind sourceValue physical stepCost ∧
                            locals.set? resultIndex physical = some updated

/--
The factored candidate-resolution induction supplies the historical selection
boundary as a theorem.

Local layout alignment recovers the closure ABI row. The cache frame then
derives the actual address, semantic candidate coverage, and first executable
match. The induction is consulted only for the selected semantic identity.
-/
theorem SaturatedClosureCandidateResolutionInduction.toSelection
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (localsAligned : LocalLayoutAligned context callerFunction)
    (induction :
      SaturatedClosureCandidateResolutionInduction context sourceModule
        callerFunction labels targetModule hosts sourceExternals) :
    SaturatedClosureDispatchSelectionInduction context sourceModule
      callerFunction labels targetModule hosts sourceExternals := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    stepCost remainingBytes initial locals initialWitness site resolution
    closureIndex resultIndex sourceStep invariant closureFound resultFound
  obtain ⟨alignedClosureIndex, alignedClosureFound, closureKindAt⟩ :=
    localsAligned site.closureCompiled
  rw [closureFound] at alignedClosureFound
  injection alignedClosureFound with closureIndexEq
  subst alignedClosureIndex
  obtain ⟨address, hClosure, mapped⟩ :=
    invariant.resolveClosureAddress site resolution closureFound closureKindAt
  obtain ⟨candidates, candidatesEq, selectedImplementation⟩ :=
    induction site resolution sourceStep invariant closureFound resultFound
      hClosure mapped
  obtain ⟨before, selected, suffix, candidatesSplit, _,
      beforeNonmatching, selectedMatches, selectedIdentity⟩ :=
    invariant.closureCandidates_exists_first_match_of_resolution site
      resolution hClosure mapped candidates candidatesEq
  have selectedMem : selected ∈ candidates := by
    rw [candidatesSplit]
    simp
  obtain ⟨calleeContext, calleeFunction, targetFunction, functionIndex,
      argumentTarget, afterCall, updated, resultWitness, physicalArgs,
      physical, contexts, selectedStore, assembled, selectedBodyEq, callee,
      targetSet⟩ :=
    selectedImplementation selected selectedMem selectedIdentity
  have generatedEq := candidatesEq
  rw [candidatesSplit] at generatedEq
  exact
    ⟨address, before, selected, suffix, calleeContext, calleeFunction,
      resolution.calleeEnv, resolution.calleeCode, targetFunction,
      functionIndex, argumentTarget, afterCall, updated, resultWitness,
      physicalArgs, physical, contexts, generatedEq, hClosure,
      beforeNonmatching, selectedMatches, selectedStore, assembled,
      selectedBodyEq, callee, targetSet⟩

/--
Production compiler construction of the saturated closure-dispatch call law.

The source site fixes the real nonempty `compileClosureDispatch` expression.
The module induction returns an exact compiler candidate enumeration; the
existing adapter theorem then determines `targetValue` rather than accepting
it from the induction. Local indices come from the generated local layout and
the selected callee returns the evolved cache table.
-/
theorem SaturatedClosureCallImplementationWithCache.ofInternalCompiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction targetModule hosts exportName)
    (selection :
      SaturatedClosureDispatchSelectionInduction context sourceModule
        callerFunction labels targetModule hosts sourceExternals) :
    SaturatedClosureCallImplementationWithCache context sourceModule
      callerFunction labels targetModule.wasmModule hosts.env hosts.spec
      sourceExternals (SaturatedClosureCallSupported context) := by
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue initial locals resultIndex remainingBytes stepCost
    initialWitness supported sourceStep invariant valueCompiled valueAdapted
    resultFound
  cases supported with
  | intro site resolution =>
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok (compileClosureDispatch context decl.fvarId site.closureId
              site.resultKind site.argumentCode site.argumentKinds) := by
        simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind, site.valueEq,
          site.kindEq, site.closureCompiled, site.argumentsCompiled,
          site.nonempty, Bind.bind, Except.bind, pure, Except.pure]
      have valueCodeEq :
          valueCode =
            compileClosureDispatch context decl.fvarId site.closureId
              site.resultKind site.argumentCode site.argumentKinds := by
        rw [expectedCompiled] at valueCompiled
        exact (Except.ok.inj valueCompiled).symm
      subst valueCode
      obtain ⟨closureIndex, closureFound, _⟩ :=
        spec.localsAligned site.closureCompiled
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        spec.localsAligned site.resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      obtain ⟨address, before, selected, suffix, calleeContext, calleeFunction,
          calleeEnv, calleeCode, targetFunction, functionIndex, argumentTarget,
          afterCall, updated, resultWitness, physicalArgs, physical, contexts,
          candidatesEq, hClosure, beforeNonmatching, selectedMatches,
          selectedStore, assembled, selectedBodyEq, callee, targetSet⟩ :=
        selection site resolution sourceStep invariant closureFound resultFound
      have dispatchAdapted :
          instructions sourceModule callerFunction labels
              (compileClosureDispatch context decl.fvarId site.closureId
                site.resultKind site.argumentCode site.argumentKinds) =
            .ok
              (resolvedClosureCandidateChain
                  (before ++ selected :: suffix) ++
                [.localGet resultIndex]) :=
        instructions_compileClosureDispatch (before ++ selected :: suffix)
          candidatesEq closureFound resultFound
      have targetEq :
          targetValue =
            resolvedClosureCandidateChain (before ++ selected :: suffix) ++
              [.localGet resultIndex] := by
        rw [dispatchAdapted] at valueAdapted
        exact (Except.ok.inj valueAdapted).symm
      refine
        ⟨site.closureId, closureIndex, address, before, selected, suffix,
          calleeContext, calleeFunction, calleeEnv, calleeCode, targetFunction,
          functionIndex, argumentTarget, afterCall, updated, resultWitness,
          physicalArgs, site.resultKind, physical, contexts, targetEq,
          resultKindAt, hClosure, spec.hostsSatisfy, beforeNonmatching,
          selectedMatches, selectedStore, assembled, selectedBodyEq, callee,
          targetSet, ?_⟩
      simp [Fir.Wasm.reuseCapacityLetFacts?, site.valueEq]

/--
Preferred production construction of saturated closure dispatch.

The induction supplies only implementations for compiler candidates with the
resolved source identity. Candidate enumeration, the concrete closure address,
and executable first-match selection are discharged by the static resolution
and canonical cache frame before the historical compiler construction is
applied.
-/
theorem SaturatedClosureCallImplementationWithCache.ofInternalCompilerResolved
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedExport program context callerCode sourceModule
        callerFunction targetModule hosts exportName)
    (induction :
      SaturatedClosureCandidateResolutionInduction context sourceModule
        callerFunction labels targetModule hosts sourceExternals) :
    SaturatedClosureCallImplementationWithCache context sourceModule
      callerFunction labels targetModule.wasmModule hosts.env hosts.spec
      sourceExternals (SaturatedClosureCallSupported context) :=
  SaturatedClosureCallImplementationWithCache.ofInternalCompiler spec
    (induction.toSelection spec.localsAligned)

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
    (adapted : FirTalos.adapt sourceModule = .ok targetModule)
    (closureTables :
      ClosureTablesAgree
        (initialStore sourceModule targetModule.wasmModule concreteExternals)
        witness) :
    ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
      sourceExternals facts remainingBytes ({} : RuntimeState) sourceEnv
      (initialStore sourceModule targetModule.wasmModule concreteExternals)
      locals witness := by
  exact ⟨core,
    LazyCacheGlobalsRel.adaptedInitial checked adapted witness
      concreteExternals,
    closureTables⟩

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
      descriptorAgreement⟩, initialCache, initialClosureTables⟩
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
  have nextClosureTables :
      ClosureTablesAgree nextStore nextWitness :=
    step.toClosureTablesTransport.agree initialClosureTables
  exact ⟨step.simulates, step.externalsPreserved,
    step.hostDescriptorsPreserved, step.witnessDescriptorsPreserved, transfer,
    ⟨⟨⟨⟨nextRelated, nextOrdinary, nextFrameAligned, nextBudget⟩,
      by rw [step.externalsPreserved]; exact integerImplementation,
      by rw [step.externalsPreserved]; exact naturalImplementation,
      by rw [step.externalsPreserved]; exact scalarImplementation⟩,
      nextDescriptorAgreement⟩, nextCache, nextClosureTables⟩⟩

/--
Frame-driven generated lazy miss.

The canonical cache frame and hereditary callee result determine every
dynamic publication artifact: the concrete `cacheSet` result, the pre-existing
physical value/flag lanes, both generated global writes, the caller-local
write, and the immutable host tables. Callers retain only the static
compiler/adapter selections, the hereditary declaration theorem, the
facts-aware semantic publication transport, and the declaration result-kind
alignment. The concrete host slot's name and kind are derived from the
whole-cache invariant.
-/
theorem
    BudgetedCapacityPreservingLazyStep.miss_of_cachedDeclarationFrame
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {calleeContext : Fir.Wasm.Context}
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
    {sourceRuntime callRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {initial afterCall : Wasm.Store Host}
    {locals : Wasm.Locals}
    {initialWitness callWitness : RefinementWitness}
    {physical : Wasm.Value}
    {cacheIndex resultIndex stepCost remainingBytes : Nat}
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (declValue : decl.value = .fap declaration #[])
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (kindEq :
      Fir.Wasm.checkedAbiKind decl.type = .ok kind)
    (cacheEq :
      context.cachedDeclarations.findIdx? (· == declaration) =
        some cacheIndex)
    (declarationFound :
      context.program.findDecl? declaration = some sourceDeclaration)
    (declarationParams : sourceDeclaration.params = #[])
    (declarationBody : sourceDeclaration.value = .code calleeCode)
    (contexts : DeclarationContextsCoherent context calleeContext)
    (callee :
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache calleeContext
        sourceModule calleeFunction module hostEnv sourceExternals
        sourceRuntime callRuntime [] calleeCode targetFunction declarationId
        initial afterCall initialWitness callWitness [] resultKind sourceValue
        physical stepCost)
    (importFound :
      module.imports[cacheSetId]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : cacheSetId < module.imports.length)
    (contractFound :
      spec.contracts[cacheSetId]? =
        some (cacheSetContract declaration kind))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (resultKindAt :
      (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
        some kind)
    (publicationOrdinary :
      ReuseTokenOrdinaryBindTransport facts decl.fvarId callRuntime
        (callRuntime.setGlobal declaration sourceValue) sourceEnv sourceValue)
    (resultKindEq : resultKind = kind) :
    ∃ nextStore nextLocals,
      BudgetedCapacityPreservingLazyStep .miss facts context callerFunction
            module hostEnv sourceExternals decl continuation
            [.globalGet (2 * cacheIndex),
              .iff 0 0 [] [
                .call declarationId,
                .call cacheSetId,
                .globalSet (2 * cacheIndex + 1),
                .const 1,
                .globalSet (2 * cacheIndex)],
              .globalGet (2 * cacheIndex + 1)]
            sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
            locals nextLocals resultIndex initialWitness callWitness physical
            stepCost ∧
        LazyCacheGlobalsRel callWitness sourceModule nextRuntime nextStore := by
  rcases invariant with
    ⟨⟨⟨⟨initialRelated, _, frameAligned, _⟩, _, _, _⟩,
      descriptorAgreement⟩, initialCache, _initialClosureTables⟩
  obtain ⟨initializerFound, signature⟩ :=
    generated.select kindEq declarationFound
      (by simp [declarationParams]) cacheEq
  obtain ⟨cacheSlot, cacheFound, cacheKindEq⟩ :=
    callee.cacheTable.hostSlot initializerFound signature
  have valueRelated :
      PhysicalValueRel callWitness kind physical sourceValue := by
    simpa [resultKindEq] using
      callee.declaration.capacityPreserving.successful.valueRelated
  have cacheDescriptorsEq :
      afterCall.host.closureDescriptors = callWitness.closureDescriptors :=
    callee.declaration.hostDescriptorsPreserved.trans
      (descriptorAgreement.trans
        callee.declaration.witnessDescriptorsPreserved.symm)
  obtain ⟨runtimeAfter, operation, _, _, _⟩ :=
    cacheSetStep_of_refines
      callee.declaration.capacityPreserving.successful.runtimeRelated
      valueRelated cacheFound cacheKindEq cacheDescriptorsEq
  let afterCache := replaceRuntime afterCall runtimeAfter
  have operationEq :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache := by
    simpa [afterCache] using operation
  obtain ⟨oldFlag, oldValue, flagAfterCall, valueAfterCall⟩ :=
    callee.cacheTable.slotLanesPresent initializerFound signature
  have valueAfterCache :
      afterCache.globals.globals[2 * cacheIndex + 1]? = some oldValue := by
    rw [cacheSetStep_preserves_wasmGlobals operationEq]
    exact valueAfterCall
  have flagAfterCache :
      afterCache.globals.globals[2 * cacheIndex]? = some oldFlag := by
    rw [cacheSetStep_preserves_wasmGlobals operationEq]
    exact flagAfterCall
  let valueStore :=
    writeWasmGlobal afterCache (2 * cacheIndex + 1) physical
  have valueStoreEq :
      valueStore =
        writeWasmGlobal afterCache (2 * cacheIndex + 1) physical := rfl
  have flagAfterValue :
      valueStore.globals.globals[2 * cacheIndex]? = some oldFlag := by
    rw [valueStoreEq, writeWasmGlobal_get_ne (by omega)]
    exact flagAfterCache
  let nextStore := writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)
  obtain ⟨nextLocals, targetSet, _⟩ :=
    frameAligned.set?
      (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := nextStore)
      (nextWitness := callWitness)
      (physical := physical) resultFound
  have publicationExternals :
      nextStore.host.externals = afterCall.host.externals := by
    simp [nextStore, valueStore, afterCache, writeWasmGlobal, replaceRuntime,
      clearFailure]
  have publicationDescriptors :
      nextStore.host.closureDescriptors =
        afterCall.host.closureDescriptors := by
    simp [nextStore, valueStore, afterCache, writeWasmGlobal, replaceRuntime,
      clearFailure]
  have publicationDispatch :
      nextStore.host.closureDispatch =
        afterCall.host.closureDispatch := by
    simp [nextStore, valueStore, afterCache, writeWasmGlobal, replaceRuntime,
      clearFailure]
  obtain ⟨step, nextCache⟩ :=
    BudgetedCapacityPreservingLazyStep.miss_of_cachedDeclaration_cacheSet
      sourceStep declValue initialRelated.1 initialCache generated kindEq cacheEq
      declarationFound declarationParams declarationBody contexts callee
      importFound hostSatisfies importInBounds contractFound parameterCount
      resultCount operationEq valueAfterCache valueStoreEq flagAfterValue
      resultFound resultKindAt targetSet publicationOrdinary resultKindEq
      cacheFound cacheKindEq cacheDescriptorsEq publicationExternals
      publicationDispatch publicationDescriptors
  exact ⟨nextStore, nextLocals, step, nextCache⟩

/--
Source/static admission shared by generated lazy-cache hits and misses.

The relation names only the source nullary call, its declaration/result ABI,
and the destination local. Cache indices, numeric call targets, symbolic
code, executable code, physical values, and target executions are deliberately
absent and are recovered from the production compiler pipeline.
-/
inductive LazyCacheCallSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Name → LCNF.Decl .impure → AbiKind → Prop where
  | intro
      {decl : LCNF.LetDecl .impure}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      (valueEq : decl.value = .fap declaration #[])
      (kindEq : Fir.Wasm.checkedAbiKind decl.type = .ok resultKind)
      (targetEq :
        context.program.findDecl? declaration = some sourceDeclaration)
      (paramsEq : sourceDeclaration.params.isEmpty = true)
      (resultCompiled :
        Fir.Wasm.getLocal context decl.fvarId =
          .ok (.localGet decl.fvarId, resultKind)) :
      LazyCacheCallSupported context decl declaration sourceDeclaration
        resultKind

/--
The internal-declaration specialization of lazy-cache admission.

External nullary declarations require their own hereditary external-result
branch; this relation records exactly the generated source body needed by the
ordinary declaration induction used for an internal miss.
-/
inductive LazyCacheInternalMissSupported (context : Fir.Wasm.Context) :
    LCNF.LetDecl .impure → Name → LCNF.Decl .impure → AbiKind →
      LCNF.Code .impure → Prop where
  | intro
      {decl : LCNF.LetDecl .impure}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      {calleeCode : LCNF.Code .impure}
      (call :
        LazyCacheCallSupported context decl declaration sourceDeclaration
          resultKind)
      (bodyEq : sourceDeclaration.value = .code calleeCode) :
      LazyCacheInternalMissSupported context decl declaration
        sourceDeclaration resultKind calleeCode

/--
Exact recursive induction result consumed by one internal lazy-cache miss.

The production adapter chooses the declaration index. At that index the
recursive program proof returns the cache-aware hereditary callee theorem and
the source fact-analysis result needed to publish the value. Quantification
over the compiler-selected index keeps this a structural induction boundary,
not a caller-chosen target execution certificate.
-/
def LazyCacheInternalMissInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (facts : ReuseCapacityFacts)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (resultId : FVarId)
    (declaration : Name)
    (calleeCode : LCNF.Code .impure)
    (resultKind : AbiKind)
    (initial : Wasm.Store Host)
    (initialWitness : RefinementWitness)
    (sourceValue : Value)
    (stepCost : Nat) : Prop :=
  ∀ {declarationId : Nat},
    callIndex? sourceModule (.declaration declaration) = some declarationId →
      ∃ calleeContext : Fir.Wasm.Context,
        ∃ calleeFunction targetFunction callRuntime afterCall callWitness
            physical,
          DeclarationContextsCoherent context calleeContext ∧
            BudgetedCapacityPreservingSuccessfulDeclarationWithCache
                calleeContext sourceModule calleeFunction module hostEnv
                sourceExternals sourceRuntime callRuntime [] calleeCode
                targetFunction declarationId initial afterCall initialWitness
                callWitness [] resultKind sourceValue physical stepCost ∧
              ReuseTokenOrdinaryBindTransport facts resultId callRuntime
                (callRuntime.setGlobal declaration sourceValue) sourceEnv
                sourceValue

/--
Hereditary declaration selection parameterized by one source-runtime
postcondition.

This factors the recursive target theorem from the semantic property required
at its exact source post-state. Instantiating `Post` with reachability
disjointness gives the preferred cache-publication boundary; instantiating it
with `True` records the ordinary hereditary callee theorem alone.
-/
def LazyCacheInternalCalleeInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (sourceRuntime : RuntimeState)
    (declaration : Name)
    (calleeCode : LCNF.Code .impure)
    (resultKind : AbiKind)
    (initial : Wasm.Store Host)
    (initialWitness : RefinementWitness)
    (sourceValue : Value)
    (stepCost : Nat)
    (Post : RuntimeState → Prop) : Prop :=
  ∀ {declarationId : Nat},
    callIndex? sourceModule (.declaration declaration) = some declarationId →
      ∃ calleeContext : Fir.Wasm.Context,
        ∃ calleeFunction targetFunction callRuntime afterCall callWitness
            physical,
          DeclarationContextsCoherent context calleeContext ∧
            BudgetedCapacityPreservingSuccessfulDeclarationWithCache
                calleeContext sourceModule calleeFunction module hostEnv
                sourceExternals sourceRuntime callRuntime [] calleeCode
                targetFunction declarationId initial afterCall initialWitness
                callWitness [] resultKind sourceValue physical stepCost ∧
              Post callRuntime

/-- Preferred recursive cache-miss boundary: the hereditary callee result is
paired with reachability disjointness at its exact semantic post-state. -/
abbrev LazyCacheInternalPublicationInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (facts : ReuseCapacityFacts)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (declaration : Name)
    (calleeCode : LCNF.Code .impure)
    (resultKind : AbiKind)
    (initial : Wasm.Store Host)
    (initialWitness : RefinementWitness)
    (sourceValue : Value)
    (stepCost : Nat) : Prop :=
  LazyCacheInternalCalleeInduction context sourceModule module hostEnv
    sourceExternals sourceRuntime declaration calleeCode resultKind initial
    initialWitness sourceValue stepCost fun callRuntime =>
      ReuseTokenPublicationDisjoint facts callRuntime sourceEnv sourceValue

/-- Hereditary callee theorem without a publication property. This is already
enough for non-heap results, whose ownership closure is empty. -/
abbrev LazyCacheInternalHereditaryInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    (sourceRuntime : RuntimeState)
    (declaration : Name)
    (calleeCode : LCNF.Code .impure)
    (resultKind : AbiKind)
    (initial : Wasm.Store Host)
    (initialWitness : RefinementWitness)
    (sourceValue : Value)
    (stepCost : Nat) : Prop :=
  LazyCacheInternalCalleeInduction context sourceModule module hostEnv
    sourceExternals sourceRuntime declaration calleeCode resultKind initial
    initialWitness sourceValue stepCost fun _ => True

/-- Reachability-disjoint declaration induction constructively supplies the
facts-aware ordinary-token publication transport. -/
theorem LazyCacheInternalPublicationInduction.toMissInduction
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {resultId : FVarId}
    {declaration : Name}
    {calleeCode : LCNF.Code .impure}
    {resultKind : AbiKind}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {sourceValue : Value}
    {stepCost : Nat}
    (induction :
      LazyCacheInternalPublicationInduction context sourceModule module hostEnv
        sourceExternals facts sourceRuntime sourceEnv declaration calleeCode
        resultKind initial initialWitness sourceValue stepCost) :
    LazyCacheInternalMissInduction context sourceModule module hostEnv
      sourceExternals facts sourceRuntime sourceEnv resultId declaration
      calleeCode resultKind initial initialWitness sourceValue stepCost := by
  intro declarationId declarationCall
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee, disjoint⟩ :=
    induction declarationCall
  exact ⟨calleeContext, calleeFunction, targetFunction, callRuntime, afterCall,
    callWitness, physical, contexts, callee,
    ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint declaration
      disjoint⟩

/-- Non-heap lazy results add the publication property to any hereditary
callee theorem without an alias-analysis premise. -/
theorem
    LazyCacheInternalHereditaryInduction.publication_of_nonHeapReference
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {declaration : Name}
    {calleeCode : LCNF.Code .impure}
    {resultKind : AbiKind}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {sourceValue : Value}
    {stepCost : Nat}
    (induction :
      LazyCacheInternalHereditaryInduction context sourceModule module hostEnv
        sourceExternals sourceRuntime declaration calleeCode resultKind initial
        initialWitness sourceValue stepCost)
    (nonHeap : IsNonHeapReference sourceValue) :
    LazyCacheInternalPublicationInduction context sourceModule module hostEnv
      sourceExternals facts sourceRuntime sourceEnv declaration calleeCode
      resultKind initial initialWitness sourceValue stepCost := by
  intro declarationId declarationCall
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee, _⟩ :=
    induction declarationCall
  exact ⟨calleeContext, calleeFunction, targetFunction, callRuntime, afterCall,
    callWitness, physical, contexts, callee,
    ReuseTokenPublicationDisjoint.of_nonHeapReference nonHeap⟩

/--
Every hereditary declaration returning an exact non-object ABI kind satisfies
cache-publication disjointness constructively.

The returned semantic value is recovered from the recursive declaration's
existing physical refinement. Only `.object` and representation-polymorphic
`.tobject` can denote a semantic heap-reference root, so exact tagged, erased,
reuse-token, integer-width, and scalar results need no separate alias theorem.
-/
theorem
    LazyCacheInternalHereditaryInduction.publication_of_nonHeapKind
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {declaration : Name}
    {calleeCode : LCNF.Code .impure}
    {resultKind : AbiKind}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {sourceValue : Value}
    {stepCost : Nat}
    (induction :
      LazyCacheInternalHereditaryInduction context sourceModule module hostEnv
        sourceExternals sourceRuntime declaration calleeCode resultKind initial
        initialWitness sourceValue stepCost)
    (notObject : resultKind ≠ .object)
    (notTObject : resultKind ≠ .tobject) :
    LazyCacheInternalPublicationInduction context sourceModule module hostEnv
      sourceExternals facts sourceRuntime sourceEnv declaration calleeCode
      resultKind initial initialWitness sourceValue stepCost := by
  intro declarationId declarationCall
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee, _⟩ :=
    induction declarationCall
  have nonHeap : IsNonHeapReference sourceValue :=
    callee.declaration.capacityPreserving.successful.valueRelated
      |>.isNonHeapReference_of_kind notObject notTObject
  exact ⟨calleeContext, calleeFunction, targetFunction, callRuntime, afterCall,
    callWitness, physical, contexts, callee,
    ReuseTokenPublicationDisjoint.of_nonHeapReference nonHeap⟩

/--
Structural compiler-derived internal lazy-cache miss.

The source support relation supplies only the nullary declaration and its
body. Production lowering/adaptation chooses the cache, declaration, and
publication-call indices. `ConcreteSupportedFunction` then supplies the exact
resolved publication contract and destination layout, while the recursive
program induction supplies the hereditary callee result at the selected
declaration index. No target execution or numeric-index certificate is a
premise.
-/
theorem BudgetedCapacityPreservingLazyStep.miss_of_supportedFunctionCompiler
    {facts : ReuseCapacityFacts}
    {program : Fir.LeanIR.ImpureProgram}
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    {callerCode : LCNF.Code .impure}
    (spec :
      ConcreteSupportedFunction program context callerCode sourceModule
        callerFunction targetModule hosts)
    (sourceExternals : ExternalImpl)
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {sourceDeclaration : LCNF.Decl .impure}
    {resultKind : AbiKind}
    {calleeCode : LCNF.Code .impure}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness : RefinementWitness}
    (supported :
      LazyCacheInternalMissSupported context decl declaration
        sourceDeclaration resultKind calleeCode)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule callerFunction labels valueCode =
        .ok targetValue)
    (resultFound :
      findFVar? (functionBindings callerFunction) decl.fvarId =
        some resultIndex)
    (induction :
      LazyCacheInternalMissInduction context sourceModule
        targetModule.wasmModule hosts.env sourceExternals facts sourceRuntime
        sourceEnv decl.fvarId declaration calleeCode resultKind initial
        initialWitness sourceValue stepCost) :
    ∃ nextStore nextLocals nextWitness physical,
      BudgetedCapacityPreservingLazyStep .miss facts context callerFunction
          targetModule.wasmModule hosts.env sourceExternals decl continuation
          targetValue sourceRuntime nextRuntime sourceEnv sourceValue initial
          nextStore locals nextLocals resultIndex initialWitness nextWitness
          physical stepCost ∧
        reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId) ∧
          LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore := by
  rcases supported with
    ⟨⟨valueEq, kindEq, targetEq, paramsEq, resultCompiled⟩, bodyEq⟩
  obtain ⟨cacheIndex, declarationId, cacheSetId, cacheEq, declarationCall,
      cacheSetCall, _, targetValueEq⟩ :=
    compileCachedLetValue_adapted_inv context sourceModule callerFunction
      labels decl declaration sourceDeclaration resultKind valueCode
      targetValue valueEq kindEq targetEq paramsEq valueCompiled valueAdapted
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee,
      publicationOrdinary⟩ :=
    induction declarationCall
  obtain ⟨imp, importFound, importInBounds, contractFound, parameterCount,
      resultCount⟩ :=
    spec.cacheSetCall cacheSetCall
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    spec.localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  have declarationParams : sourceDeclaration.params = #[] :=
    Array.isEmpty_iff.mp paramsEq
  obtain ⟨nextStore, nextLocals, step, nextCache⟩ :=
    BudgetedCapacityPreservingLazyStep.miss_of_cachedDeclarationFrame
      sourceStep valueEq invariant generated kindEq cacheEq targetEq
      declarationParams bodyEq contexts callee importFound spec.hostsSatisfy
      importInBounds contractFound parameterCount resultCount resultFound
      resultKindAt publicationOrdinary rfl
  refine
    ⟨nextStore, nextLocals, callWitness, physical, ?_, ?_, nextCache⟩
  · rw [targetValueEq]
    exact step
  · simp [Fir.Wasm.reuseCapacityLetFacts?, valueEq]

/--
A compiler-selected internal lazy miss with a non-heap result preserves source
ordinaryness from body entry through cache publication.

The hereditary callee supplies entry-to-return ordinaryness. Compiler
inversion selects that exact callee, while non-heap publication leaves the
semantic heap unchanged. This is the source-side transport needed by a fixed
declaration-entry invariant; it is intentionally unavailable for arbitrary
heap-valued cache results.
-/
theorem
    SourceLazyLetResult.miss_ordinaryTransport_of_internalCompiler_nonHeap
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {sourceDeclaration : LCNF.Decl .impure}
    {resultKind : AbiKind}
    {calleeCode : LCNF.Code .impure}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {stepCost : Nat}
    (supported :
      LazyCacheInternalMissSupported context decl declaration
        sourceDeclaration resultKind calleeCode)
    (sourceStep :
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule callerFunction labels valueCode =
        .ok targetValue)
    (induction :
      LazyCacheInternalHereditaryInduction context sourceModule module hostEnv
        sourceExternals sourceRuntime declaration calleeCode resultKind initial
        initialWitness sourceValue stepCost)
    (notObject : resultKind ≠ .object)
    (notTObject : resultKind ≠ .tobject) :
    OrdinaryPersistenceTransport sourceRuntime nextRuntime := by
  rcases supported with
    ⟨⟨valueEq, kindEq, targetEq, paramsEq, resultCompiled⟩, bodyEq⟩
  obtain ⟨cacheIndex, declarationId, cacheSetId, cacheEq, declarationCall,
      cacheSetCall, valueCodeEq, targetValueEq⟩ :=
    compileCachedLetValue_adapted_inv context sourceModule callerFunction
      labels decl declaration sourceDeclaration resultKind valueCode
      targetValue valueEq kindEq targetEq paramsEq valueCompiled valueAdapted
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee, hereditaryPost⟩ :=
    induction declarationCall
  have declarationParams : sourceDeclaration.params = #[] :=
    Array.isEmpty_iff.mp paramsEq
  have publicationRuntimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue :=
    (SourceLazyLetResult.miss_cacheFacts_of_callee valueEq targetEq
      declarationParams bodyEq sourceStep
      (contexts.sourceCodeResult
        callee.declaration.capacityPreserving.successful.sourceResult)).2
  have nonHeap : IsNonHeapReference sourceValue :=
    callee.declaration.capacityPreserving.successful.valueRelated
      |>.isNonHeapReference_of_kind notObject notTObject
  apply callee.declaration.ordinaryTransport.congrAfter
  rw [publicationRuntimeEq]
  exact
    (RuntimeState.setGlobal_heap_eq_of_nonHeapReference callRuntime declaration
      sourceValue nonHeap).symm

/--
Structural compiler-derived cache hit.

The source-only facts identify a nullary declaration and its result lane.
Successful production lowering/adaptation then supplies the cache and call
indices by inversion, while the generated environment and canonical frame
supply the populated slot and checked local update. No target execution
certificate is a premise.
-/
theorem BudgetedCapacityPreservingLazyStep.hit_of_compiler
    {facts : ReuseCapacityFacts}
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl)
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {target : LCNF.Decl .impure}
    {resultKind : AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {resultIndex remainingBytes stepCost : Nat}
    {initialWitness : RefinementWitness}
    (supported :
      LazyCacheCallSupported context decl declaration target resultKind)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts remainingBytes sourceRuntime sourceEnv initial
        locals initialWitness)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (stepCostEq : stepCost = 0) :
    ∃ nextStore nextLocals nextWitness physical,
      BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction
          module hostEnv sourceExternals decl continuation targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
          locals nextLocals resultIndex initialWitness nextWitness physical
          stepCost ∧
        reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId) ∧
          LazyCacheGlobalsRel nextWitness sourceModule nextRuntime nextStore := by
  rcases supported with
    ⟨valueEq, kindEq, targetEq, paramsEq, resultCompiled⟩
  obtain ⟨runtimeEq, semanticFound⟩ :=
    SourceLazyLetResult.hit_cacheFacts_of_valueEq valueEq targetEq paramsEq
      sourceStep
  subst nextRuntime
  subst stepCost
  obtain ⟨cacheIndex, _, _, cacheEq, _, _, valueCodeEq, targetValueEq⟩ :=
    compileCachedLetValue_adapted_inv context sourceModule sourceFunction labels
      decl declaration target resultKind valueCode targetValue valueEq kindEq
      targetEq paramsEq valueCompiled valueAdapted
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  rcases invariant with
    ⟨⟨⟨⟨initialRelated, _, frameAligned, _⟩, _, _, _⟩, _⟩,
      cacheTable, _closureTables⟩
  obtain ⟨initializerFound, signature⟩ :=
    generated.select kindEq targetEq paramsEq cacheEq
  obtain ⟨physical, slot⟩ :=
    cacheTable.populatedSlot initializerFound signature semanticFound
  obtain ⟨nextLocals, hit⟩ :=
    BudgetedCapacityPreservingLazyStep.hit_of_populatedSlot sourceStep
      initialRelated.stateRelated frameAligned resultFound resultKindAt slot
  refine ⟨initial, nextLocals, initialWitness, physical, ?_, ?_, cacheTable⟩
  · rw [targetValueEq]
    exact hit
  · simp [Fir.Wasm.reuseCapacityLetFacts?, valueEq]

/-- A generated cache hit returns in the unchanged semantic runtime. -/
theorem SourceLazyLetResult.hit_ordinaryTransport_of_supported
    {context : Fir.Wasm.Context}
    {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure}
    {declaration : Name}
    {sourceDeclaration : LCNF.Decl .impure}
    {resultKind : AbiKind}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    (supported :
      LazyCacheCallSupported context decl declaration sourceDeclaration
        resultKind)
    (sourceStep :
      SourceLazyLetResult .hit context sourceExternals sourceRuntime sourceEnv
        decl continuation nextRuntime sourceValue) :
    OrdinaryPersistenceTransport sourceRuntime nextRuntime := by
  rcases supported with
    ⟨valueEq, kindEq, targetEq, paramsEq, resultCompiled⟩
  obtain ⟨runtimeEq, semanticFound⟩ :=
    SourceLazyLetResult.hit_cacheFacts_of_valueEq valueEq targetEq paramsEq
      sourceStep
  subst nextRuntime
  exact OrdinaryPersistenceTransport.refl sourceRuntime

/--
Source-facing internal lazy-cache family handled by the structural compiler
law.

The hit constructor fixes the source allocation cost to zero. The miss
constructor retains the source declaration body and arbitrary recursive cost.
Neither constructor contains target code, numeric call indices, concrete
values, stores, witnesses, or executions.
-/
inductive LazyCacheInternalSupported (context : Fir.Wasm.Context) :
    LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
      LCNF.Code .impure → RuntimeState → Value → Nat → Prop where
  | hit
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      (call :
        LazyCacheCallSupported context decl declaration sourceDeclaration
          resultKind) :
      LazyCacheInternalSupported context .hit sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue 0
  | miss
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost : Nat}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      {calleeCode : LCNF.Code .impure}
      (call :
        LazyCacheInternalMissSupported context decl declaration
          sourceDeclaration resultKind calleeCode) :
      LazyCacheInternalSupported context .miss sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue stepCost

/--
Source-only hereditary admission for compiler-generated internal lazy calls.

A hit retains the ordinary static nullary-call facts. A miss additionally
retains the exact declaration-local row selected by production lowering and a
finite source derivation of the initializer body from the empty environment.
The first admitted miss family also records that its exact result ABI kind is
neither `.object` nor `.tobject`, which is the local source-side condition
needed for heap-neutral cache publication.
The initializer derivation may use a separately chosen recursive fragment;
this makes one lazy layer compositional without placing a target execution or
a recursive target-correctness theorem in the source premise.
-/
inductive LazyCacheInternalHereditarySupported
    (externals : ExternalImpl)
    (DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop)
    (InitializerLazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState →
          Value → Nat → Prop)
    (CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop)
    (EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate)
    (context : Fir.Wasm.Context) :
    LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
      LCNF.Code .impure → RuntimeState → Value → Nat → Prop where
  | hit
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      (call :
        LazyCacheCallSupported context decl declaration sourceDeclaration
          resultKind) :
      LazyCacheInternalHereditarySupported externals DirectSupported
        ExternalSupported InitializerLazySupported CaseSupported
        EffectSupported context .hit sourceRuntime sourceEnv decl continuation
        nextRuntime sourceValue 0
  | miss
      {sourceRuntime nextRuntime callRuntime : RuntimeState}
      {sourceEnv calleeResultEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {sourceValue : Value}
      {stepCost : Nat}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      {calleeCode : LCNF.Code .impure}
      {calleeFunction : Fir.Wasm.Function}
      {calleeResultFacts : ReuseCapacityFacts}
      (call :
        LazyCacheInternalMissSupported context decl declaration
          sourceDeclaration resultKind calleeCode)
      (row :
        LoweredInternalDeclaration context.program context.cachedDeclarations
          sourceDeclaration calleeCode calleeFunction)
      (resultClassified :
        Fir.Wasm.abiKind? sourceDeclaration.type = .ok (some resultKind))
      (notObject : resultKind ≠ .object)
      (notTObject : resultKind ≠ .tobject)
      (callee :
        ReuseCapacityDirectHereditaryCodeEvaluates externals DirectSupported
          ExternalSupported InitializerLazySupported CaseSupported
          EffectSupported directLetAllocationCost row.context resultKind []
          sourceRuntime [] calleeCode calleeResultFacts callRuntime
          calleeResultEnv sourceValue stepCost) :
      LazyCacheInternalHereditarySupported externals DirectSupported
        ExternalSupported InitializerLazySupported CaseSupported
        EffectSupported context .miss sourceRuntime sourceEnv decl continuation
        nextRuntime sourceValue stepCost

/-- The first production lazy family: callers and ordinary recursive callees
may use the complete current production fragment, while each cached nullary
initializer is proved in that fragment with no nested lazy lookup. -/
abbrev ProductionHereditaryLazySupported
    (sourceExternals : ExternalImpl) (context : Fir.Wasm.Context) :=
  LazyCacheInternalHereditarySupported sourceExternals
    (fun context => ReuseBudgetedDirectSupported context)
    (fun context => PureExternalSupported context sourceExternals)
    (fun _ => NoReuseCapacityLazySupported)
    (fun context => ProductionCasesSupported context)
    (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
    context

/--
Source-only result-kind policy for the internal lazy fragment whose
publication safety is representation-derived.

Exact `.object` results are heap references, while `.tobject` is
representation-polymorphic and may be one. Every other ABI kind determines a
non-heap semantic publication root from `PhysicalValueRel`.
-/
def LazyCacheInternalResultKindsNonHeap
    (context : Fir.Wasm.Context) : Prop :=
  ∀ {decl : LCNF.LetDecl .impure}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      {calleeCode : LCNF.Code .impure},
    LazyCacheInternalMissSupported context decl declaration sourceDeclaration
        resultKind calleeCode →
      resultKind ≠ .object ∧ resultKind ≠ .tobject

/--
Recursive generated-declaration theorem before cache-publication alias
reasoning.

This is the ordinary hereditary target induction uniformly selected from an
admitted internal source miss and the canonical caller frame. It retains no
publication postcondition; result-kind classification or a heap alias theorem
adds that source property separately.
-/
def LazyCacheInternalHereditaryDeclarationInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {callerFunction : Fir.Wasm.Function}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      {calleeCode : LCNF.Code .impure}
      {sourceValue : Value}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {remainingBytes stepCost : Nat}
      {initialWitness : RefinementWitness},
    LazyCacheInternalMissSupported context decl declaration sourceDeclaration
        resultKind calleeCode →
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
          decl continuation nextRuntime sourceValue →
        ConcreteReuseCapacityCacheFrame sourceModule callerFunction
            sourceExternals facts remainingBytes sourceRuntime sourceEnv
            initial locals initialWitness →
          LazyCacheInternalHereditaryInduction context sourceModule
            targetModule.wasmModule hosts.env sourceExternals sourceRuntime
            declaration calleeCode resultKind initial initialWitness
            sourceValue stepCost

/--
Module-level recursive theorem required by internal lazy misses.

For every admitted source miss and canonical caller frame, declaration
induction must produce the hereditary cache-aware callee result at the numeric
index chosen later by production adaptation, together with the exact
facts-aware publication transport. This is the single recursive semantic
condition left after compiler, resolver, cache-layout, and caller-local
selection have been derived. It is quantified uniformly over executions and
therefore is a program theorem, not a per-call target certificate.
-/
def LazyCacheInternalDeclarationInduction
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (targetModule : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {callerFunction : Fir.Wasm.Function}
      {sourceRuntime nextRuntime : RuntimeState}
      {sourceEnv : Env}
      {decl : LCNF.LetDecl .impure}
      {continuation : LCNF.Code .impure}
      {declaration : Name}
      {sourceDeclaration : LCNF.Decl .impure}
      {resultKind : AbiKind}
      {calleeCode : LCNF.Code .impure}
      {sourceValue : Value}
      {initial : Wasm.Store Host}
      {locals : Wasm.Locals}
      {remainingBytes stepCost : Nat}
      {initialWitness : RefinementWitness},
    LazyCacheInternalMissSupported context decl declaration sourceDeclaration
        resultKind calleeCode →
      SourceLazyLetResult .miss context sourceExternals sourceRuntime sourceEnv
          decl continuation nextRuntime sourceValue →
        ConcreteReuseCapacityCacheFrame sourceModule callerFunction
            sourceExternals facts remainingBytes sourceRuntime sourceEnv
            initial locals initialWitness →
          LazyCacheInternalPublicationInduction context sourceModule
            targetModule.wasmModule hosts.env sourceExternals facts
            sourceRuntime sourceEnv declaration calleeCode resultKind initial
            initialWitness sourceValue stepCost

/--
For modules whose admitted internal lazy results have exact non-heap ABI
kinds, ordinary hereditary declaration induction supplies the complete
publication-aware induction.

The adapter is uniform over source executions. It derives the semantic
non-heap fact from the callee's already-proved physical result relation and
therefore adds no target execution premise.
-/
theorem LazyCacheInternalDeclarationInduction.ofHereditaryNonHeap
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (resultKinds : LazyCacheInternalResultKindsNonHeap context)
    (declarations :
      LazyCacheInternalHereditaryDeclarationInduction context sourceModule
        targetModule hosts sourceExternals) :
    LazyCacheInternalDeclarationInduction context sourceModule targetModule
      hosts sourceExternals := by
  intro facts callerFunction sourceRuntime nextRuntime sourceEnv decl
    continuation declaration sourceDeclaration resultKind calleeCode
    sourceValue initial locals remainingBytes stepCost initialWitness call
    sourceStep invariant
  obtain ⟨notObject, notTObject⟩ := resultKinds call
  exact
    LazyCacheInternalHereditaryInduction.publication_of_nonHeapKind
      (declarations call sourceStep invariant) notObject notTObject

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

/--
Lazy-cache implementation strengthened with the source ordinaryness transport
needed by a fixed declaration-entry invariant.

The executable/cache implementation remains the existing reusable structure.
The additional field is a semantic consequence of the selected source path
and hereditary callee. It is valid for hits and the current non-heap internal
fragment, but deliberately not postulated for arbitrary heap publication.
-/
structure LazyCacheImplementationWithEntryTransports
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
  implementation :
    LazyCacheImplementation context sourceModule sourceFunction labels module
      hostEnv sourceExternals LazySupported
  ordinaryTransport :
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
      {stepCost remainingBytes : Nat}
      {initialWitness : RefinementWitness},
      LazySupported path sourceRuntime sourceEnv decl continuation nextRuntime
          sourceValue stepCost →
        SourceLazyLetResult path context sourceExternals sourceRuntime sourceEnv
            decl continuation nextRuntime sourceValue →
          ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals facts remainingBytes sourceRuntime sourceEnv
              initial locals initialWitness →
            Fir.Wasm.compileLetValue context decl = .ok valueCode →
              instructions sourceModule sourceFunction labels valueCode =
                  .ok targetValue →
                OrdinaryPersistenceTransport sourceRuntime nextRuntime

/--
Production internal hit/miss composition constructs the uniform lazy
implementation from one generated cache environment and the recursive
declaration theorem.

Hits are discharged directly by the generated table. Misses use the
module-level induction only for the hereditary callee/publication result; all
target indices, imports, contracts, locals, concrete publication operations,
and successor cache state are recovered by the compiler-derived theorem.
-/
theorem LazyCacheImplementation.ofInternalCompiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (declarations :
      LazyCacheInternalDeclarationInduction context sourceModule targetModule
        hosts sourceExternals) :
    LazyCacheImplementation context sourceModule sourceFunction labels
      targetModule.wasmModule hosts.env sourceExternals
      (LazyCacheInternalSupported context) := by
  refine ⟨generated, ?_⟩
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals resultIndex stepCost
    remainingBytes initialWitness supported sourceStep invariant valueCompiled
    valueAdapted resultFound
  cases supported with
  | hit call =>
      exact
        BudgetedCapacityPreservingLazyStep.hit_of_compiler context sourceModule
          sourceFunction labels targetModule.wasmModule hosts.env
          sourceExternals call spec.localsAligned generated sourceStep invariant
          valueCompiled valueAdapted resultFound rfl
  | miss call =>
      exact
        BudgetedCapacityPreservingLazyStep.miss_of_supportedFunctionCompiler
          context sourceModule sourceFunction labels targetModule hosts
          spec sourceExternals call generated sourceStep invariant
          valueCompiled valueAdapted resultFound
          (LazyCacheInternalPublicationInduction.toMissInduction
            (resultId := decl.fvarId)
            (declarations call sourceStep invariant))

/--
The compiler-generated non-heap internal lazy family supplies both its
evolved-cache implementation and the source ordinaryness transport required
at a fixed declaration entry.

Hits are runtime identities. On a miss the same hereditary callee used for
publication preserves ordinaryness to its return, and the non-heap result-kind
policy makes the subsequent semantic `setGlobal` heap-neutral.
-/
theorem
    LazyCacheImplementationWithEntryTransports.ofInternalCompilerNonHeap
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (resultKinds : LazyCacheInternalResultKindsNonHeap context)
    (declarations :
      LazyCacheInternalHereditaryDeclarationInduction context sourceModule
        targetModule hosts sourceExternals) :
    LazyCacheImplementationWithEntryTransports context sourceModule
      sourceFunction labels targetModule.wasmModule hosts.env sourceExternals
      (LazyCacheInternalSupported context) := by
  refine
    ⟨LazyCacheImplementation.ofInternalCompiler spec generated
      (LazyCacheInternalDeclarationInduction.ofHereditaryNonHeap resultKinds
        declarations),
      ?_⟩
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals stepCost remainingBytes
    initialWitness supported sourceStep invariant valueCompiled valueAdapted
  cases supported with
  | hit call =>
      exact
        SourceLazyLetResult.hit_ordinaryTransport_of_supported call sourceStep
  | miss call =>
      obtain ⟨notObject, notTObject⟩ := resultKinds call
      exact
        SourceLazyLetResult.miss_ordinaryTransport_of_internalCompiler_nonHeap
          (stepCost := stepCost) call sourceStep valueCompiled valueAdapted
          (declarations (stepCost := stepCost) call sourceStep invariant)
          notObject notTObject

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

/--
An entry-transporting lazy implementation supplies the complete lazy runtime
law over one fixed execution entry.

The implementation's successor cache table is used verbatim. The
path-specific source ordinaryness theorem and the budgeted step's concrete
transports extend the entry accumulator, so both cache hits and non-heap
misses compose inside hereditary declaration bodies.
-/
theorem
    LazyCacheImplementationWithEntryTransports.runtimeRefinesEntryRelative
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
      LazyCacheImplementationWithEntryTransports context sourceModule
        sourceFunction labels module hostEnv sourceExternals LazySupported)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels module hostEnv sourceExternals LazySupported
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) := by
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals resultIndex remainingBytes
    stepCost initialWitness supported stepFits invariant sourceStep
    valueCompiled valueAdapted resultFound
  rcases invariant with ⟨cacheInvariant, entryTransports⟩
  obtain ⟨nextStore, nextLocals, nextWitness, physical, step, transfer,
      nextCache⟩ :=
    implementation.implementation.step supported sourceStep cacheInvariant
      valueCompiled valueAdapted resultFound
  have ordinary :
      OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
    implementation.ordinaryTransport supported sourceStep cacheInvariant
      valueCompiled valueAdapted
  obtain ⟨simulates, externalsPreserved, hostDescriptorsPreserved,
      witnessDescriptorsPreserved, nextTransfer, nextCacheInvariant⟩ :=
    cacheInvariant.ofLazyCacheResult stepFits step (fun _ => nextCache)
      resultFound transfer
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        nextStore entryWitness nextWitness :=
    entryTransports.step step.witnessTransport step.capacityTransport ordinary
      step.externalsPreserved step.toClosureTablesTransport
  exact ⟨nextStore, nextLocals, nextWitness,
    eraseReuseCapacityFact facts decl.fvarId, simulates, externalsPreserved,
    hostDescriptorsPreserved, witnessDescriptorsPreserved, nextTransfer,
    ⟨nextCacheInvariant, nextEntry⟩⟩

/--
Public facts-indexed lazy runtime law for compiler-generated internal
declarations.

This is the exact boundary consumed by
`codeWP_of_reuseCapacityBudgetedCodeEvaluates_exactReturn`: source evaluation
contains only `LazyCacheInternalSupported`, while target execution is derived
from the supported export, generated cache environment, and the uniform
declaration induction.
-/
theorem ConcreteSupportedFunction.internalLazyRuntimeRefines
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (declarations :
      LazyCacheInternalDeclarationInduction context sourceModule targetModule
        hosts sourceExternals) :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels targetModule.wasmModule hosts.env sourceExternals
      (LazyCacheInternalSupported context)
      (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals) :=
  (LazyCacheImplementation.ofInternalCompiler spec generated
    declarations).runtimeRefines

/--
Public internal lazy-runtime law for the representation-derived non-heap
fragment.

Clients provide only the recursive hereditary declaration theorem and the
source result-kind policy. Publication disjointness, retained-token transport,
and the complete compiler-generated hit/miss implementation are derived.
-/
theorem ConcreteSupportedFunction.internalNonHeapLazyRuntimeRefines
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (resultKinds : LazyCacheInternalResultKindsNonHeap context)
    (declarations :
      LazyCacheInternalHereditaryDeclarationInduction context sourceModule
        targetModule hosts sourceExternals) :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels targetModule.wasmModule hosts.env sourceExternals
      (LazyCacheInternalSupported context)
      (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals) :=
  spec.internalLazyRuntimeRefines generated
    (LazyCacheInternalDeclarationInduction.ofHereditaryNonHeap
      resultKinds declarations)

/--
Public compiler-generated non-heap lazy law over the entry-relative
whole-cache frame.

This is the lazy premise consumed by the structural hereditary body theorem:
hits preserve the existing table, misses consume the recursively evolved
table and publish their own non-heap result, and both paths extend every
fixed-entry representation transport.
-/
theorem
    ConcreteSupportedFunction.internalNonHeapLazyRuntimeRefines_entryRelativeCache
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    (spec :
      ConcreteSupportedFunction program context callerCode sourceModule
        sourceFunction targetModule hosts)
    (generated :
      LazyCacheGeneratedEnvironment context sourceModule)
    (resultKinds : LazyCacheInternalResultKindsNonHeap context)
    (declarations :
      LazyCacheInternalHereditaryDeclarationInduction context sourceModule
        targetModule hosts sourceExternals)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      sourceFunction labels targetModule.wasmModule hosts.env sourceExternals
      (LazyCacheInternalSupported context)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) :=
  (LazyCacheImplementationWithEntryTransports.ofInternalCompilerNonHeap spec
    generated resultKinds declarations).runtimeRefinesEntryRelative

/--
Static compiler/adaptor evidence for one generated declaration body.

Unlike `ConcreteSupportedExport`, this boundary does not require an export
name or an export-table entry. It is therefore the right recursive unit for
ordinary internal calls and lazy initializers. Dynamic source and target
executions remain outside the structure.
-/
structure ConcreteSupportedDeclaration
    (context : Fir.Wasm.Context)
    (sourceCode : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule) where
  targetFunctionIndex : Nat
  targetFunction : Wasm.Function
  notImport : target.wasmModule.imports[targetFunctionIndex]? = none
  targetFunctionFound :
    target.wasmModule.funcs[
        targetFunctionIndex - target.wasmModule.imports.length]? =
      some targetFunction
  bodyAdapted :
    CodeAdapted context sourceModule sourceFunction [] sourceCode
      targetFunction.body
  localsAligned : LocalLayoutAligned context sourceFunction
  singleResult : targetFunction.results.length = 1

/-- Name-directed lookup and numeric lookup select the same typed entry when
they traverse the same canonical binding row. -/
private theorem findFVar?_kind_of_findLocalKind?
    {locals : Fir.Wasm.LocalKinds} {fvarId : FVarId} {kind : AbiKind}
    (found : Fir.Wasm.findLocalKind? locals fvarId = some kind) :
    ∃ index,
      findFVar? locals fvarId = some index ∧
        locals[index]?.map Prod.snd = some kind := by
  induction locals with
  | nil => simp [Fir.Wasm.findLocalKind?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, candidateKind⟩ := entry
      by_cases sameName : candidate.name == fvarId.name
      · rw [Fir.Wasm.findLocalKind?, if_pos sameName] at found
        simp only [Option.some.injEq] at found
        subst candidateKind
        exact ⟨0, by simp [findFVar?, sameName], by simp⟩
      · rw [Fir.Wasm.findLocalKind?, if_neg sameName] at found
        obtain ⟨index, indexFound, kindFound⟩ := ih found
        refine ⟨index + 1, ?_, ?_⟩
        · simp [findFVar?, sameName, indexFound]
        · simpa [Nat.add_comm] using kindFound

/-- Every production declaration uses one canonical binding row for symbolic
local lookup, emitted parameters/locals, and numeric adaptation. -/
theorem LoweredInternalDeclaration.localsAligned
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction) :
    LocalLayoutAligned row.context sourceFunction := by
  have bindingsEq : functionBindings sourceFunction = row.localKinds := by
    simpa [functionBindings, LoweredInternalDeclaration.localKinds] using
      congrArg functionBindings row.sourceFunctionEq
  unfold LocalLayoutAligned
  intro fvarId kind found
  have localFound :
      Fir.Wasm.findLocalKind? row.localKinds fvarId = some kind := by
    unfold Fir.Wasm.getLocal at found
    change (match Fir.Wasm.findLocalKind? row.localKinds fvarId with
      | some actual =>
          Except.ok (Fir.Wasm.Instruction.localGet fvarId, actual)
      | none =>
          Except.error (Fir.Wasm.CompileError.unknownVariable fvarId)) =
        Except.ok (Fir.Wasm.Instruction.localGet fvarId, kind) at found
    split at found <;> rename_i selected
    · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at found
      simpa [selected, found]
    · contradiction
  rw [bindingsEq]
  exact findFVar?_kind_of_findLocalKind? localFound

/-- Successful production `lowerDecl` exposes its exact declaration-local
context, symbolic body, ABI result row, and emitted source function. -/
theorem LoweredInternalDeclaration.exists_of_lowerDecl
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (bodyEq : declaration.value = .code sourceCode)
    (lowered :
      Fir.Wasm.lowerDecl program cachedDeclarations declaration =
        .ok (some sourceFunction)) :
    Nonempty (LoweredInternalDeclaration program cachedDeclarations declaration
      sourceCode sourceFunction) := by
  unfold Fir.Wasm.lowerDecl at lowered
  rw [bodyEq] at lowered
  cases paramsResult : Fir.Wasm.addDeclarationParams program declaration with
  | error error =>
      simp only [paramsResult, Bind.bind, Except.bind] at lowered
      contradiction
  | ok paramLocals =>
      simp only [paramsResult, Bind.bind, Except.bind] at lowered
      cases localsResult :
          Fir.Wasm.collectLocals [] sourceCode with
      | error error =>
          simp only [localsResult] at lowered
          contradiction
      | ok bodyLocals =>
          simp only [localsResult] at lowered
          cases bodyResult :
              Fir.Wasm.compileCode {
                program
                localKinds := paramLocals.reverse ++ bodyLocals.reverse
                cachedDeclarations } sourceCode with
          | error error =>
              simp only [bodyResult] at lowered
              contradiction
          | ok symbolicBody =>
              simp only [bodyResult] at lowered
              cases resultsResult :
                  Fir.Wasm.resultKinds declaration.type with
              | error error =>
                  simp only [resultsResult] at lowered
                  contradiction
              | ok abiResults =>
                  simp only [resultsResult, pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at lowered
                  exact ⟨{
                    paramLocals
                    bodyLocals
                    symbolicBody
                    abiResults
                    bodyEq
                    paramsAdded := paramsResult
                    localsCollected := localsResult
                    bodyCompiled := bodyResult
                    resultsCompiled := resultsResult
                    sourceFunctionEq := lowered.symm }⟩

/-- A lowering view replays to the exact executable `lowerDecl` result. -/
theorem LoweredInternalDeclaration.lowerDecl
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction) :
  Fir.Wasm.lowerDecl program cachedDeclarations declaration =
      .ok (some sourceFunction) := by
  unfold Fir.Wasm.lowerDecl
  simp only [row.bodyEq, row.paramsAdded, row.localsCollected,
    row.bodyCompiled, row.resultsCompiled, Bind.bind, Except.bind, pure,
    Except.pure, row.sourceFunctionEq]

/-- Production declaration lowering preserves the source declaration name. -/
theorem LoweredInternalDeclaration.sourceFunctionName
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction) :
    sourceFunction.name = declaration.name := by
  simpa using congrArg Fir.Wasm.Function.name row.sourceFunctionEq

/-- An internal source declaration cannot produce the `none` branch reserved
for external imports when `lowerDecl` succeeds. -/
theorem lowerDecl_some_of_code
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {result : Option Fir.Wasm.Function}
    (bodyEq : declaration.value = .code sourceCode)
    (lowered :
      Fir.Wasm.lowerDecl program cachedDeclarations declaration = .ok result) :
    ∃ sourceFunction, result = some sourceFunction := by
  cases result with
  | some sourceFunction => exact ⟨sourceFunction, rfl⟩
  | none =>
      unfold Fir.Wasm.lowerDecl at lowered
      rw [bodyEq] at lowered
      cases paramsResult : Fir.Wasm.addDeclarationParams program declaration with
      | error error =>
          simp only [paramsResult, Bind.bind, Except.bind] at lowered
          contradiction
      | ok paramLocals =>
          simp only [paramsResult, Bind.bind, Except.bind] at lowered
          cases localsResult :
              Fir.Wasm.collectLocals [] sourceCode with
          | error error => simp [localsResult] at lowered
          | ok bodyLocals =>
              simp only [localsResult] at lowered
              cases bodyResult :
                  Fir.Wasm.compileCode {
                    program
                    localKinds := paramLocals.reverse ++ bodyLocals.reverse
                    cachedDeclarations } sourceCode with
              | error error => simp [bodyResult] at lowered
              | ok symbolicBody =>
                  simp only [bodyResult] at lowered
                  cases resultsResult :
                      Fir.Wasm.resultKinds declaration.type with
                  | error error => simp [resultsResult] at lowered
                  | ok abiResults =>
                      simp [resultsResult, pure, Except.pure] at lowered

/-- Successful whole-module lowering exposes the exact production
`filterMapM lowerDecl` result used as the symbolic function table. -/
theorem LoweredInternalDeclaration.functions_of_lower
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source) :
    program.decls.filterMapM
        (Fir.Wasm.lowerDecl program
          (Fir.Wasm.cachedDeclarationNames program)) =
      .ok source.functions := by
  unfold Fir.Wasm.lower at lowered
  dsimp only at lowered
  generalize functionsEq :
      program.decls.filterMapM
          (Fir.Wasm.lowerDecl program
            (Fir.Wasm.cachedDeclarationNames program)) =
        functionsResult at lowered
  cases functionsResult with
  | error error => contradiction
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
        | error error => contradiction
        | ok externals =>
            simp only [pure, Except.pure, Except.ok.injEq] at lowered
            subst source
            simpa using functionsEq
      · simp [operations] at lowered

/--
The production-strengthened declaration package.

`ConcreteSupportedDeclaration` contains exactly the static facts consumed by
the dynamic body theorem.  This companion additionally records that the
symbolic and concrete functions occupy the same row of the actual
`lower`/`adapt` pipeline.  In particular, its unified target index is computed
from the symbolic import prefix and source-function row; it cannot be paired
with an unrelated adapted function.
-/
structure ConcreteGeneratedDeclaration
    (context : Fir.Wasm.Context)
    (sourceCode : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule)
    extends ConcreteSupportedDeclaration context sourceCode sourceModule
      sourceFunction target where
  sourceFunctionIndex : Nat
  sourceFunctionFound :
    sourceModule.functions[sourceFunctionIndex]? = some sourceFunction
  targetFunctionIndex_eq :
    targetFunctionIndex = sourceModule.imports.size + sourceFunctionIndex
  functionAdapted :
    FirTalos.function sourceModule sourceFunction = .ok targetFunction

/--
Production-generated declaration evidence with its exact parameter row.

`ConcreteGeneratedDeclaration` is sufficient for proving a body once its
entry frame is related. Recursive calls additionally have to construct that
entry frame from semantic arguments and physical Wasm operands. These fields
retain the parameter row computed by the real `addDeclarationParams` call and
identify it with the emitted symbolic function parameters; they contain no
dynamic source or target execution.
-/
structure ConcreteGeneratedInternalDeclaration
    (program : Fir.LeanIR.ImpureProgram)
    (declaration : LCNF.Decl .impure)
    (context : Fir.Wasm.Context)
    (sourceCode : LCNF.Code .impure)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (target : AdaptedModule)
    extends ConcreteGeneratedDeclaration context sourceCode sourceModule
      sourceFunction target where
  contextProgram : context.program = program
  contextCaches :
    context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program
  parameterLocals : Fir.Wasm.LocalKinds
  parameterIdsUnique :
    Fir.Wasm.declarationParameterIdsUnique declaration = true
  parametersAdded :
    Fir.Wasm.addDeclarationParams program declaration = .ok parameterLocals
  sourceParameters :
    sourceFunction.params = parameterLocals.reverse.toArray
  callIndexEq :
    callIndex? sourceModule (.declaration declaration.name) =
      some targetFunctionIndex

/-- Every internal declaration selected from the production pipeline inherits
the module-wide compiler, adapter, resolver, and host-alignment facts from a
supported root export.  Its function-specific facts come from the exact
generated row, so this construction requires no export-table membership for
the internal declaration. -/
def ConcreteGeneratedInternalDeclaration.toSupportedFunction
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext context : Fir.Wasm.Context}
    {rootCode sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    {declaration : LCNF.Decl .impure}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target) :
    ConcreteSupportedFunction program context sourceCode sourceModule
      sourceFunction target hosts := {
  programSupported := spec.programSupported
  programNamesUnique := spec.programNamesUnique
  contextProgram := row.contextProgram
  lowered := spec.lowered
  sourceFunctionIndex := row.sourceFunctionIndex
  sourceFunctionFound := row.sourceFunctionFound
  localsAligned := row.localsAligned
  adapted := spec.adapted
  hostsResolved := spec.hostsResolved
  hostsAligned := spec.hostsAligned
  runtimeCallsAligned := spec.runtimeCallsAligned
  externalCallsAligned := spec.externalCallsAligned
  targetFunctionIndex := row.targetFunctionIndex
  targetFunction := row.targetFunction
  notImport := row.notImport
  targetFunctionFound := row.targetFunctionFound
  bodyAdapted := row.bodyAdapted
  singleResult := row.singleResult }

/-- The validator's count-based parameter check gives the proof-facing
`Nodup` fact for the source parameter names. -/
private theorem declarationParameterNamesNodup
    {declaration : LCNF.Decl .impure}
    (unique : Fir.Wasm.declarationParameterIdsUnique declaration = true) :
    (declaration.params.toList.map (·.fvarId.name)).Nodup := by
  unfold Fir.Wasm.declarationParameterIdsUnique at unique
  rw [List.nodup_iff_count_eq_one]
  intro name nameMem
  obtain ⟨param, paramMem, rfl⟩ := List.mem_map.mp nameMem
  have idMem : param.fvarId ∈
      declaration.params.toList.map (·.fvarId) :=
    List.mem_map.mpr ⟨param, paramMem, rfl⟩
  have one := (List.all_eq_true.mp unique) param.fvarId idMem
  have oneEq :
      (declaration.params.toList.map (·.fvarId) |>.filter
        (Fir.Wasm.sameFVar param.fvarId)).length = 1 :=
    beq_iff_eq.mp one
  rw [List.count_eq_length_filter]
  rw [List.filter_map] at oneEq
  rw [List.filter_map]
  simpa [Fir.Wasm.sameFVar, Function.comp_def, BEq.comm] using oneEq

/-- One proof-transparent step of production declaration-parameter lowering. -/
private def declarationParamStep
    (program : Fir.LeanIR.ImpureProgram) (declaration : LCNF.Decl .impure)
    (locals : Fir.Wasm.LocalKinds) (param : LCNF.Param .impure) :
    Except Fir.Wasm.CompileError Fir.Wasm.LocalKinds := do
  match ← Fir.Wasm.checkedAbiKind? param.type with
  | none => return locals
  | some kind =>
      let kind :=
        if kind == .tobject &&
            Fir.Wasm.erasedOnlyParameter program declaration param then
          .erased
        else
          kind
      return Fir.Wasm.insertLocal locals param.fvarId kind

/-- The pure parameter-kind classifier and the executable lowerer select the
same effective lane for one admitted declaration parameter. -/
private theorem declarationParamStep_eq
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {locals : Fir.Wasm.LocalKinds} {param : LCNF.Param .impure}
    {kind : AbiKind}
    (known :
      Fir.Wasm.declarationParamKind? program declaration param = some kind) :
    declarationParamStep program declaration locals param =
      .ok (Fir.Wasm.insertLocal locals param.fvarId kind) := by
  unfold declarationParamStep
  unfold Fir.Wasm.checkedAbiKind?
  unfold Fir.Wasm.declarationParamKind? at known
  cases kindResult : Fir.Wasm.abiKind? param.type with
  | error error => simp_all
  | ok kindOption =>
      cases kindOption with
      | none => simp_all
      | some declaredKind =>
          rw [kindResult] at known
          simp only at known
          simp only [pure, Except.pure, Bind.bind, Except.bind]
          by_cases erased :
              (declaredKind == .tobject &&
                Fir.Wasm.erasedOnlyParameter program declaration param) = true
          · simp [erased] at known ⊢
            exact congrArg (Fir.Wasm.insertLocal locals param.fvarId) known
          · simp [erased] at known ⊢
            exact congrArg (Fir.Wasm.insertLocal locals param.fvarId) known

/-- With fresh source parameter names, front-insertion followed by reversal is
exactly the source-order `(identifier, effective ABI kind)` row. -/
private theorem declarationParamFold_exact
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {params : List (LCNF.Param .impure)} {kinds : List AbiKind}
    {locals : Fir.Wasm.LocalKinds}
    (namesNodup : (params.map (·.fvarId.name)).Nodup)
    (fresh : ∀ param ∈ params, ∀ entry ∈ locals,
      entry.fst.name ≠ param.fvarId.name)
    (known :
      params.mapM (Fir.Wasm.declarationParamKind? program declaration) =
        some kinds) :
    params.foldlM (declarationParamStep program declaration) locals =
      .ok (((params.zip kinds).map
        (fun pair => (pair.fst.fvarId, pair.snd))).reverse ++ locals) := by
  induction params generalizing kinds locals with
  | nil =>
      have kindsEq : kinds = [] := by simpa using known.symm
      subst kinds
      simp [pure, Except.pure]
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at namesNodup
      rcases namesNodup with ⟨headFresh, tailNodup⟩
      cases headKnown :
          Fir.Wasm.declarationParamKind? program declaration head with
      | none => simp [List.mapM_cons, headKnown] at known
      | some headKind =>
          cases tailKnown :
              tail.mapM
                (Fir.Wasm.declarationParamKind? program declaration) with
          | none =>
              simp [List.mapM_cons, headKnown, tailKnown] at known
          | some tailKinds =>
              have kindsEq : kinds = headKind :: tailKinds := by
                simpa [List.mapM_cons, headKnown, tailKnown] using known.symm
              subst kinds
              have filterEq :
                  locals.filter
                      (fun entry => entry.fst.name != head.fvarId.name) =
                    locals := by
                apply List.filter_eq_self.mpr
                intro entry entryMem
                exact bne_iff_ne.mpr
                  (fresh head (by simp) entry entryMem)
              have insertEq :
                  Fir.Wasm.insertLocal locals head.fvarId headKind =
                    (head.fvarId, headKind) :: locals := by
                simp [Fir.Wasm.insertLocal, filterEq]
              have tailFresh : ∀ param ∈ tail,
                  ∀ entry ∈ (head.fvarId, headKind) :: locals,
                    entry.fst.name ≠ param.fvarId.name := by
                intro param paramMem entry entryMem
                rcases List.mem_cons.mp entryMem with entryEq | entryMem
                · subst entry
                  intro namesEq
                  apply headFresh
                  exact List.mem_map.mpr ⟨param, paramMem, namesEq.symm⟩
                · exact fresh param (by simp [paramMem]) entry entryMem
              have tailRun :=
                ih tailNodup tailFresh tailKnown
              rw [List.foldlM_cons, declarationParamStep_eq headKnown]
              simp only [Bind.bind, Except.bind]
              rw [insertEq, tailRun]
              simp [List.reverse_cons, List.append_assoc]

/-- The emitted symbolic parameter row is exactly the source declaration row
paired, in source order, with the validator's effective ABI kinds. -/
theorem ConcreteGeneratedInternalDeclaration.sourceParameterBindings
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {parameterKinds : Array AbiKind}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target)
    (known :
      Fir.Wasm.declarationParameterKinds? program declaration =
        some parameterKinds) :
    sourceFunction.params.toList =
      (declaration.params.toList.zip parameterKinds.toList).map
        (fun pair => (pair.fst.fvarId, pair.snd)) := by
  have namesNodup := declarationParameterNamesNodup row.parameterIdsUnique
  unfold Fir.Wasm.declarationParameterKinds? at known
  rw [Array.mapM_eq_mapM_toList] at known
  cases listKnown :
      declaration.params.toList.mapM
        (Fir.Wasm.declarationParamKind? program declaration) with
  | none => simp [listKnown] at known
  | some listKinds =>
      have parameterKindsEq : parameterKinds = listKinds.toArray := by
        simpa [listKnown] using known.symm
      subst parameterKinds
      have folded := declarationParamFold_exact
        (program := program) (declaration := declaration)
        (params := declaration.params.toList) (kinds := listKinds)
        (locals := []) namesNodup (by simp) listKnown
      have parametersAdded := row.parametersAdded
      unfold Fir.Wasm.addDeclarationParams at parametersAdded
      change declaration.params.foldlM
          (declarationParamStep program declaration) [] =
        .ok row.parameterLocals at parametersAdded
      rw [← Array.foldlM_toList] at parametersAdded
      rw [folded] at parametersAdded
      have localsEq :
          row.parameterLocals =
            ((declaration.params.toList.zip listKinds).map
              (fun pair => (pair.fst.fvarId, pair.snd))).reverse := by
        simpa using (Except.ok.inj parametersAdded).symm
      have sourceParameters := congrArg Array.toList row.sourceParameters
      simpa [localsEq] using sourceParameters

/-- Successful production parameter classification preserves declaration
arity. -/
theorem ConcreteGeneratedInternalDeclaration.parameterKindsSize
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {parameterKinds : Array AbiKind}
    (_row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target)
    (known :
      Fir.Wasm.declarationParameterKinds? program declaration =
        some parameterKinds) :
    parameterKinds.size = declaration.params.size := by
  unfold Fir.Wasm.declarationParameterKinds? at known
  rw [Array.mapM_eq_mapM_toList] at known
  cases listKnown :
      declaration.params.toList.mapM
        (Fir.Wasm.declarationParamKind? program declaration) with
  | none => simp [listKnown] at known
  | some listKinds =>
      have parameterKindsEq : parameterKinds = listKinds.toArray := by
        simpa [listKnown] using known.symm
      subst parameterKinds
      simpa using optionListMapM_length listKnown

/-- Generated symbolic parameter bindings inherit the source declaration's
name uniqueness. -/
theorem ConcreteGeneratedInternalDeclaration.sourceParameterNamesNodup
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {parameterKinds : Array AbiKind}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target)
    (known :
      Fir.Wasm.declarationParameterKinds? program declaration =
        some parameterKinds) :
    (sourceFunction.params.toList.map (·.fst.name)).Nodup := by
  rw [row.sourceParameterBindings known]
  have sizes := row.parameterKindsSize known
  have lengthLe : declaration.params.toList.length ≤
      parameterKinds.toList.length := by
    simpa using sizes.symm.le
  have parameterNames :
      ((declaration.params.toList.zip parameterKinds.toList).map
          (fun pair => (pair.fst.fvarId, pair.snd))).map (·.fst.name) =
        declaration.params.toList.map (·.fvarId.name) := by
    simpa [List.map_map, Function.comp_def] using congrArg
      (List.map (fun param : LCNF.Param .impure => param.fvarId.name))
      (List.map_fst_zip lengthLe)
  rw [parameterNames]
  exact declarationParameterNamesNodup row.parameterIdsUnique

/-- A successful semantic lookup names a binding present in the environment,
with the same free-variable name. -/
private theorem lookup_eq_some_mem
    {sourceEnv : Env} {fvar : FVarId} {value : Value}
    (found : lookup sourceEnv fvar = some value) :
    ∃ bound,
      (bound, value) ∈ sourceEnv ∧ bound.name = fvar.name := by
  induction sourceEnv with
  | nil => simp [lookup] at found
  | cons binding rest ih =>
      obtain ⟨candidate, current⟩ := binding
      by_cases sameName : candidate.name == fvar.name
      · rw [lookup, if_pos sameName] at found
        have currentEq : current = value := Option.some.inj found
        subst current
        exact ⟨candidate, by simp, LawfulBEq.eq_of_beq sameName⟩
      · rw [lookup, if_neg sameName] at found
        obtain ⟨bound, member, names⟩ := ih found
        exact ⟨bound, by simp [member], names⟩

/-- Folding semantic parameter binding is just the reverse source-order row
prepended to the initial environment. -/
private theorem bindParamPairsFold_eq
    (pairs : List (LCNF.Param .impure × Value)) (initial : Env) :
    pairs.foldl
        (fun env pair => bind env pair.fst.fvarId pair.snd) initial =
      (pairs.map (fun pair => (pair.fst.fvarId, pair.snd))).reverse ++
        initial := by
  induction pairs generalizing initial with
  | nil => simp
  | cons pair rest ih =>
      simp [List.foldl_cons, ih, Fir.LeanIR.Impure.bind, List.reverse_cons,
        List.append_assoc]

/-- In a unique-name prefix, a binding found at an exact list position is the
one selected by name-directed symbolic lookup, even after body locals are
appended. -/
private theorem findFVar?_append_eq_some_of_getElem?
    {α : Type} {bindings suffix : List (FVarId × α)}
    {fvar candidate : FVarId} {kind : α} {index : Nat}
    (namesNodup : (bindings.map (·.fst.name)).Nodup)
    (bindingFound : bindings[index]? = some (candidate, kind))
    (names : candidate.name = fvar.name) :
    findFVar? (bindings ++ suffix) fvar = some index := by
  induction bindings generalizing index with
  | nil => simp at bindingFound
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at namesNodup
      rcases namesNodup with ⟨headFresh, tailNodup⟩
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at bindingFound
          have headNames : head.fst.name = fvar.name := by
            rw [bindingFound]
            exact names
          have sameName : (head.fst.name == fvar.name) = true :=
            beq_iff_eq.mpr headNames
          simp [findFVar?, sameName]
      | succ index =>
          simp only [List.getElem?_cons_succ] at bindingFound
          have candidateMem : candidate.name ∈ tail.map (·.fst.name) := by
            have bindingMem : (candidate, kind) ∈ tail :=
              List.mem_iff_getElem?.mpr ⟨index, bindingFound⟩
            exact List.mem_map.mpr ⟨(candidate, kind), bindingMem, rfl⟩
          have headNames : head.fst.name ≠ fvar.name := by
            intro sameName
            apply headFresh
            rw [sameName, ← names]
            exact candidateMem
          have different : (head.fst.name == fvar.name) = false :=
            beq_eq_false_iff_ne.mpr headNames
          have tailFound := ih tailNodup bindingFound
          simp [findFVar?, different, tailFound]

/-- Exact generated callee-entry local relation for a saturated direct call.
The theorem composes production parameter classification/lowering, semantic
`bindParams`, and the already-related physical argument row. -/
theorem ConcreteGeneratedInternalDeclaration.entryEnvLocalsRelated
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure} {callerEnv : Env}
    {sourceModule : Fir.Wasm.Module}
    {calleeFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.parameterKinds.toList
        physicalArgs site.semanticArgs.toList) :
    EnvLocalsRelated witness (functionBindings calleeFunction) site.calleeEnv
      (row.targetFunction.toLocals physicalArgs) := by
  have arityEq :
      site.sourceDeclaration.params.size = site.semanticArgs.size := by
    by_contra different
    have sizeTest :
        (site.sourceDeclaration.params.size == site.semanticArgs.size) =
          false := beq_eq_false_iff_ne.mpr different
    have parametersBound := site.parametersBound
    unfold bindParams at parametersBound
    simp [sizeTest] at parametersBound
  have parameterBindings := row.sourceParameterBindings site.parametersKnown
  have parameterNamesNodup :=
    row.sourceParameterNamesNodup site.parametersKnown
  have calleeEnvEq :
      site.calleeEnv =
        ((site.sourceDeclaration.params.toList.zip
          site.semanticArgs.toList).map
            (fun pair => (pair.fst.fvarId, pair.snd))).reverse := by
    have parametersBound := site.parametersBound
    unfold bindParams at parametersBound
    have sizeTest :
        (site.sourceDeclaration.params.size == site.semanticArgs.size) =
          true := beq_iff_eq.mpr arityEq
    simp only [sizeTest, ↓reduceIte] at parametersBound
    rw [bindParamPairsFold_eq] at parametersBound
    simpa using (Except.ok.inj parametersBound).symm
  intro fvar value sourceLookup
  rw [calleeEnvEq] at sourceLookup
  obtain ⟨candidate, candidateMember, candidateNames⟩ :=
    lookup_eq_some_mem sourceLookup
  have sourceRowMember :
      (candidate, value) ∈
        (site.sourceDeclaration.params.toList.zip
          site.semanticArgs.toList).map
            (fun pair => (pair.fst.fvarId, pair.snd)) := by
    simpa using candidateMember
  obtain ⟨index, rowBound, sourceRowAt⟩ :=
    List.mem_iff_getElem.mp sourceRowMember
  have zippedBound : index <
      (site.sourceDeclaration.params.toList.zip
        site.semanticArgs.toList).length := by
    simpa using rowBound
  have parameterBound : index < site.sourceDeclaration.params.toList.length := by
    simp only [List.length_zip] at zippedBound
    omega
  have semanticBound : index < site.semanticArgs.toList.length := by
    simp only [List.length_zip] at zippedBound
    omega
  rw [List.getElem_map, List.getElem_zip] at sourceRowAt
  have candidateAt :
      site.sourceDeclaration.params.toList[index].fvarId = candidate :=
    congrArg Prod.fst sourceRowAt
  have semanticAt : site.semanticArgs.toList[index] = value :=
    congrArg Prod.snd sourceRowAt
  have semanticFound : site.semanticArgs.toList[index]? = some value := by
    rw [List.getElem?_eq_getElem semanticBound, semanticAt]
  obtain ⟨kind, physical, kindFound, physicalFound, valueRelated⟩ :=
    argumentsRelated.resolveAt semanticFound
  obtain ⟨kindBound, kindAt⟩ := List.getElem?_eq_some_iff.mp kindFound
  have parameterRowBound : index < calleeFunction.params.toList.length := by
    rw [parameterBindings]
    simp only [List.length_map, List.length_zip]
    omega
  have expectedParameterRowAt :
      ((site.sourceDeclaration.params.toList.zip
        site.parameterKinds.toList).map
          (fun pair => (pair.fst.fvarId, pair.snd)))[index]? =
        some (candidate, kind) := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨?_, ?_⟩
    · simp only [List.length_map, List.length_zip]
      omega
    · rw [List.getElem_map, List.getElem_zip, candidateAt, kindAt]
  have parameterRowAt :
      calleeFunction.params.toList[index]? = some (candidate, kind) := by
    rw [parameterBindings]
    exact expectedParameterRowAt
  have localFound :
      findFVar? (functionBindings calleeFunction) fvar = some index := by
    unfold functionBindings
    exact findFVar?_append_eq_some_of_getElem? parameterNamesNodup
      parameterRowAt candidateNames
  have kindAtBinding :
      (functionBindings calleeFunction)[index]?.map Prod.snd = some kind := by
    unfold functionBindings
    rw [List.getElem?_append_left parameterRowBound, parameterRowAt]
    rfl
  obtain ⟨physicalBound, _physicalAt⟩ :=
    List.getElem?_eq_some_iff.mp physicalFound
  have physicalAt :
      (row.targetFunction.toLocals physicalArgs).get index = some physical := by
    simp only [Wasm.Function.toLocals, Wasm.Locals.get]
    rw [if_pos physicalBound]
    exact physicalFound
  exact ⟨index, kind, physical, localFound, kindAtBinding, physicalAt,
    valueRelated⟩

/-- Direct-call corollary: the caller's actual argument ABI is first
transported through the validator's refinement decision, then used to build
the exact generated callee-entry local relation. -/
theorem ConcreteGeneratedInternalDeclaration.entryEnvLocalsRelatedOfArguments
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure} {callerEnv : Env}
    {sourceModule : Fir.Wasm.Module}
    {calleeFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    EnvLocalsRelated witness (functionBindings calleeFunction) site.calleeEnv
      (row.targetFunction.toLocals physicalArgs) :=
  row.entryEnvLocalsRelated site
    (argumentsRelated.ofKindsRefine site.argumentsRefine)

/-- Re-index an unchanged valid caller store as the generated direct callee's
canonical entry frame. Reuse facts and their ordinary-token obligations start
empty; runtime, failure, budget, external-handler, cache, and closure-table
invariants are inherited unchanged. -/
theorem ConcreteReuseCapacityCacheFrame.generatedDirectCalleeEntry
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {callerEnv : Env} {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule} {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals} {witness : RefinementWitness}
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes sourceRuntime callerEnv targetStore callerLocals
        witness)
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals []
      remainingBytes sourceRuntime site.calleeEnv targetStore
      (row.targetFunction.toLocals physicalArgs) witness := by
  rcases callerFrame with
    ⟨⟨⟨⟨callerRelated, _callerOrdinary, _callerAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩, cacheTable, closureTables⟩
  have entryLocals :
      EnvLocalsRelated witness (functionBindings calleeFunction)
        site.calleeEnv (row.targetFunction.toLocals physicalArgs) :=
    row.entryEnvLocalsRelatedOfArguments site argumentsRelated
  have entryState :
      StateRelated calleeFunction sourceRuntime site.calleeEnv targetStore
        (row.targetFunction.toLocals physicalArgs) witness :=
    ⟨callerRelated.1.1, callerRelated.1.2.1, entryLocals⟩
  have emptyFacts :
      ReuseCapacityFactsRel [] (functionBindings calleeFunction)
        site.calleeEnv (row.targetFunction.toLocals physicalArgs)
        targetStore.host.runtime.heap witness := by
    intro fvarId evidence found
    simp [findReuseCapacityEvidence?] at found
  have entryRelated :
      ReuseCapacityStateRelated [] calleeFunction sourceRuntime site.calleeEnv
        targetStore (row.targetFunction.toLocals physicalArgs) witness :=
    ⟨entryState, emptyFacts⟩
  have emptyOrdinary :
      ReuseTokenOrdinaryRel [] sourceRuntime site.calleeEnv := by
    intro fvarId available location cell found
    simp [findReuseCapacityEvidence?] at found
  have classifiedSize := row.parameterKindsSize site.parametersKnown
  have parameterBindings := row.sourceParameterBindings site.parametersKnown
  have sourceParameterSize :
      calleeFunction.params.size = site.parameterKinds.size := by
    have lengths := congrArg List.length parameterBindings
    simp only [Array.length_toList, List.length_map, List.length_zip] at lengths
    rw [← classifiedSize] at lengths
    simpa using lengths
  have parameterRelated :=
    argumentsRelated.ofKindsRefine site.argumentsRefine
  have physicalSize : physicalArgs.length = site.parameterKinds.size := by
    simpa using parameterRelated.physicalLength
  have parameterFrameSize :
      (row.targetFunction.toLocals physicalArgs).params.length =
        calleeFunction.params.size := by
    simpa [Wasm.Function.toLocals] using
      physicalSize.trans sourceParameterSize.symm
  have signature :=
    FirTalos.Correctness.function_preserves_signature row.functionAdapted
  have localFrameSize :
      (row.targetFunction.toLocals physicalArgs).locals.length =
        calleeFunction.locals.size := by
    simp [Wasm.Function.toLocals, signature.2.1]
  have entryAligned :
      ConcreteLocalFrameAligned calleeFunction sourceRuntime site.calleeEnv
        targetStore (row.targetFunction.toLocals physicalArgs) witness :=
    ⟨parameterFrameSize, localFrameSize⟩
  exact
    ⟨⟨⟨⟨entryRelated, emptyOrdinary, entryAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩, cacheTable, closureTables⟩

/-- Re-index the generated callee entry at its exact source-selected cost.
The required weakening is justified by the budget-fit premise already checked
by the enclosing structural call theorem. -/
theorem ConcreteReuseCapacityCacheFrame.generatedDirectCalleeEntryAtCost
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {callerEnv : Env} {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule} {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes stepCost : Nat}
    {sourceRuntime : RuntimeState} {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals} {witness : RefinementWitness}
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes sourceRuntime callerEnv targetStore callerLocals
        witness)
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList)
    (stepFits : stepCost ≤ remainingBytes) :
    ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals []
      stepCost sourceRuntime site.calleeEnv targetStore
      (row.targetFunction.toLocals physicalArgs) witness :=
  (callerFrame.generatedDirectCalleeEntry site row argumentsRelated).withBudget
    (callerFrame.budget.weaken stepFits)

/-- Re-index an unchanged caller store as the entry frame of a generated
nullary initializer. The empty source environment makes the local-value
relation vacuous, while the production parameter row and adapted signature
show that `toLocals []` has the exact symbolic frame shape. -/
theorem ConcreteReuseCapacityCacheFrame.generatedNullaryCalleeEntryAtCost
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {calleeContext : Fir.Wasm.Context}
    {calleeCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {remainingBytes stepCost : Nat}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes sourceRuntime callerEnv targetStore callerLocals
        witness)
    (row : ConcreteGeneratedInternalDeclaration program declaration
      calleeContext calleeCode sourceModule calleeFunction target)
    (parametersEmpty : declaration.params = #[])
    (stepFits : stepCost ≤ remainingBytes) :
    ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals []
      stepCost sourceRuntime [] targetStore
      (row.targetFunction.toLocals []) witness := by
  rcases callerFrame with
    ⟨⟨⟨⟨callerRelated, _callerOrdinary, _callerAligned, budget⟩,
      integerImplementation, naturalImplementation, scalarImplementation⟩,
      descriptorAgreement⟩, cacheTable, closureTables⟩
  have parameterLocalsEmpty : row.parameterLocals = [] := by
    have parametersAdded := row.parametersAdded
    unfold Fir.Wasm.addDeclarationParams at parametersAdded
    rw [parametersEmpty] at parametersAdded
    simpa using (Except.ok.inj parametersAdded).symm
  have sourceParametersEmpty : calleeFunction.params = #[] := by
    simpa [parameterLocalsEmpty] using row.sourceParameters
  have entryState :
      StateRelated calleeFunction sourceRuntime [] targetStore
        (row.targetFunction.toLocals []) witness := by
    refine ⟨callerRelated.1.1, callerRelated.1.2.1, ?_⟩
    intro fvar value found
    simp [lookup] at found
  have emptyFacts :
      ReuseCapacityFactsRel [] (functionBindings calleeFunction) []
        (row.targetFunction.toLocals []) targetStore.host.runtime.heap witness := by
    intro fvarId evidence found
    simp [findReuseCapacityEvidence?] at found
  have emptyRelated :
      ReuseCapacityStateRelated [] calleeFunction sourceRuntime [] targetStore
        (row.targetFunction.toLocals []) witness :=
    ⟨entryState, emptyFacts⟩
  have emptyOrdinary : ReuseTokenOrdinaryRel [] sourceRuntime [] := by
    intro fvarId available location cell found
    simp [findReuseCapacityEvidence?] at found
  have signature :=
    FirTalos.Correctness.function_preserves_signature row.functionAdapted
  have entryAligned :
      ConcreteLocalFrameAligned calleeFunction sourceRuntime [] targetStore
        (row.targetFunction.toLocals []) witness := by
    constructor
    · simp [Wasm.Function.toLocals, sourceParametersEmpty]
    · simp [Wasm.Function.toLocals, signature.2.1]
  exact
    ⟨⟨⟨⟨emptyRelated, emptyOrdinary, entryAligned,
      budget.weaken stepFits⟩, integerImplementation, naturalImplementation,
      scalarImplementation⟩, descriptorAgreement⟩, cacheTable,
      closureTables⟩

/-- A generated nullary initializer accepts the empty physical parameter row. -/
theorem ConcreteGeneratedInternalDeclaration.targetParameterCount_nullary
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      sourceCode sourceModule sourceFunction target)
    (parametersEmpty : declaration.params = #[]) :
    ([] : List Wasm.Value).length = row.targetFunction.numParams := by
  have parameterLocalsEmpty : row.parameterLocals = [] := by
    have parametersAdded := row.parametersAdded
    unfold Fir.Wasm.addDeclarationParams at parametersAdded
    rw [parametersEmpty] at parametersAdded
    simpa using (Except.ok.inj parametersAdded).symm
  have sourceParametersEmpty : sourceFunction.params = #[] := by
    simpa [parameterLocalsEmpty] using row.sourceParameters
  have signature :=
    FirTalos.Correctness.function_preserves_signature row.functionAdapted
  simp [Wasm.Function.numParams, signature.1, sourceParametersEmpty]

/-- The physical argument row selected by production compilation has exactly
the adapted callee arity, in the stack order expected by Wasm function calls. -/
theorem ConcreteGeneratedInternalDeclaration.targetParameterCount
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure} {callerEnv : Env}
    {sourceModule : Fir.Wasm.Module}
    {calleeFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {witness : RefinementWitness} {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    physicalArgs.reverse.length = row.targetFunction.numParams := by
  have parameterBindings := row.sourceParameterBindings site.parametersKnown
  have classifiedSize := row.parameterKindsSize site.parametersKnown
  have sourceParameterSize :
      calleeFunction.params.size = site.parameterKinds.size := by
    have lengths := congrArg List.length parameterBindings
    simp only [Array.length_toList, List.length_map, List.length_zip] at lengths
    rw [← classifiedSize] at lengths
    simpa using lengths
  have physicalSize : physicalArgs.length = site.parameterKinds.size := by
    simpa using
      (argumentsRelated.ofKindsRefine site.argumentsRefine).physicalLength
  have signature :=
    FirTalos.Correctness.function_preserves_signature row.functionAdapted
  simp [Wasm.Function.numParams, signature.1, physicalSize,
    sourceParameterSize]

/-- Pointwise inversion of a successful `Except`-valued array traversal. -/
private theorem exceptArrayForM_ok_of_mem
    {α ε : Type} {f : α → Except ε Unit} {xs : Array α} {x : α}
    (run : xs.forM f = .ok ()) (member : x ∈ xs) :
    f x = .ok () := by
  have listRun :
      xs.toList.foldlM (fun _ item => f item) () = .ok () := by
    simpa [Array.forM] using run
  have listMember : x ∈ xs.toList := by simpa using member
  have go : ∀ (list : List α),
      list.foldlM (fun _ item => f item) () = .ok () →
        x ∈ list → f x = .ok () := by
    intro list
    induction list with
    | nil => simp
    | cons head tail ih =>
        intro tailRun itemMember
        simp only [List.mem_cons] at itemMember
        simp only [List.foldlM_cons] at tailRun
        cases headRun : f head with
        | error error =>
            simp only [headRun, Bind.bind, Except.bind] at tailRun
            contradiction
        | ok unit =>
            have unitEq : unit = () := Subsingleton.elim _ _
            subst unit
            simp only [headRun, Bind.bind, Except.bind] at tailRun
            rcases itemMember with rfl | itemMember
            · exact headRun
            · exact ih tailRun itemMember
  exact go xs.toList listRun listMember

/-- Supported lowering validates the exact declaration selected from the
program, so its parameter identifiers satisfy the shared single-scope
uniqueness contract. -/
private theorem declarationParameterIdsUnique_of_lowerSupported
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    (lowered : Fir.Wasm.lowerSupported program = .ok source)
    (declarationFound :
      program.findDecl? declarationName = some declaration) :
    Fir.Wasm.declarationParameterIdsUnique declaration = true := by
  have validated : Fir.Wasm.validateSupported program = .ok () := by
    unfold Fir.Wasm.lowerSupported at lowered
    cases validationEq : Fir.Wasm.validateSupported program with
    | error error =>
        simp only [validationEq, Bind.bind, Except.bind] at lowered
        contradiction
    | ok unit =>
        have unitEq : unit = () := Subsingleton.elim _ _
        simpa [validationEq, unitEq]
  have declarationMember : declaration ∈ program.decls := by
    obtain ⟨_, index, inBounds, selected, _⟩ :=
      Array.find?_eq_some_iff_getElem.mp declarationFound
    rw [← selected]
    exact Array.getElem_mem inBounds
  have declarationValidated :
      Fir.Wasm.validateSupportedDecl program declaration = .ok () := by
    unfold Fir.Wasm.validateSupported at validated
    exact exceptArrayForM_ok_of_mem validated declarationMember
  have supported : Fir.Wasm.supportedDecl program declaration = true := by
    by_contra notSupported
    have supportedFalse :
        Fir.Wasm.supportedDecl program declaration = false :=
      Bool.eq_false_iff.mpr notSupported
    cases valueEq : declaration.value <;>
      simp [Fir.Wasm.validateSupportedDecl, valueEq, supportedFalse]
        at declarationValidated
  unfold Fir.Wasm.supportedDecl at supported
  simp only [Bool.and_eq_true] at supported
  exact supported.1.1

/-- Pointwise inversion of successful `Except`-valued list traversal. -/
private theorem exceptListMapM_getElem?_eq_some
    {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    {index : Nat} {x : α}
    (mapped : xs.mapM f = .ok ys)
    (found : xs[index]? = some x) :
    ∃ y, f x = .ok y ∧ ys[index]? = some y := by
  induction xs generalizing ys index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero] at found
          have xEq : x = head := (Option.some.inj found).symm
          subst x
          cases headResult : f head with
          | error error =>
              simp only [List.mapM_cons, headResult, Bind.bind, Except.bind]
                at mapped
              contradiction
          | ok y =>
              cases tailResult : tail.mapM f with
              | error error =>
                  simp only [List.mapM_cons, headResult, Bind.bind, Except.bind,
                    tailResult] at mapped
                  contradiction
              | ok mappedTail =>
                  simp only [List.mapM_cons, headResult, Bind.bind, Except.bind,
                    tailResult, pure, Except.pure, Except.ok.injEq] at mapped
                  subst ys
                  exact ⟨y, by simpa using headResult, rfl⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          cases headResult : f head with
          | error error =>
              simp only [List.mapM_cons, headResult, Bind.bind, Except.bind]
                at mapped
              contradiction
          | ok y =>
              cases tailResult : tail.mapM f with
              | error error =>
                  simp only [List.mapM_cons, headResult, Bind.bind, Except.bind,
                    tailResult] at mapped
                  contradiction
              | ok mappedTail =>
                  simp only [List.mapM_cons, headResult, Bind.bind, Except.bind,
                    tailResult, pure, Except.pure, Except.ok.injEq] at mapped
                  subst ys
                  obtain ⟨result, resultFound, resultAt⟩ :=
                    ih tailResult found
                  exact ⟨result, resultFound, by simpa using resultAt⟩

/-- Every input visited by a successful `filterMapM` also returned
successfully, whether or not it contributed an output row. -/
private theorem exceptListFilterMapM_ok_of_mem
    {α β ε : Type} {f : α → Except ε (Option β)}
    {xs : List α} {ys : List β} {x : α}
    (mapped : xs.filterMapM f = .ok ys)
    (member : x ∈ xs) :
    ∃ result, f x = .ok result := by
  induction xs generalizing ys x with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      cases headResult : f head with
      | error error =>
          simp only [List.filterMapM_cons, headResult, Bind.bind, Except.bind]
            at mapped
          contradiction
      | ok headOption =>
          cases tailResult : tail.filterMapM f with
          | error error =>
              cases headOption <;>
                simp only [List.filterMapM_cons, headResult, Bind.bind,
                  Except.bind, tailResult] at mapped <;>
                contradiction
          | ok mappedTail =>
              rcases member with headEq | tailMember
              · subst x
                exact ⟨headOption, headResult⟩
              · exact ih tailResult tailMember

/-- A selected successful `filterMapM` row occurs in the successful output. -/
private theorem exceptListFilterMapM_mem_of_mem
    {α β ε : Type} {f : α → Except ε (Option β)}
    {xs : List α} {ys : List β} {x : α} {y : β}
    (mapped : xs.filterMapM f = .ok ys)
    (member : x ∈ xs)
    (selected : f x = .ok (some y)) :
    y ∈ ys := by
  induction xs generalizing ys x y with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      cases headResult : f head with
      | error error =>
          simp only [List.filterMapM_cons, headResult, Bind.bind, Except.bind]
            at mapped
          contradiction
      | ok headOption =>
          cases tailResult : tail.filterMapM f with
          | error error =>
              cases headOption <;>
                simp only [List.filterMapM_cons, headResult, Bind.bind,
                  Except.bind, tailResult] at mapped <;>
                contradiction
          | ok mappedTail =>
              cases headOption with
              | none =>
                  simp only [List.filterMapM_cons, headResult, Bind.bind,
                    Except.bind, tailResult, Except.ok.injEq] at mapped
                  subst ys
                  rcases member with headEq | tailMember
                  · subst x
                    rw [headResult] at selected
                    simp at selected
                  · exact ih tailResult tailMember selected
              | some headValue =>
                  simp only [List.filterMapM_cons, headResult, Bind.bind,
                    Except.bind, tailResult, pure, Except.pure,
                    Except.ok.injEq] at mapped
                  subst ys
                  rcases member with headEq | tailMember
                  · subst x
                    rw [headResult] at selected
                    simp only [Except.ok.injEq, Option.some.injEq] at selected
                    subst y
                    simp
                  · exact List.mem_cons_of_mem headValue
                      (ih tailResult tailMember selected)

/-- Every row emitted by a successful `filterMapM` comes from an exact input
row selected by the executable traversal. -/
private theorem exceptListFilterMapM_source_of_mem
    {α β ε : Type} {f : α → Except ε (Option β)}
    {xs : List α} {ys : List β} {y : β}
    (mapped : xs.filterMapM f = .ok ys)
    (member : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok (some y) := by
  induction xs generalizing ys y with
  | nil =>
      simp only [List.filterMapM_nil, pure, Except.pure,
        Except.ok.injEq] at mapped
      subst ys
      simp at member
  | cons head tail ih =>
      cases headResult : f head with
      | error error =>
          simp only [List.filterMapM_cons, headResult, Bind.bind,
            Except.bind] at mapped
          contradiction
      | ok headOption =>
          cases tailResult : tail.filterMapM f with
          | error error =>
              cases headOption <;>
                simp only [List.filterMapM_cons, headResult, Bind.bind,
                  Except.bind, tailResult] at mapped <;>
                contradiction
          | ok mappedTail =>
              cases headOption with
              | none =>
                  simp only [List.filterMapM_cons, headResult, Bind.bind,
                    Except.bind, tailResult, Except.ok.injEq] at mapped
                  subst ys
                  obtain ⟨x, xMem, selected⟩ := ih tailResult member
                  exact ⟨x, by simp [xMem], selected⟩
              | some headValue =>
                  simp only [List.filterMapM_cons, headResult, Bind.bind,
                    Except.bind, tailResult, pure, Except.pure,
                    Except.ok.injEq] at mapped
                  subst ys
                  rcases List.mem_cons.mp member with rfl | tailMember
                  · exact ⟨head, by simp, headResult⟩
                  · obtain ⟨x, xMem, selected⟩ := ih tailResult tailMember
                    exact ⟨x, by simp [xMem], selected⟩

/-- A successful `filterMapM` that preserves keys also preserves uniqueness of
those keys. -/
private theorem exceptListFilterMapM_map_nodup
    {α β ε κ : Type} [DecidableEq κ]
    {f : α → Except ε (Option β)} {inputKey : α → κ}
    {outputKey : β → κ} {xs : List α} {ys : List β}
    (mapped : xs.filterMapM f = .ok ys)
    (unique : (xs.map inputKey).Nodup)
    (keyPreserved : ∀ {x y}, f x = .ok (some y) →
      outputKey y = inputKey x) :
    (ys.map outputKey).Nodup := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.filterMapM_nil, pure, Except.pure,
        Except.ok.injEq] at mapped
      subst ys
      simp
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headFresh, tailUnique⟩
      cases headResult : f head with
      | error error =>
          simp only [List.filterMapM_cons, headResult, Bind.bind,
            Except.bind] at mapped
          contradiction
      | ok headOption =>
          cases tailResult : tail.filterMapM f with
          | error error =>
              cases headOption <;>
                simp only [List.filterMapM_cons, headResult, Bind.bind,
                  Except.bind, tailResult] at mapped <;>
                contradiction
          | ok mappedTail =>
              cases headOption with
              | none =>
                  simp only [List.filterMapM_cons, headResult, Bind.bind,
                    Except.bind, tailResult, Except.ok.injEq] at mapped
                  subst ys
                  exact ih tailResult tailUnique
              | some headValue =>
                  simp only [List.filterMapM_cons, headResult, Bind.bind,
                    Except.bind, tailResult, pure, Except.pure,
                    Except.ok.injEq] at mapped
                  subst ys
                  simp only [List.map_cons, List.nodup_cons]
                  refine ⟨?_, ih tailResult tailUnique⟩
                  intro outputMem
                  obtain ⟨tailValue, tailValueMem, outputEq⟩ :=
                    List.mem_map.mp outputMem
                  obtain ⟨tailInput, tailInputMem, tailSelected⟩ :=
                    exceptListFilterMapM_source_of_mem tailResult
                      tailValueMem
                  apply headFresh
                  apply List.mem_map.mpr
                  refine ⟨tailInput, tailInputMem, ?_⟩
                  rw [← keyPreserved headResult, ← keyPreserved tailSelected]
                  exact outputEq

/-- Name-unique source declarations lower to a name-unique symbolic function
table. This is a compiler-derived invariant of the real `filterMapM lowerDecl`
run, not an independent target certificate. -/
theorem LoweredInternalDeclaration.functionNamesNodup
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lower program = .ok source) :
    (source.functions.toList.map (·.name)).Nodup := by
  have mappedArray := LoweredInternalDeclaration.functions_of_lower lowered
  have mappedList :
      program.decls.toList.filterMapM
          (Fir.Wasm.lowerDecl program
            (Fir.Wasm.cachedDeclarationNames program)) =
        .ok source.functions.toList := by
    rw [← Array.toList_filterMapM]
    rw [mappedArray]
    rfl
  have sourceNamesUnique :
      (program.decls.toList.map (·.name)).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact namesUnique
  apply exceptListFilterMapM_map_nodup mappedList sourceNamesUnique
  intro declaration sourceFunction selected
  cases valueEq : declaration.value with
  | extern metadata =>
      simp [Fir.Wasm.lowerDecl, valueEq, pure, Except.pure] at selected
  | code sourceCode =>
      obtain ⟨row⟩ :=
        LoweredInternalDeclaration.exists_of_lowerDecl valueEq selected
      exact row.sourceFunctionName

/-- In a name-unique symbolic function table, an exact array row is also the
row selected by the adapter's executable name lookup. -/
private theorem functionFindIdx?_eq_some_of_namesNodup
    {functions : Array Fir.Wasm.Function}
    {index : Nat} {sourceFunction : Fir.Wasm.Function} {name : Name}
    (namesNodup : (functions.toList.map (·.name)).Nodup)
    (found : functions[index]? = some sourceFunction)
    (nameEq : sourceFunction.name = name) :
    functions.findIdx? (·.name == name) = some index := by
  obtain ⟨indexLt, functionAt⟩ := Array.getElem?_eq_some_iff.mp found
  apply Array.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨indexLt, ?_, ?_⟩
  · rw [functionAt, nameEq]
    simp
  · intro earlier earlierLt
    intro earlierMatches
    have earlierName : functions[earlier].name = name :=
      beq_iff_eq.mp earlierMatches
    have earlierArrayFound :
        functions[earlier]? = some functions[earlier] :=
      Array.getElem?_eq_getElem (Nat.lt_trans earlierLt indexLt)
    have indexListFound :
        (functions.toList.map (·.name))[index]? = some name := by
      rw [List.getElem?_map]
      have foundList : functions.toList[index]? = some sourceFunction := by
        simpa using found
      rw [foundList]
      simp [nameEq]
    have earlierListFound :
        (functions.toList.map (·.name))[earlier]? = some name := by
      rw [List.getElem?_map]
      have earlierList :
          functions.toList[earlier]? = some functions[earlier] := by
        simpa using earlierArrayFound
      rw [earlierList]
      simp [earlierName]
    have indicesEq : earlier = index := by
      apply (List.getElem?_inj
        (by simpa using Nat.lt_trans earlierLt indexLt) namesNodup).mp
      rw [earlierListFound, indexListFound]
    omega

/-- Top-level declaration-name uniqueness makes the source declaration table
injective on its members. -/
private theorem declaration_eq_of_namesUnique
    {declarations : List (LCNF.Decl .impure)}
    {left right : LCNF.Decl .impure}
    (unique :
      declarations.Pairwise fun left right => left.name ≠ right.name)
    (leftMem : left ∈ declarations)
    (rightMem : right ∈ declarations)
    (namesEq : left.name = right.name) :
    left = right := by
  induction declarations with
  | nil => simp at leftMem
  | cons head tail ih =>
      simp only [List.pairwise_cons] at unique
      rcases unique with ⟨headFresh, tailUnique⟩
      rcases List.mem_cons.mp leftMem with rfl | leftTail
      · rcases List.mem_cons.mp rightMem with rfl | rightTail
        · rfl
        · exact False.elim ((headFresh right rightTail) namesEq)
      · rcases List.mem_cons.mp rightMem with rfl | rightTail
        · exact False.elim ((headFresh left leftTail) namesEq.symm)
        · exact ih tailUnique leftTail rightTail

/-- Successful lowering exposes the exact runtime-import prefix and external
declaration traversal used to construct the symbolic import table. -/
theorem LoweredInternalDeclaration.imports_of_lower
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source) :
    ∃ externalImports,
      source.imports =
          (Fir.Wasm.collectRuntimeOps source.functions).mapIdx
              Fir.Wasm.runtimeImport ++ externalImports ∧
        (program.decls.filterMapM (fun declaration =>
            match declaration.value with
            | .extern _ => do
                match Fir.Wasm.externalImport declaration with
                | .ok import_ => return some import_
                | .error error =>
                    throw (Fir.Wasm.CompileError.abi error)
            | .code _ => pure none) :
          Except Fir.Wasm.CompileError (Array Fir.Wasm.Import)) =
            Except.ok externalImports := by
  unfold Fir.Wasm.lower at lowered
  dsimp only at lowered
  generalize functionsEq :
      program.decls.filterMapM
          (Fir.Wasm.lowerDecl program
            (Fir.Wasm.cachedDeclarationNames program)) =
        functionsResult at lowered
  cases functionsResult with
  | error error => contradiction
  | ok functions =>
      simp only [Bind.bind, Except.bind] at lowered
      by_cases operations :
          (Fir.Wasm.collectRuntimeOps functions).all
              Fir.Wasm.RuntimeOp.abiWellFormed = true
      · simp only [operations, ↓reduceIte] at lowered
        generalize externalEq :
            (program.decls.filterMapM (fun declaration =>
                match declaration.value with
                | .extern _ => do
                    match Fir.Wasm.externalImport declaration with
                    | .ok import_ => return some import_
                    | .error error =>
                        throw (Fir.Wasm.CompileError.abi error)
                | .code _ => pure none) :
              Except Fir.Wasm.CompileError (Array Fir.Wasm.Import)) =
                externalResult at lowered
        cases externalResult with
        | error error => contradiction
        | ok externalImports =>
            simp only [pure, Except.pure, Except.ok.injEq] at lowered
            subst source
            exact ⟨externalImports, rfl, rfl⟩
      · simp [operations] at lowered

/-- A successfully constructed external import retains its source declaration
name in the symbolic import key. -/
private theorem externalImport_declaration?
    {declaration : LCNF.Decl .impure} {import_ : Fir.Wasm.Import}
    (imported : Fir.Wasm.externalImport declaration = .ok import_) :
    import_.declaration? = some declaration.name := by
  unfold Fir.Wasm.externalImport at imported
  cases signatureResult :
      Fir.Wasm.ExternalTypes.signature {
        params := declaration.params.map (·.type)
        result := declaration.type } with
  | error error =>
      simp [signatureResult] at imported
  | ok signature =>
      simp only [signatureResult, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at imported
      subst import_
      rfl

/-- Successful source lookup fixes the selected declaration's name. -/
private theorem declarationName_of_findDecl?
    {program : Fir.LeanIR.ImpureProgram}
    {name : Name} {declaration : LCNF.Decl .impure}
    (found : program.findDecl? name = some declaration) :
    declaration.name = name := by
  have selected := (Array.find?_eq_some_iff_getElem.mp found).1
  simpa [Fir.LeanIR.Program.findDecl?] using selected

/-- A name-unique internal source declaration cannot be shadowed by the
runtime/external import prefix produced by the same lowering run. -/
theorem LoweredInternalDeclaration.findImportTarget?_eq_none
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lower program = .ok source)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (bodyEq : declaration.value = .code sourceCode) :
    findImportTarget? source (.declaration declarationName) = none := by
  obtain ⟨externalImports, importsEq, externalMappedArray⟩ :=
    LoweredInternalDeclaration.imports_of_lower lowered
  have externalMappedList :
      (program.decls.toList.filterMapM (fun sourceDeclaration =>
            match sourceDeclaration.value with
            | .extern _ => do
                match Fir.Wasm.externalImport sourceDeclaration with
                | .ok import_ => return some import_
                | .error error =>
                    throw (Fir.Wasm.CompileError.abi error)
            | .code _ => pure none) :
        Except Fir.Wasm.CompileError (List Fir.Wasm.Import)) =
          Except.ok externalImports.toList := by
    rw [← Array.toList_filterMapM]
    rw [externalMappedArray]
    rfl
  have declarationMember : declaration ∈ program.decls.toList := by
    obtain ⟨_, index, inBounds, selected, _⟩ :=
      Array.find?_eq_some_iff_getElem.mp declarationFound
    have member : declaration ∈ program.decls := by
      rw [← selected]
      exact Array.getElem_mem inBounds
    simpa using member
  have declarationNameEq : declaration.name = declarationName :=
    declarationName_of_findDecl? declarationFound
  cases importFound :
      findImportTarget? source (.declaration declarationName) with
  | none => rfl
  | some importIndex =>
      exfalso
      obtain ⟨importInBounds, importMatches, _⟩ :=
        Array.findIdx?_eq_some_iff_getElem.mp importFound
      let import_ := source.imports[importIndex]
      have importName : import_.declaration? = some declarationName :=
        beq_iff_eq.mp importMatches
      have importMember : import_ ∈ source.imports :=
        Array.getElem_mem importInBounds
      rw [importsEq] at importMember
      rcases Array.mem_append.mp importMember with
        runtimeMember | externalMember
      · obtain ⟨operationIndex, operationInBounds, runtimeEq⟩ :=
          Array.exists_of_mem_mapIdx runtimeMember
        have noDeclaration : import_.declaration? = none := by
          rw [← runtimeEq]
          rfl
        rw [noDeclaration] at importName
        contradiction
      · have externalMemberList : import_ ∈ externalImports.toList := by
          simpa using externalMember
        obtain ⟨externalDeclaration, externalDeclarationMember, selected⟩ :=
          exceptListFilterMapM_source_of_mem externalMappedList
            externalMemberList
        cases externalValue : externalDeclaration.value with
        | code externalCode =>
            simp [externalValue, pure, Except.pure] at selected
        | extern metadata =>
            cases importedEq :
                Fir.Wasm.externalImport externalDeclaration with
            | error error =>
                simp [externalValue, importedEq] at selected
            | ok externalImport =>
                simp only [externalValue, importedEq, pure, Except.pure,
                  Except.ok.injEq, Option.some.injEq] at selected
                subst externalImport
                have externalImportName :=
                  externalImport_declaration? importedEq
                have externalNameEq :
                    externalDeclaration.name = declarationName := by
                  rw [externalImportName] at importName
                  exact Option.some.inj importName
                have declarationsEq : externalDeclaration = declaration :=
                  declaration_eq_of_namesUnique namesUnique
                    externalDeclarationMember declarationMember
                    (externalNameEq.trans declarationNameEq.symm)
                subst externalDeclaration
                rw [bodyEq] at externalValue
                contradiction

/-- The numeric declaration-call target selected by the adapter is exactly
the concrete generated function row obtained from the same production
lowering/adaptation run. -/
theorem ConcreteGeneratedDeclaration.internalCallIndex
    {program rowProgram : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {context : Fir.Wasm.Context}
    {source : Fir.Wasm.Module}
    {target : AdaptedModule}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (generated : ConcreteGeneratedDeclaration context sourceCode source
      sourceFunction target)
    (row : LoweredInternalDeclaration rowProgram cachedDeclarations
      declaration sourceCode sourceFunction)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lower program = .ok source)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (bodyEq : declaration.value = .code sourceCode) :
    callIndex? source (.declaration declarationName) =
      some generated.targetFunctionIndex := by
  have noImport :=
    LoweredInternalDeclaration.findImportTarget?_eq_none namesUnique lowered
      declarationFound bodyEq
  have namesNodup :=
    LoweredInternalDeclaration.functionNamesNodup namesUnique lowered
  have sourceName : sourceFunction.name = declarationName :=
    row.sourceFunctionName.trans
      (declarationName_of_findDecl? declarationFound)
  have functionIndex :
      source.functions.findIdx? (·.name == declarationName) =
        some generated.sourceFunctionIndex :=
    functionFindIdx?_eq_some_of_namesNodup namesNodup
      generated.sourceFunctionFound sourceName
  change
    (findImportTarget? source (.declaration declarationName) <|>
      findFunctionTarget? source declarationName) =
        some generated.targetFunctionIndex
  rw [noImport]
  unfold findFunctionTarget?
  rw [functionIndex]
  simp [generated.targetFunctionIndex_eq]

/-- Select the exact symbolic function row and declaration-local lowering view
for any internal declaration found in a successfully lowered program. -/
theorem LoweredInternalDeclaration.exists_of_lower
    {program : Fir.LeanIR.ImpureProgram}
    {source : Fir.Wasm.Module}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    (lowered : Fir.Wasm.lower program = .ok source)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (bodyEq : declaration.value = .code sourceCode) :
    ∃ (sourceFunctionIndex : Nat) (sourceFunction : Fir.Wasm.Function),
      source.functions[sourceFunctionIndex]? = some sourceFunction ∧
        Nonempty (LoweredInternalDeclaration program
          (Fir.Wasm.cachedDeclarationNames program) declaration sourceCode
          sourceFunction) := by
  have functionsEq := LoweredInternalDeclaration.functions_of_lower lowered
  have mappedList :
      program.decls.toList.filterMapM
          (Fir.Wasm.lowerDecl program
            (Fir.Wasm.cachedDeclarationNames program)) =
        .ok source.functions.toList := by
    rw [← Array.toList_filterMapM]
    rw [functionsEq]
    rfl
  have declarationMember : declaration ∈ program.decls.toList := by
    obtain ⟨_, index, inBounds, selected, _⟩ :=
      Array.find?_eq_some_iff_getElem.mp declarationFound
    have member : declaration ∈ program.decls := by
      rw [← selected]
      exact Array.getElem_mem inBounds
    simpa using member
  obtain ⟨result, selected⟩ :=
    exceptListFilterMapM_ok_of_mem mappedList declarationMember
  obtain ⟨sourceFunction, resultEq⟩ :=
    lowerDecl_some_of_code bodyEq selected
  subst result
  have sourceMember : sourceFunction ∈ source.functions.toList :=
    exceptListFilterMapM_mem_of_mem mappedList declarationMember selected
  obtain ⟨sourceFunctionIndex, sourceFunctionFoundList⟩ :=
    List.getElem?_of_mem sourceMember
  have sourceFunctionFound :
      source.functions[sourceFunctionIndex]? = some sourceFunction := by
    simpa using sourceFunctionFoundList
  exact ⟨sourceFunctionIndex, sourceFunction, sourceFunctionFound,
    LoweredInternalDeclaration.exists_of_lowerDecl bodyEq selected⟩

/-- A value-classified source result produces the singleton function result
row required by the concrete declaration body theorem. -/
theorem LoweredInternalDeclaration.singleResult_of_abiKind
    {program : Fir.LeanIR.ImpureProgram}
    {cachedDeclarations : Array Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row :
      LoweredInternalDeclaration program cachedDeclarations declaration
        sourceCode sourceFunction)
    {resultKind : AbiKind}
    (classified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind)) :
    sourceFunction.results.size = 1 := by
  have resultsCompiled := row.resultsCompiled
  have abiResultsEq : row.abiResults = #[resultKind] := by
    unfold Fir.Wasm.resultKinds at resultsCompiled
    rw [classified] at resultsCompiled
    simp only [Bind.bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at resultsCompiled
    exact resultsCompiled.symm
  have functionResults : sourceFunction.results = row.abiResults := by
    simpa using congrArg Fir.Wasm.Function.results row.sourceFunctionEq
  rw [functionResults, abiResultsEq]
  rfl

/-- A successful function adaptation turns the source body equation into the
two-stage `CodeAdapted` boundary used by the structural correctness proof. -/
private theorem codeAdapted_of_function
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {sourceCode : LCNF.Code .impure}
    {targetFunction : Wasm.Function}
    (compiled :
      Fir.Wasm.compileCode context sourceCode = .ok sourceFunction.body)
    (adapted :
      FirTalos.function sourceModule sourceFunction = .ok targetFunction) :
    CodeAdapted context sourceModule sourceFunction [] sourceCode
      targetFunction.body := by
  unfold FirTalos.function at adapted
  cases bodyEq :
      FirTalos.instructions sourceModule sourceFunction [] sourceFunction.body with
  | error error =>
      simp only [bodyEq, Bind.bind, Except.bind] at adapted
      contradiction
  | ok targetBody =>
      simp only [bodyEq, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at adapted
      subst targetFunction
      exact ⟨sourceFunction.body, compiled, bodyEq⟩

/--
Select the matching concrete function from one actual adapted symbolic row.

The returned package uses the unified index
`sourceModule.imports.size + sourceFunctionIndex`; both its non-import fact and
its concrete function lookup are consequences of the production adapter
layout.  `Nonempty` keeps the construction proof-irrelevant while still
allowing recursive correctness proofs (whose conclusions are propositions) to
open the selected package.
-/
theorem ConcreteGeneratedDeclaration.exists_ofAdaptedFunction
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    (sourceFunctionIndex : Nat)
    (sourceFunctionFound :
      sourceModule.functions[sourceFunctionIndex]? = some sourceFunction)
    (compiled :
      Fir.Wasm.compileCode context sourceCode = .ok sourceFunction.body)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (sourceSingleResult : sourceFunction.results.size = 1)
    (adapted : FirTalos.adapt sourceModule = .ok target) :
    Nonempty (ConcreteGeneratedDeclaration context sourceCode sourceModule
      sourceFunction target) := by
  obtain ⟨targetFunctions, functionsAdapted, targetLayout⟩ :=
    FirTalos.Correctness.adapt_preserves_module_layout adapted
  have sourceFoundList :
      sourceModule.functions.toList[sourceFunctionIndex]? =
        some sourceFunction := by
    simpa using sourceFunctionFound
  obtain ⟨targetFunction, functionAdapted, targetFoundList⟩ :=
    exceptListMapM_getElem?_eq_some functionsAdapted sourceFoundList
  have targetFoundAt :
      target.wasmModule.funcs[sourceFunctionIndex]? = some targetFunction := by
    rw [targetLayout]
    exact targetFoundList
  have importCount :
      target.wasmModule.imports.length = sourceModule.imports.size :=
    FirTalos.Correctness.adapt_preserves_import_count adapted
  have notImport :
      target.wasmModule.imports[
        sourceModule.imports.size + sourceFunctionIndex]? = none := by
    apply List.getElem?_eq_none
    rw [importCount]
    omega
  have targetFunctionFound :
      target.wasmModule.funcs[
          sourceModule.imports.size + sourceFunctionIndex -
            target.wasmModule.imports.length]? =
        some targetFunction := by
    rw [importCount]
    simpa using targetFoundAt
  have signature :=
    FirTalos.Correctness.function_preserves_signature functionAdapted
  have singleResult : targetFunction.results.length = 1 := by
    rw [signature.2.2]
    simpa using sourceSingleResult
  exact ⟨{
    sourceFunctionIndex
    sourceFunctionFound
    targetFunctionIndex := sourceModule.imports.size + sourceFunctionIndex
    targetFunction
    targetFunctionIndex_eq := rfl
    functionAdapted
    notImport
    targetFunctionFound
    bodyAdapted := codeAdapted_of_function compiled functionAdapted
    localsAligned
    singleResult }⟩

/--
Whole-pipeline internal-declaration selector.

Supported lowering chooses the real symbolic function row, `adapt` chooses the
corresponding concrete row, and the declaration-local context is constructed
from the exact `lowerDecl` intermediates. Symbolic lookup and numeric adaptation
share the canonical binding row by construction; no layout premise crosses the
public selector.
-/
theorem ConcreteGeneratedDeclaration.exists_ofSupportedPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {caller : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {resultKind : AbiKind}
    (callerProgram : caller.program = program)
    (callerCaches :
      caller.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (bodyEq : declaration.value = .code sourceCode)
    (resultClassified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind)) :
    ∃ calleeContext sourceFunction,
      DeclarationContextsCoherent caller calleeContext ∧
        Nonempty (ConcreteGeneratedDeclaration calleeContext sourceCode
          sourceModule sourceFunction target) := by
  have ordinaryLowering : Fir.Wasm.lower program = .ok sourceModule :=
    LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered
  obtain ⟨sourceFunctionIndex, sourceFunction, sourceFunctionFound,
      ⟨row⟩⟩ :=
    LoweredInternalDeclaration.exists_of_lower ordinaryLowering
      declarationFound bodyEq
  have contexts : DeclarationContextsCoherent caller row.context :=
    row.contextsCoherent callerProgram callerCaches
  have localsAligned : LocalLayoutAligned row.context sourceFunction :=
    row.localsAligned
  have sourceSingleResult : sourceFunction.results.size = 1 :=
    row.singleResult_of_abiKind resultClassified
  have generated :=
    ConcreteGeneratedDeclaration.exists_ofAdaptedFunction
      sourceFunctionIndex sourceFunctionFound row.compileCode localsAligned
      sourceSingleResult adapted
  exact ⟨row.context, sourceFunction, contexts, generated⟩

/--
The production selector with the declaration parameter row retained for
recursive callee-entry reconstruction.
-/
theorem ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {caller : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {resultKind : AbiKind}
    (callerProgram : caller.program = program)
    (callerCaches :
      caller.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (bodyEq : declaration.value = .code sourceCode)
    (resultClassified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind)) :
    ∃ calleeContext sourceFunction,
      DeclarationContextsCoherent caller calleeContext ∧
        Nonempty (ConcreteGeneratedInternalDeclaration program declaration
          calleeContext sourceCode sourceModule sourceFunction target) := by
  have ordinaryLowering : Fir.Wasm.lower program = .ok sourceModule :=
    LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered
  obtain ⟨sourceFunctionIndex, sourceFunction, sourceFunctionFound,
      ⟨row⟩⟩ :=
    LoweredInternalDeclaration.exists_of_lower ordinaryLowering
      declarationFound bodyEq
  have contexts : DeclarationContextsCoherent caller row.context :=
    row.contextsCoherent callerProgram callerCaches
  have sourceSingleResult : sourceFunction.results.size = 1 :=
    row.singleResult_of_abiKind resultClassified
  obtain ⟨generated⟩ :=
    ConcreteGeneratedDeclaration.exists_ofAdaptedFunction
      sourceFunctionIndex sourceFunctionFound row.compileCode row.localsAligned
      sourceSingleResult adapted
  have sourceParameters :
      sourceFunction.params = row.paramLocals.reverse.toArray := by
    simpa using congrArg Fir.Wasm.Function.params row.sourceFunctionEq
  have parameterIdsUnique :=
    declarationParameterIdsUnique_of_lowerSupported lowered declarationFound
  have callIndexEq :=
    generated.internalCallIndex row namesUnique ordinaryLowering
      declarationFound bodyEq
  have declarationNameEq := declarationName_of_findDecl? declarationFound
  exact ⟨row.context, sourceFunction, contexts, ⟨{
    toConcreteGeneratedDeclaration := generated
    contextProgram := rfl
    contextCaches := rfl
    parameterLocals := row.paramLocals
    parameterIdsUnique
    parametersAdded := row.paramsAdded
    sourceParameters
    callIndexEq := by simpa [declarationNameEq] using callIndexEq }⟩⟩

/--
Production selection at an already exposed canonical lowering row.

The hereditary source derivation carries this `LoweredInternalDeclaration`.
Determinism of the executable `filterMapM lowerDecl` table puts that exact
function in the generated symbolic module, and adaptation selects its exact
concrete row. Consequently the recursive induction hypothesis and production
callee package have definitionally the same declaration-local context; no
context cast, target execution, or translation certificate is needed.
-/
theorem
    ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
    {program : Fir.LeanIR.ImpureProgram}
    {caller : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {declarationName : Name}
    {declaration : LCNF.Decl .impure}
    {sourceCode : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    {resultKind : AbiKind}
    (callerProgram : caller.program = program)
    (callerCaches :
      caller.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (declarationFound :
      program.findDecl? declarationName = some declaration)
    (row :
      LoweredInternalDeclaration caller.program caller.cachedDeclarations
        declaration sourceCode sourceFunction)
    (resultClassified :
      Fir.Wasm.abiKind? declaration.type = .ok (some resultKind)) :
    Nonempty (ConcreteGeneratedInternalDeclaration program declaration
      row.context sourceCode sourceModule sourceFunction target) := by
  have ordinaryLowering : Fir.Wasm.lower program = .ok sourceModule :=
    LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered
  have functionsEq :=
    LoweredInternalDeclaration.functions_of_lower ordinaryLowering
  have mappedList :
      program.decls.toList.filterMapM
          (Fir.Wasm.lowerDecl program
            (Fir.Wasm.cachedDeclarationNames program)) =
        .ok sourceModule.functions.toList := by
    rw [← Array.toList_filterMapM]
    rw [functionsEq]
    rfl
  have declarationMember : declaration ∈ program.decls.toList := by
    obtain ⟨_, index, inBounds, selected, _⟩ :=
      Array.find?_eq_some_iff_getElem.mp declarationFound
    have member : declaration ∈ program.decls := by
      rw [← selected]
      exact Array.getElem_mem inBounds
    simpa using member
  have rowSelected :
      Fir.Wasm.lowerDecl program (Fir.Wasm.cachedDeclarationNames program)
          declaration = .ok (some sourceFunction) := by
    simpa only [callerProgram, callerCaches] using row.lowerDecl
  have sourceMember : sourceFunction ∈ sourceModule.functions.toList :=
    exceptListFilterMapM_mem_of_mem mappedList declarationMember rowSelected
  obtain ⟨sourceFunctionIndex, sourceFunctionFoundList⟩ :=
    List.getElem?_of_mem sourceMember
  have sourceFunctionFound :
      sourceModule.functions[sourceFunctionIndex]? = some sourceFunction := by
    simpa using sourceFunctionFoundList
  have sourceSingleResult : sourceFunction.results.size = 1 :=
    row.singleResult_of_abiKind resultClassified
  obtain ⟨generated⟩ :=
    ConcreteGeneratedDeclaration.exists_ofAdaptedFunction
      sourceFunctionIndex sourceFunctionFound row.compileCode row.localsAligned
      sourceSingleResult adapted
  have sourceParameters :
      sourceFunction.params = row.paramLocals.reverse.toArray := by
    simpa using congrArg Fir.Wasm.Function.params row.sourceFunctionEq
  have parameterIdsUnique :=
    declarationParameterIdsUnique_of_lowerSupported lowered declarationFound
  have parametersAdded :
      Fir.Wasm.addDeclarationParams program declaration =
        .ok row.paramLocals := by
    simpa only [callerProgram] using row.paramsAdded
  have callIndexEq :=
    generated.internalCallIndex row namesUnique ordinaryLowering
      declarationFound (by simpa only [callerProgram] using row.bodyEq)
  have declarationNameEq := declarationName_of_findDecl? declarationFound
  exact ⟨{
    toConcreteGeneratedDeclaration := generated
    contextProgram := by
      change caller.program = program
      exact callerProgram
    contextCaches := by
      change caller.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program
      exact callerCaches
    parameterLocals := row.paramLocals
    parameterIdsUnique
    parametersAdded
    sourceParameters
    callIndexEq := by simpa [declarationNameEq] using callIndexEq }⟩

/--
Module-wide production declaration family.

Every value-returning internal declaration selected from the source program is
paired with the exact symbolic and concrete function row produced by the
successful `lowerSupported`/`adapt` pipeline. The caller context is universally
quantified: recursive callers need only share the source program and generated
lazy-cache name table, while each callee retains its independently computed
local layout.

This is static compiler evidence, not a target execution certificate. Dynamic
hereditary correctness is built from the returned
`ConcreteGeneratedDeclaration` and the source execution of that body.
-/
def ConcreteGeneratedDeclarationFamily
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (target : AdaptedModule) : Prop :=
  ∀ {caller : Fir.Wasm.Context}
      {declarationName : Name}
      {declaration : LCNF.Decl .impure}
      {sourceCode : LCNF.Code .impure}
      {resultKind : AbiKind},
    caller.program = program →
      caller.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program →
        program.findDecl? declarationName = some declaration →
          declaration.value = .code sourceCode →
            Fir.Wasm.abiKind? declaration.type = .ok (some resultKind) →
              ∃ calleeContext sourceFunction,
                DeclarationContextsCoherent caller calleeContext ∧
                  Nonempty (ConcreteGeneratedInternalDeclaration program
                    declaration calleeContext sourceCode sourceModule
                    sourceFunction target)

/--
One successful production lowering/adaptation pair constructs the complete
static declaration family. No per-declaration compiler premise remains at
recursive call sites.
-/
theorem ConcreteGeneratedDeclarationFamily.ofSupportedPipeline
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target) :
    ConcreteGeneratedDeclarationFamily program sourceModule target := by
  intro caller declarationName declaration sourceCode resultKind callerProgram
    callerCaches declarationFound bodyEq resultClassified
  exact
    ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipeline
      callerProgram callerCaches namesUnique lowered adapted declarationFound
      bodyEq resultClassified

/-- Every supported export exposes its export-independent declaration body. -/
def ConcreteSupportedExport.toSupportedDeclaration
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
        sourceFunction target hosts exportName) :
    ConcreteSupportedDeclaration context sourceCode sourceModule sourceFunction
      target := {
  targetFunctionIndex := spec.targetFunctionIndex
  targetFunction := spec.targetFunction
  notImport := spec.notImport
  targetFunctionFound := spec.targetFunctionFound
  bodyAdapted := spec.bodyAdapted
  localsAligned := spec.localsAligned
  singleResult := spec.singleResult }

/--
Package the structural mixed-code theorem as one hereditary cache-aware
declaration result.

The canonical execution is proved with exactly the source-selected allocation
budget. To establish the declaration package's stronger budget-parametric
field, re-run the same structural proof with arbitrary caller-owned slack and
use `CodeWP.exactReturn_unique` to identify its existential target result with
the canonical store and lane. Thus callers receive one fixed execution result;
the repeated proof supplies only resource evidence.
-/
theorem
    ConcreteSupportedDeclaration.budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedDeclaration context sourceCode sourceModule
        sourceFunction target)
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CallSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {EffectSupported : EffectSupportedPredicate}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityBudgetedCodeEvaluates context sourceExternals
        DirectSupported ExternalSupported CallSupported LazySupported
        CaseSupported EffectSupported directLetAllocationCost facts
        sourceRuntime sourceEnv sourceCode resultFacts resultRuntime resultEnv
        resultValue requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (directRuntimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env DirectSupported
        directLetAllocationCost
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (externalRuntimeRefines :
      ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        ExternalSupported
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (callRuntimeRefines :
      ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        CallSupported
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (lazyRuntimeRefines :
      ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        LazySupported
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction []
        target.wasmModule hosts.env CaseSupported)
    (effectRuntimeRefines :
      ∀ facts,
        EffectRuntimeRefines context sourceModule sourceFunction []
          target.wasmModule hosts.env EffectSupported
          (ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals)
            sourceRuntime initial initialWitness facts))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness resultKind physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical
        requiredBytes := by
  have initialExact :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts (requiredBytes + 0) sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness := by
    simpa using invariant
  obtain ⟨sourceResult, resultStore, resultLocals, resultWitness, resultKind,
      physical, exactWP, resultInvariant, entryTransports, failureClear,
      valueRelated⟩ :=
    codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelativeWithSlack
      (slack := 0) evaluation spec.bodyAdapted spec.localsAligned initialExact
      (fun related => related.stateRelated) directRuntimeRefines
      externalRuntimeRefines callRuntimeRefines lazyRuntimeRefines
      caseRuntimeRefines effectRuntimeRefines
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv sourceCode spec.targetFunction initial
        resultStore initialWitness parameters physical := by
    refine ⟨parameterCount, spec.singleResult, fun callerTail => ?_⟩
    apply exactWP.conseq
    intro continuation returned
    subst continuation
    simp [ConcreteFunctionBodyPost, ExactReturnPost, spec.singleResult,
      ← parameterCount]
  have successful :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
        sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex
        initial resultStore initialWitness resultWitness parameters resultKind
        resultValue physical := {
    sourceResult
    notImport := spec.notImport
    functionFound := spec.targetFunctionFound
    body
    runtimeRelated := resultInvariant.stateRelated.stateRelated.1
    failureClear
    valueRelated }
  have capacityPreserving :
      CapacityPreservingSuccessfulDeclaration context sourceModule
        sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical := {
    successful
    witnessTransport := entryTransports.witness
    capacityTransport := entryTransports.capacity }
  have residualBudget :
      ∀ {remainingBytes : Nat},
        requiredBytes ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            resultStore.host.runtime.heap.AddressSpaceBudget
              (remainingBytes - requiredBytes) := by
    intro remainingBytes stepFits budget
    let slack := remainingBytes - requiredBytes
    have budgetEq : requiredBytes + slack = remainingBytes := by
      simp [slack, Nat.add_sub_of_le stepFits]
    have slackInvariant :
        ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals facts (requiredBytes + slack) sourceRuntime sourceEnv
          initial (spec.targetFunction.toLocals parameters.reverse)
          initialWitness :=
      invariant.withBudget (by simpa [budgetEq] using budget)
    obtain ⟨_, slackStore, slackLocals, slackWitness, slackKind,
        slackPhysical, slackWP, slackResultInvariant, _, _, _⟩ :=
      codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelativeWithSlack
        (slack := slack) evaluation spec.bodyAdapted spec.localsAligned
        slackInvariant (fun related => related.stateRelated)
        directRuntimeRefines externalRuntimeRefines callRuntimeRefines
        lazyRuntimeRefines caseRuntimeRefines effectRuntimeRefines
    have resultEq := exactWP.exactReturn_unique slackWP
    rw [resultEq.1]
    simpa [slack] using slackResultInvariant.budget
  exact ⟨resultStore, resultWitness, resultKind, physical, {
    declaration := {
      toClosureTablesTransport := entryTransports.toClosureTablesTransport
      capacityPreserving
      ordinaryTransport := entryTransports.ordinary
      externalsPreserved := entryTransports.externals
      residualBudget }
    cacheTable := resultInvariant.2.1 }⟩

/--
Package ABI-indexed hereditary structural correctness as the cache-aware
declaration theorem consumed by generated direct calls.

Unlike the compatibility packaging theorem above, the returned physical lane
is related at the declaration's declared result ABI rather than at an
existential implementation kind. The proof remains budget-parametric by
replaying the same source derivation with arbitrary caller slack.
-/
theorem
    ConcreteSupportedDeclaration.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedDeclaration context sourceCode sourceModule
        sourceFunction target)
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        DirectSupported ExternalSupported LazySupported CaseSupported
        EffectSupported directLetAllocationCost context resultKind facts
        sourceRuntime sourceEnv sourceCode resultFacts resultRuntime resultEnv
        resultValue requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (directRuntimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env (DirectSupported context)
        directLetAllocationCost
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (externalRuntimeRefines :
      ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        (ExternalSupported context)
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (callRuntimeRefines :
      ReuseCapacityCallLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        (ReuseCapacityDirectHereditaryCallSupported sourceExternals
          DirectSupported ExternalSupported LazySupported CaseSupported
          EffectSupported directLetAllocationCost context)
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (lazyRuntimeRefines :
      ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        (LazySupported context)
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (caseRuntimeRefines :
      CaseRuntimeRefines context sourceModule sourceFunction []
        target.wasmModule hosts.env (CaseSupported context))
    (effectRuntimeRefines :
      ∀ facts,
        EffectRuntimeRefines context sourceModule sourceFunction []
          target.wasmModule hosts.env (EffectSupported context)
          (ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals)
            sourceRuntime initial initialWitness facts))
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical
        requiredBytes := by
  have initialExact :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        sourceRuntime initial initialWitness facts (requiredBytes + 0)
        sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness := by
    exact ⟨by simpa using invariant,
      ReuseCapacityCodeEntryTransports.refl sourceRuntime initial
        initialWitness⟩
  obtain ⟨resultStore, resultLocals, resultWitness, physical, exactWP,
      resultInvariant, failureClear, valueRelated⟩ :=
    codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_withSlack
      (slack := 0) evaluation spec.bodyAdapted spec.localsAligned initialExact
      (fun related => related.1.stateRelated) directRuntimeRefines
      externalRuntimeRefines callRuntimeRefines lazyRuntimeRefines
      caseRuntimeRefines effectRuntimeRefines
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv sourceCode spec.targetFunction initial
        resultStore initialWitness parameters physical := by
    refine ⟨parameterCount, spec.singleResult, fun callerTail => ?_⟩
    apply exactWP.conseq
    intro continuation returned
    subst continuation
    simp [ConcreteFunctionBodyPost, ExactReturnPost, spec.singleResult,
      ← parameterCount]
  have successful :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
        sourceEnv sourceCode spec.targetFunction spec.targetFunctionIndex
        initial resultStore initialWitness resultWitness parameters resultKind
        resultValue physical := {
    sourceResult := evaluation.sourceResult
    notImport := spec.notImport
    functionFound := spec.targetFunctionFound
    body
    runtimeRelated := resultInvariant.1.stateRelated.stateRelated.1
    failureClear
    valueRelated }
  have capacityPreserving :
      CapacityPreservingSuccessfulDeclaration context sourceModule
        sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical := {
    successful
    witnessTransport := resultInvariant.2.witness
    capacityTransport := resultInvariant.2.capacity }
  have residualBudget :
      ∀ {remainingBytes : Nat},
        requiredBytes ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            resultStore.host.runtime.heap.AddressSpaceBudget
              (remainingBytes - requiredBytes) := by
    intro remainingBytes stepFits budget
    let slack := remainingBytes - requiredBytes
    have budgetEq : requiredBytes + slack = remainingBytes := by
      simp [slack, Nat.add_sub_of_le stepFits]
    have slackInvariant :
        ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness facts (requiredBytes + slack)
          sourceRuntime sourceEnv initial
          (spec.targetFunction.toLocals parameters.reverse) initialWitness := by
      exact ⟨invariant.withBudget (by simpa [budgetEq] using budget),
        ReuseCapacityCodeEntryTransports.refl sourceRuntime initial
          initialWitness⟩
    obtain ⟨slackStore, slackLocals, slackWitness, slackPhysical, slackWP,
        slackResultInvariant, _, _⟩ :=
      codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_withSlack
        (slack := slack) evaluation spec.bodyAdapted spec.localsAligned
        slackInvariant (fun related => related.1.stateRelated)
        directRuntimeRefines externalRuntimeRefines callRuntimeRefines
        lazyRuntimeRefines caseRuntimeRefines effectRuntimeRefines
    have resultEq := exactWP.exactReturn_unique slackWP
    rw [resultEq.1]
    simpa [slack] using slackResultInvariant.1.budget
  exact ⟨resultStore, resultWitness, physical, {
    declaration := {
      toClosureTablesTransport := resultInvariant.2.toClosureTablesTransport
      capacityPreserving
      ordinaryTransport := resultInvariant.2.ordinary
      externalsPreserved := resultInvariant.2.externals
      residualBudget }
    cacheTable := resultInvariant.1.2.1 }⟩

/--
The production direct-callee induction step.

The caller frame, admitted call site, generated declaration row, related
physical arguments, and the enclosing call's budget-fit check construct the
exact callee entry. A finite source-body evaluation and the uniform operation
laws then yield the cache-aware hereditary declaration package consumed by
the caller. No target execution or translation certificate is supplied at the
call site.
-/
theorem
    ConcreteGeneratedInternalDeclaration.budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : LCNF.LetDecl .impure}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {callerEnv : Env} {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes stepCost : Nat}
    {sourceRuntime resultRuntime : RuntimeState}
    {resultFacts : ReuseCapacityFacts} {resultEnv : Env}
    {resultValue : Value}
    {initial : Wasm.Store Host} {callerLocals : Wasm.Locals}
    {initialWitness : RefinementWitness}
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction
        sourceExternals facts remainingBytes sourceRuntime callerEnv initial
        callerLocals initialWitness)
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction target)
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated initialWitness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList)
    (stepFits : stepCost ≤ remainingBytes)
    {DirectSupported :
      ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {CallSupported :
      RuntimeState → Env → LCNF.LetDecl .impure → LCNF.Code .impure →
        RuntimeState → Value → Nat → Prop}
    {LazySupported :
      LazyCachePath → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {CaseSupported :
      RuntimeState → Env → LCNF.Cases .impure → LCNF.Code .impure → Prop}
    {EffectSupported : EffectSupportedPredicate}
    (evaluation :
      ReuseCapacityBudgetedCodeEvaluates calleeContext sourceExternals
        DirectSupported ExternalSupported CallSupported LazySupported
        CaseSupported EffectSupported directLetAllocationCost [] sourceRuntime
        site.calleeEnv site.calleeCode resultFacts resultRuntime resultEnv
        resultValue stepCost)
    (directRuntimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost calleeContext sourceModule
        calleeFunction [] target.wasmModule hosts.env DirectSupported
        directLetAllocationCost
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (externalRuntimeRefines :
      ReuseCapacityExternalLetRuntimeRefinesWithCost calleeContext sourceModule
        calleeFunction [] target.wasmModule hosts.env sourceExternals
        ExternalSupported
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (callRuntimeRefines :
      ReuseCapacityCallLetRuntimeRefinesWithCost calleeContext sourceModule
        calleeFunction [] target.wasmModule hosts.env sourceExternals
        CallSupported
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (lazyRuntimeRefines :
      ReuseCapacityLazyLetRuntimeRefinesWithCost calleeContext sourceModule
        calleeFunction [] target.wasmModule hosts.env sourceExternals
        LazySupported
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
            sourceExternals)
          sourceRuntime initial initialWitness))
    (caseRuntimeRefines :
      CaseRuntimeRefines calleeContext sourceModule calleeFunction []
        target.wasmModule hosts.env CaseSupported)
    (effectRuntimeRefines :
      ∀ facts,
        EffectRuntimeRefines calleeContext sourceModule calleeFunction []
          target.wasmModule hosts.env EffectSupported
          (ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
              sourceExternals)
            sourceRuntime initial initialWitness facts)) :
    ∃ resultStore resultWitness resultKind physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache calleeContext
        sourceModule calleeFunction target.wasmModule hosts.env
        sourceExternals sourceRuntime resultRuntime site.calleeEnv
        site.calleeCode row.targetFunction row.targetFunctionIndex initial
        resultStore initialWitness resultWitness physicalArgs.reverse
        resultKind resultValue physical stepCost := by
  have calleeFrame :=
    callerFrame.generatedDirectCalleeEntryAtCost site row argumentsRelated
      stepFits
  have calleeFrameForCall :
      ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
        sourceExternals [] stepCost sourceRuntime site.calleeEnv initial
        (row.targetFunction.toLocals physicalArgs.reverse.reverse)
        initialWitness := by
    simpa using calleeFrame
  exact
    row.toConcreteGeneratedDeclaration.toConcreteSupportedDeclaration
      |>.budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates
        evaluation calleeFrameForCall directRuntimeRefines externalRuntimeRefines
        callRuntimeRefines lazyRuntimeRefines caseRuntimeRefines
        effectRuntimeRefines (row.targetParameterCount site argumentsRelated)

/-- Recover the ordinary ABI classifier hidden by the source-facing direct
classifier. -/
private theorem abiKind?_eq_ok_some_of_directAbiKind?_eq_some
    {type : Expr} {kind : AbiKind}
    (classified : Fir.Wasm.directAbiKind? type = some kind) :
    Fir.Wasm.abiKind? type = .ok (some kind) := by
  unfold Fir.Wasm.directAbiKind? at classified
  cases result : Fir.Wasm.abiKind? type with
  | error error => simp [result] at classified
  | ok optional =>
      cases optional with
      | none => simp [result] at classified
      | some actual =>
          simp only [result, Option.some.injEq] at classified
          subst actual
          rfl

/--
Uniform non-recursive operation laws for every declaration row generated by
one successful production pipeline.

These are the local compiler/runtime theorems consumed by the hereditary
structural induction. They quantify over the actual generated function and
over every concrete entry state; they contain no source execution or target
execution certificate. Direct named calls are deliberately absent: their law
is obtained recursively from the nested hereditary derivation.
-/
structure DirectHereditaryGeneratedOperationLaws
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (target : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl)
    (DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop)
    (LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop)
    (CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop)
    (EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate) : Prop where
  direct :
    ∀ {declaration : LCNF.Decl .impure}
        {context : Fir.Wasm.Context}
        {sourceCode : LCNF.Code .impure}
        {sourceFunction : Fir.Wasm.Function}
        (_row : ConcreteGeneratedInternalDeclaration program declaration
          context sourceCode sourceModule sourceFunction target)
        {entryRuntime : RuntimeState}
        {entryStore : Wasm.Store Host}
        {entryWitness : RefinementWitness},
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env
        (DirectSupported context) directLetAllocationCost
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          entryRuntime entryStore entryWitness)
  external :
    ∀ {declaration : LCNF.Decl .impure}
        {context : Fir.Wasm.Context}
        {sourceCode : LCNF.Code .impure}
        {sourceFunction : Fir.Wasm.Function}
        (_row : ConcreteGeneratedInternalDeclaration program declaration
          context sourceCode sourceModule sourceFunction target)
        {entryRuntime : RuntimeState}
        {entryStore : Wasm.Store Host}
        {entryWitness : RefinementWitness},
      ReuseCapacityExternalLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        (ExternalSupported context)
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          entryRuntime entryStore entryWitness)
  lazy :
    ∀ {declaration : LCNF.Decl .impure}
        {context : Fir.Wasm.Context}
        {sourceCode : LCNF.Code .impure}
        {sourceFunction : Fir.Wasm.Function}
        (_row : ConcreteGeneratedInternalDeclaration program declaration
          context sourceCode sourceModule sourceFunction target)
        {entryRuntime : RuntimeState}
        {entryStore : Wasm.Store Host}
        {entryWitness : RefinementWitness},
      ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
        sourceFunction [] target.wasmModule hosts.env sourceExternals
        (LazySupported context)
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          entryRuntime entryStore entryWitness)
  caseOf :
    ∀ {declaration : LCNF.Decl .impure}
        {context : Fir.Wasm.Context}
        {sourceCode : LCNF.Code .impure}
        {sourceFunction : Fir.Wasm.Function}
        (_row : ConcreteGeneratedInternalDeclaration program declaration
          context sourceCode sourceModule sourceFunction target),
      CaseRuntimeRefines context sourceModule sourceFunction []
        target.wasmModule hosts.env (CaseSupported context)
  effect :
    ∀ {declaration : LCNF.Decl .impure}
        {context : Fir.Wasm.Context}
        {sourceCode : LCNF.Code .impure}
        {sourceFunction : Fir.Wasm.Function}
        (_row : ConcreteGeneratedInternalDeclaration program declaration
          context sourceCode sourceModule sourceFunction target)
        {entryRuntime : RuntimeState}
        {entryStore : Wasm.Store Host}
        {entryWitness : RefinementWitness}
        (facts : ReuseCapacityFacts),
      EffectRuntimeRefines context sourceModule sourceFunction []
        target.wasmModule hosts.env (EffectSupported context)
        (ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          entryRuntime entryStore entryWitness facts)

/-- The production operation theorems instantiate the generated-row bundle
for the first recursive fragment: supported direct heap/reuse operations,
default-only cases, and no external, lazy, or no-result effect nodes.

Each direct law is selected for the exact internal function row. The empty
families are discharged by their generic impossibility theorems, so this
constructor contains no per-program target behavior premise. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_noCalls
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
      sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun _ => NoReuseCapacityExternalsSupported)
      (fun _ => NoReuseCapacityLazySupported)
      (fun _ => DefaultOnlyCaseSupported)
      (fun _ => NoEffectsSupported) := by
  constructor
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact reuseCapacityExternalLetRuntimeRefinesWithCost_noExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact reuseCapacityLazyLetRuntimeRefinesWithCost_noLazy
  · intro declaration context sourceCode sourceFunction row
    exact caseRuntimeRefines_defaultOnly
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness facts
    exact effectRuntimeRefines_noEffects

/-- The production operation laws for recursive generated declarations with
the complete pure `Nat`/`Int`/scalar external family.  The external law is
selected for each exact generated function row, just like the direct law;
being a named export is required only for the root entry point. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
      sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun context => PureExternalSupported context sourceExternals)
      (fun _ => NoReuseCapacityLazySupported)
      (fun _ => DefaultOnlyCaseSupported)
      (fun _ => NoEffectsSupported) := by
  constructor
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact reuseCapacityLazyLetRuntimeRefinesWithCost_noLazy
  · intro declaration context sourceCode sourceFunction row
    exact caseRuntimeRefines_defaultOnly
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness facts
    exact effectRuntimeRefines_noEffects

/-- The production operation laws with pure external calls, the complete
supported no-result runtime family, and every currently proved production
case mode. Each law is selected for the exact generated function row; export
membership remains a property only of the root entry point. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal_effects
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
      sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun context => PureExternalSupported context sourceExternals)
      (fun _ => NoReuseCapacityLazySupported)
      (fun context => ProductionCasesSupported context)
      (fun context => OwnershipTagAndAllFieldMutationEffectSupported context) := by
  constructor
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact reuseCapacityLazyLetRuntimeRefinesWithCost_noLazy
  · intro declaration context sourceCode sourceFunction row
    exact (row.toSupportedFunction spec).caseRuntimeRefines_productionCases
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness facts
    exact
      (row.toSupportedFunction spec).effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache
        sourceExternals

/--
The structural hereditary theorem specialized to actual generated declaration
rows. Its caller-slack quantifier is part of the induction motive, so a nested
direct callee can supply both its exact execution and the residual-budget law
required by the enclosing call.
-/
theorem codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_generated
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adaptedModule : FirTalos.adapt sourceModule = .ok target)
    (operationLaws :
      DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
        sourceExternals DirectSupported ExternalSupported LazySupported
        CaseSupported EffectSupported)
    {declaration : LCNF.Decl .impure}
    {context : Fir.Wasm.Context}
    {functionCode code : LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (row : ConcreteGeneratedInternalDeclaration program declaration context
      functionCode sourceModule sourceFunction target)
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime entryRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {resultValue : Value} {requiredBytes slack : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        DirectSupported ExternalSupported LazySupported CaseSupported
        EffectSupported directLetAllocationCost context expectedResult facts
        sourceRuntime sourceEnv code resultFacts resultRuntime resultEnv
        resultValue requiredBytes)
    {targetCode : Wasm.Program}
    {initial entryStore : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    (codeAdapted :
      CodeAdapted context sourceModule sourceFunction [] code targetCode)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        entryRuntime entryStore entryWitness facts (requiredBytes + slack)
        sourceRuntime sourceEnv initial locals witness) :
    ∃ resultStore resultLocals resultWitness physical,
      CodeWP context sourceModule sourceFunction [] target.wasmModule hosts.env
          sourceRuntime sourceEnv code targetCode initial locals witness []
          (ExactReturnControlPost resultStore physical) ∧
        ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          entryRuntime entryStore entryWitness resultFacts slack resultRuntime
          resultEnv resultStore resultLocals resultWitness ∧
        resultStore.host.failure? = none ∧
        PhysicalValueRel resultWitness expectedResult physical resultValue := by
  induction evaluation generalizing declaration functionCode sourceFunction
      targetCode initial locals witness entryRuntime entryStore entryWitness
      slack with
  | ret sourceLookup resultCompiled resultRefines =>
      exact codeWP_of_reuseCapacityDirectHereditaryReturn_withSlack
        sourceLookup resultCompiled resultRefines codeAdapted row.localsAligned
        (by simpa only [Nat.zero_add] using invariant)
        (fun related => related.1.stateRelated)
  | @letValue context facts decl sourceRuntime sourceEnv nextRuntime sourceValue
      nextFacts expectedResult continuation resultFacts resultRuntime resultEnv
      resultValue continuationCost supported sourceStep transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq codeAdapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          directLetAllocationCost decl ≤
            (directLetAllocationCost decl + continuationCost) + slack :=
        by omega
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, _directTransports, producedTransfer,
          nextInvariant⟩ :=
        operationLaws.direct row supported stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        have budgetEq :
            directLetAllocationCost decl + continuationCost + slack -
                directLetAllocationCost decl =
              continuationCost + slack := by
          omega
        simpa only [budgetEq] using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih row continuationAdapted continuationInvariant
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_letValue valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @externalLet context sourceRuntime sourceEnv decl continuation nextRuntime
      sourceValue stepCost facts nextFacts expectedResult resultFacts
      resultRuntime resultEnv resultValue continuationCost supported sourceStep
      transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq codeAdapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ (stepCost + continuationCost) + slack :=
        by omega
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, producedTransfer, nextInvariant⟩ :=
        operationLaws.external row supported stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        have budgetEq :
            stepCost + continuationCost + slack - stepCost =
              continuationCost + slack := by
          omega
        simpa only [budgetEq] using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih row continuationAdapted continuationInvariant
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_externalLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @directCallLet context decl sourceEnv sourceRuntime calleeResultFacts
      nextRuntime calleeResultEnv sourceValue stepCost facts nextFacts
      expectedResult continuation resultFacts resultRuntime resultEnv resultValue
      continuationCost calleeFunction site loweredRow callee transfer continued
      calleeIH continuedIH =>
      have programEq : context.program = program := row.contextProgram
      subst program
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq codeAdapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          stepCost ≤ (stepCost + continuationCost) + slack := by
        omega
      have sourceStep :
          SourceCallLetResult context sourceExternals sourceRuntime sourceEnv
            decl continuation nextRuntime sourceValue :=
        site.sourceCallLetResult (loweredRow.contextsCoherent rfl rfl)
          callee.sourceResult
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok (site.argumentCode ++
              [.call (.declaration site.declaration)]) := by
        simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind, site.valueEq,
          site.kindEq, site.argumentsCompiled, site.declarationFound,
          site.nonCached, Bind.bind, Except.bind, pure, Except.pure]
      have valueCodeEq :
          valueCode =
            site.argumentCode ++ [.call (.declaration site.declaration)] := by
        rw [expectedCompiled] at valueCompiled
        exact (Except.ok.inj valueCompiled).symm
      subst valueCode
      obtain ⟨targetArguments, functionIndex, argumentsAdapted, callFound,
          targetValueEq⟩ :=
        instructions_append_declaration_call_eq valueAdapted
      subst targetValue
      obtain ⟨physicalArgs, argumentsReady, _, argumentsRelated⟩ :=
        constructorArgsReady_of_compileArgs row.localsAligned
          site.argumentsCompiled argumentsAdapted site.argumentsEvaluated
          invariant.1.stateRelated.stateRelated
      have assembled :
          ClosureArgumentAssembly target.wasmModule hosts.env targetArguments
            physicalArgs initial locals :=
        ClosureArgumentAssembly.ofConstructorArgsReady argumentsReady
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        row.localsAligned site.resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      have declarationFound :
          context.program.findDecl? site.declaration =
            some site.sourceDeclaration :=
        site.declarationFound
      have resultClassified :
          Fir.Wasm.abiKind? site.sourceDeclaration.type =
            .ok (some site.calleeResultKind) :=
        abiKind?_eq_ok_some_of_directAbiKind?_eq_some site.calleeResult
      obtain ⟨generatedRow⟩ :=
        ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
          rfl row.contextCaches namesUnique lowered adaptedModule declarationFound
          loweredRow resultClassified
      have calleeFrame :=
        invariant.1.generatedDirectCalleeEntryAtCost site generatedRow
          argumentsRelated stepFits
      have calleeEntry :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
              sourceExternals)
            sourceRuntime initial witness [] (stepCost + 0) sourceRuntime
            site.calleeEnv initial
            (generatedRow.targetFunction.toLocals physicalArgs) witness := by
        exact ⟨by simpa using calleeFrame,
          ReuseCapacityCodeEntryTransports.refl sourceRuntime initial witness⟩
      obtain ⟨afterCall, calleeLocals, resultWitness, physical, calleeWP,
          calleeInvariant, calleeFailureClear, calleeValueRelated⟩ :=
        calleeIH generatedRow generatedRow.bodyAdapted calleeEntry
      have parameterCount :
          physicalArgs.reverse.length =
            generatedRow.targetFunction.numParams :=
        generatedRow.targetParameterCount site argumentsRelated
      have calleeBody :
          DeclarationBodyWP loweredRow.context sourceModule calleeFunction
            target.wasmModule hosts.env sourceRuntime site.calleeEnv
            site.calleeCode generatedRow.targetFunction initial afterCall
            witness physicalArgs.reverse physical := by
        refine ⟨parameterCount, generatedRow.singleResult,
          fun callerTail => ?_⟩
        simp only [List.reverse_reverse]
        apply calleeWP.conseq
        intro returnedContinuation returned
        subst returnedContinuation
        simp [ConcreteFunctionBodyPost, ExactReturnPost,
          generatedRow.singleResult, ← parameterCount]
      have calleeSuccessful :
          SuccessfulDeclaration loweredRow.context sourceModule calleeFunction
            target.wasmModule hosts.env sourceExternals sourceRuntime
            nextRuntime site.calleeEnv site.calleeCode
            generatedRow.targetFunction generatedRow.targetFunctionIndex
            initial afterCall witness resultWitness physicalArgs.reverse
            site.calleeResultKind sourceValue physical := {
        sourceResult := callee.sourceResult
        notImport := generatedRow.notImport
        functionFound := generatedRow.targetFunctionFound
        body := calleeBody
        runtimeRelated := calleeInvariant.1.stateRelated.stateRelated.1
        failureClear := calleeFailureClear
        valueRelated := calleeValueRelated }
      have calleeCapacityPreserving :
          CapacityPreservingSuccessfulDeclaration loweredRow.context
            sourceModule calleeFunction target.wasmModule hosts.env
            sourceExternals sourceRuntime nextRuntime site.calleeEnv
            site.calleeCode generatedRow.targetFunction
            generatedRow.targetFunctionIndex initial afterCall witness
            resultWitness physicalArgs.reverse site.calleeResultKind sourceValue
            physical := {
        successful := calleeSuccessful
        witnessTransport := calleeInvariant.2.witness
        capacityTransport := calleeInvariant.2.capacity }
      have calleeResidualBudget :
          ∀ {remainingBytes : Nat},
            stepCost ≤ remainingBytes →
              initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
                afterCall.host.runtime.heap.AddressSpaceBudget
                  (remainingBytes - stepCost) := by
        intro remainingBytes calleeFits budget
        let calleeSlack := remainingBytes - stepCost
        have budgetEq : stepCost + calleeSlack = remainingBytes := by
          simp [calleeSlack, Nat.add_sub_of_le calleeFits]
        have slackFrame :
            ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
              sourceExternals [] (stepCost + calleeSlack) sourceRuntime
              site.calleeEnv initial
              (generatedRow.targetFunction.toLocals physicalArgs) witness :=
          calleeFrame.withBudget (by simpa [budgetEq] using budget)
        have slackEntry :
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
                sourceExternals)
              sourceRuntime initial witness [] (stepCost + calleeSlack)
              sourceRuntime site.calleeEnv initial
              (generatedRow.targetFunction.toLocals physicalArgs) witness :=
          ⟨slackFrame,
            ReuseCapacityCodeEntryTransports.refl sourceRuntime initial witness⟩
        obtain ⟨slackStore, slackLocals, slackWitness, slackPhysical, slackWP,
            slackInvariant, _, _⟩ :=
          calleeIH generatedRow generatedRow.bodyAdapted slackEntry
        have resultEq := calleeWP.exactReturn_unique slackWP
        rw [resultEq.1]
        simpa [calleeSlack] using slackInvariant.1.budget
      have calleeResult :
          BudgetedCapacityPreservingSuccessfulDeclarationWithCache
            loweredRow.context sourceModule calleeFunction target.wasmModule
            hosts.env sourceExternals sourceRuntime nextRuntime site.calleeEnv
            site.calleeCode generatedRow.targetFunction
            generatedRow.targetFunctionIndex initial afterCall witness
            resultWitness physicalArgs.reverse site.calleeResultKind sourceValue
            physical stepCost := {
        declaration := {
          toClosureTablesTransport :=
            calleeInvariant.2.toClosureTablesTransport
          capacityPreserving := calleeCapacityPreserving
          ordinaryTransport := calleeInvariant.2.ordinary
          externalsPreserved := calleeInvariant.2.externals
          residualBudget := calleeResidualBudget }
        cacheTable := calleeInvariant.1.2.1 }
      have declarationNameEq :
          site.sourceDeclaration.name = site.declaration :=
        declarationName_of_findDecl? site.declarationFound
      have exactCallIndex :
          callIndex? sourceModule (.declaration site.declaration) =
            some generatedRow.targetFunctionIndex := by
        simpa [declarationNameEq] using generatedRow.callIndexEq
      rw [exactCallIndex] at callFound
      have functionIndexEq :
          generatedRow.targetFunctionIndex = functionIndex :=
        Option.some.inj callFound
      subst functionIndex
      obtain ⟨updated, targetSet, _⟩ :=
        invariant.1.1.1.1.2.2.1.set?
          (nextRuntime := nextRuntime)
          (nextEnv := bind sourceEnv decl.fvarId sourceValue)
          (nextStore := afterCall)
          (nextWitness := resultWitness)
          (physical := physical) resultFound
      have callerResult := calleeResult.ofRefines site.calleeResultRefines
      have factsTransfer :
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId) := by
        simp [Fir.Wasm.reuseCapacityLetFacts?, site.valueEq]
      obtain ⟨callStep, externalsPreserved, hostDescriptorsPreserved,
          witnessDescriptorsPreserved, producedTransfer, nextBaseInvariant⟩ :=
        invariant.1.1.ofDirectDeclarationCallExact stepFits sourceStep
          resultFound resultKindAt assembled callerResult.declaration targetSet
          factsTransfer
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst nextFacts
      have nextEntry :
          ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
            afterCall entryWitness resultWitness :=
        invariant.2.step
          callerResult.declaration.capacityPreserving.witnessTransport
          callerResult.declaration.capacityPreserving.capacityTransport
          callerResult.declaration.ordinaryTransport
          callerResult.declaration.externalsPreserved
          callerResult.declaration.toClosureTablesTransport
      have nextClosureTables : ClosureTablesAgree afterCall resultWitness :=
        callerResult.declaration.toClosureTablesTransport.agree invariant.1.2.2
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals)
            entryRuntime entryStore entryWitness
            (eraseReuseCapacityFact facts decl.fvarId)
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) afterCall updated
            resultWitness := by
        have budgetEq :
            stepCost + continuationCost + slack - stepCost =
              continuationCost + slack := by
          omega
        refine ⟨⟨?_, callerResult.cacheTable, nextClosureTables⟩, nextEntry⟩
        simpa only [budgetEq] using nextBaseInvariant
      obtain ⟨resultStore, resultLocals, finalWitness, resultPhysical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        continuedIH row continuationAdapted continuationInvariant
      subst targetCode
      exact ⟨resultStore, resultLocals, finalWitness, resultPhysical,
        codeWP_callLet expectedCompiled valueAdapted resultFound callStep
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @lazyLet context sourceRuntime sourceEnv decl continuation nextRuntime
      sourceValue stepCost facts nextFacts expectedResult resultFacts
      resultRuntime resultEnv resultValue continuationCost path supported
      sourceStep transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted,
          resultFound, targetEq⟩ :=
        CodeAdapted.let_eq codeAdapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits : stepCost ≤ (stepCost + continuationCost) + slack :=
        by omega
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, producedTransfer, nextInvariant⟩ :=
        operationLaws.lazy row supported stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              sourceExternals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        have budgetEq :
            stepCost + continuationCost + slack - stepCost =
              continuationCost + slack := by
          omega
        simpa only [budgetEq] using nextInvariant
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih row continuationAdapted continuationInvariant
      subst targetCode
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_lazyLet valueCompiled valueAdapted resultFound step
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @caseOf context sourceRuntime sourceEnv cases selected expectedResult facts
      resultFacts resultRuntime resultEnv resultValue requiredBytes supported
      sourceStep continued ih =>
      obtain ⟨selectedTarget, selectedAdapted, _selected, lift⟩ :=
        operationLaws.caseOf row supported sourceStep
          invariant.1.stateRelated.stateRelated codeAdapted
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih row selectedAdapted invariant
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        lift [] (ExactReturnControlPost resultStore physical)
          (by
            intro continuation returned
            subst continuation
            rfl)
          continuationWP,
        resultInvariant, failureClear, valueRelated⟩
  | @effect context sourceRuntime sourceEnv code continuation nextRuntime
      expectedResult facts resultFacts resultRuntime resultEnv resultValue
      requiredBytes supported sourceStep continued ih =>
      obtain ⟨targetRest, nextStore, nextWitness, continuationAdapted, step,
          _externalsPreserved, nextInvariant⟩ :=
        operationLaws.effect row facts supported sourceStep
          invariant.1.stateRelated.stateRelated invariant codeAdapted
      obtain ⟨resultStore, resultLocals, resultWitness, physical,
          continuationWP, resultInvariant, failureClear, valueRelated⟩ :=
        ih row continuationAdapted nextInvariant
      exact ⟨resultStore, resultLocals, resultWitness, physical,
        codeWP_effect step continuationWP, resultInvariant, failureClear,
        valueRelated⟩

/--
Recursive semantic obligation for compiler-generated internal declarations.

The dynamic index is a finite hereditary source derivation. The static row is
selected from the production lowering/adaptation pipeline, while the entry
frame and parameters are the ordinary concrete declaration interface. No
target execution or translation certificate occurs in the premise.
-/
def DirectHereditaryGeneratedDeclarationInduction
    (program : Fir.LeanIR.ImpureProgram)
    (sourceModule : Fir.Wasm.Module)
    (target : AdaptedModule)
    (hosts : ResolvedHosts)
    (sourceExternals : ExternalImpl)
    (DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop)
    (ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop)
    (LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState →
          Value → Nat → Prop)
    (CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop)
    (EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate) : Prop :=
  ∀ {declaration : LCNF.Decl .impure}
      {context : Fir.Wasm.Context}
      {sourceCode : LCNF.Code .impure}
      {sourceFunction : Fir.Wasm.Function}
      {resultKind : AbiKind}
      (row : ConcreteGeneratedInternalDeclaration program declaration context
        sourceCode sourceModule sourceFunction target)
      (_resultClassified :
        Fir.Wasm.abiKind? declaration.type = .ok (some resultKind))
      {resultFacts : ReuseCapacityFacts}
      {sourceRuntime resultRuntime : RuntimeState}
      {sourceEnv resultEnv : Env}
      {resultValue : Value} {requiredBytes : Nat}
      (_evaluation :
        ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
          DirectSupported ExternalSupported LazySupported CaseSupported
          EffectSupported directLetAllocationCost context resultKind []
          sourceRuntime sourceEnv sourceCode resultFacts resultRuntime resultEnv
          resultValue requiredBytes)
      {initial : Wasm.Store Host}
      {initialWitness : RefinementWitness}
      {parameters : List Wasm.Value},
    ConcreteReuseCapacityCacheFrame sourceModule sourceFunction sourceExternals
          [] requiredBytes sourceRuntime sourceEnv initial
          (row.targetFunction.toLocals parameters.reverse) initialWitness →
      parameters.length = row.targetFunction.numParams →
        ∃ resultStore resultWitness physical,
          BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
            sourceModule sourceFunction target.wasmModule hosts.env
            sourceExternals sourceRuntime resultRuntime sourceEnv sourceCode
            row.targetFunction row.targetFunctionIndex initial resultStore
            initialWitness resultWitness parameters resultKind resultValue
            physical requiredBytes

/--
Production generated-row operation laws close the recursive declaration
induction constructively.

The proof follows the finite hereditary source tree. At a direct named call,
the nested induction hypothesis supplies the callee declaration package; the
compiler equations select its exact generated row and numeric call target.
No module-wide target theorem, execution certificate, or termination premise
is assumed.
-/
theorem DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws
    {program : Fir.LeanIR.ImpureProgram}
    {sourceModule : Fir.Wasm.Module}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState → Value →
          Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adaptedModule : FirTalos.adapt sourceModule = .ok target)
    (operationLaws :
      DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
        sourceExternals DirectSupported ExternalSupported LazySupported
        CaseSupported EffectSupported) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals DirectSupported ExternalSupported LazySupported
      CaseSupported EffectSupported := by
  intro declaration context sourceCode sourceFunction resultKind row
    resultClassified resultFacts sourceRuntime resultRuntime sourceEnv resultEnv
    resultValue requiredBytes evaluation initial initialWitness parameters
    invariant parameterCount
  have initialEntry :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals)
        sourceRuntime initial initialWitness [] (requiredBytes + 0)
        sourceRuntime sourceEnv initial
        (row.targetFunction.toLocals parameters.reverse) initialWitness := by
    exact ⟨by simpa using invariant,
      ReuseCapacityCodeEntryTransports.refl sourceRuntime initial
        initialWitness⟩
  obtain ⟨resultStore, resultLocals, resultWitness, physical, exactWP,
      resultInvariant, failureClear, valueRelated⟩ :=
    codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_generated
      namesUnique lowered adaptedModule operationLaws row evaluation
      row.bodyAdapted initialEntry
  have body :
      DeclarationBodyWP context sourceModule sourceFunction target.wasmModule
        hosts.env sourceRuntime sourceEnv sourceCode row.targetFunction initial
        resultStore initialWitness parameters physical := by
    refine ⟨parameterCount, row.singleResult, fun callerTail => ?_⟩
    apply exactWP.conseq
    intro continuation returned
    subst continuation
    simp [ConcreteFunctionBodyPost, ExactReturnPost, row.singleResult,
      ← parameterCount]
  have successful :
      SuccessfulDeclaration context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals sourceRuntime resultRuntime
        sourceEnv sourceCode row.targetFunction row.targetFunctionIndex initial
        resultStore initialWitness resultWitness parameters resultKind
        resultValue physical := {
    sourceResult := evaluation.sourceResult
    notImport := row.notImport
    functionFound := row.targetFunctionFound
    body
    runtimeRelated := resultInvariant.1.stateRelated.stateRelated.1
    failureClear
    valueRelated }
  have capacityPreserving :
      CapacityPreservingSuccessfulDeclaration context sourceModule
        sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode row.targetFunction
        row.targetFunctionIndex initial resultStore initialWitness resultWitness
        parameters resultKind resultValue physical := {
    successful
    witnessTransport := resultInvariant.2.witness
    capacityTransport := resultInvariant.2.capacity }
  have residualBudget :
      ∀ {remainingBytes : Nat},
        requiredBytes ≤ remainingBytes →
          initial.host.runtime.heap.AddressSpaceBudget remainingBytes →
            resultStore.host.runtime.heap.AddressSpaceBudget
              (remainingBytes - requiredBytes) := by
    intro remainingBytes stepFits budget
    let slack := remainingBytes - requiredBytes
    have budgetEq : requiredBytes + slack = remainingBytes := by
      simp [slack, Nat.add_sub_of_le stepFits]
    have slackFrame :
        ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
          sourceExternals [] (requiredBytes + slack) sourceRuntime sourceEnv
          initial (row.targetFunction.toLocals parameters.reverse)
          initialWitness :=
      invariant.withBudget (by simpa [budgetEq] using budget)
    have slackEntry :
        ReuseCapacityEntryRelativeFrame
          (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
            sourceExternals)
          sourceRuntime initial initialWitness [] (requiredBytes + slack)
          sourceRuntime sourceEnv initial
          (row.targetFunction.toLocals parameters.reverse) initialWitness :=
      ⟨slackFrame,
        ReuseCapacityCodeEntryTransports.refl sourceRuntime initial
          initialWitness⟩
    obtain ⟨slackStore, slackLocals, slackWitness, slackPhysical, slackWP,
        slackInvariant, _, _⟩ :=
      codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_generated
        namesUnique lowered adaptedModule operationLaws row evaluation
        row.bodyAdapted slackEntry
    have resultEq := exactWP.exactReturn_unique slackWP
    rw [resultEq.1]
    simpa [slack] using slackInvariant.1.budget
  exact ⟨resultStore, resultWitness, physical, {
    declaration := {
      toClosureTablesTransport := resultInvariant.2.toClosureTablesTransport
      capacityPreserving
      ordinaryTransport := resultInvariant.2.ordinary
      externalsPreserved := resultInvariant.2.externals
      residualBudget }
    cacheTable := resultInvariant.1.2.1 }⟩

/--
One compiler-generated lazy layer is derived from a nested source initializer
derivation, not from a caller-supplied target theorem.

The nested derivation is discharged by the already-constructed hereditary
generated-declaration theorem for the initializer fragment. Production
lowering and adaptation select the exact nullary callee row and numeric call
index; the caller frame is re-indexed at the initializer's source-selected
cost. For exact non-heap result kinds, publication ordinaryness follows from
the callee's returned physical-value refinement.
-/
theorem
    ConcreteSupportedFunction.internalNonHeapHereditaryLazyRuntimeRefines_entryRelativeCache
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {InitializerLazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState →
          Value → Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    (spec : ConcreteSupportedFunction program context callerCode sourceModule
      callerFunction target hosts)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (declarations :
      DirectHereditaryGeneratedDeclarationInduction program sourceModule target
        hosts sourceExternals DirectSupported ExternalSupported
        InitializerLazySupported CaseSupported EffectSupported)
    {entryRuntime : RuntimeState}
    {entryStore : Wasm.Store Host}
    {entryWitness : RefinementWitness} :
    ReuseCapacityLazyLetRuntimeRefinesWithCost context sourceModule
      callerFunction labels target.wasmModule hosts.env sourceExternals
      (LazyCacheInternalHereditarySupported sourceExternals DirectSupported
        ExternalSupported InitializerLazySupported CaseSupported
        EffectSupported context)
      (ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule callerFunction
          sourceExternals)
        entryRuntime entryStore entryWitness) := by
  intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
    sourceValue valueCode targetValue initial locals resultIndex remainingBytes
    stepCost initialWitness supported stepFits invariant sourceStep
    valueCompiled valueAdapted resultFound
  rcases invariant with ⟨cacheInvariant, entryTransports⟩
  cases supported with
  | hit call =>
      obtain ⟨nextStore, nextLocals, nextWitness, physical, step, transfer,
          nextCache⟩ :=
        BudgetedCapacityPreservingLazyStep.hit_of_compiler context sourceModule
          callerFunction labels target.wasmModule hosts.env sourceExternals
          call spec.localsAligned generated sourceStep cacheInvariant
          valueCompiled valueAdapted resultFound rfl
      have ordinary :
          OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
        SourceLazyLetResult.hit_ordinaryTransport_of_supported call sourceStep
      obtain ⟨simulates, externalsPreserved, hostDescriptorsPreserved,
          witnessDescriptorsPreserved, nextTransfer, nextCacheInvariant⟩ :=
        cacheInvariant.ofLazyCacheResult stepFits step (fun _ => nextCache)
          resultFound transfer
      have nextEntry :
          ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
            nextStore entryWitness nextWitness :=
        entryTransports.step step.witnessTransport step.capacityTransport
          ordinary step.externalsPreserved step.toClosureTablesTransport
      exact ⟨nextStore, nextLocals, nextWitness,
        eraseReuseCapacityFact facts decl.fvarId, simulates,
        externalsPreserved, hostDescriptorsPreserved,
        witnessDescriptorsPreserved, nextTransfer,
        ⟨nextCacheInvariant, nextEntry⟩⟩
  | @miss sourceRuntime nextRuntime callRuntime sourceEnv calleeResultEnv decl
      continuation sourceValue stepCost declaration sourceDeclaration
      resultKind calleeCode calleeFunction calleeResultFacts call loweredRow
      resultClassified notObject notTObject calleeEvaluation =>
      rcases call with
        ⟨⟨valueEq, kindEq, targetEq, paramsEq, resultCompiled⟩, bodyEq⟩
      have programEq : context.program = program := spec.contextProgram
      subst program
      obtain ⟨generatedRow⟩ :=
        ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
          rfl contextCaches spec.programNamesUnique spec.lowered
          spec.adapted targetEq loweredRow resultClassified
      have parametersEmpty : sourceDeclaration.params = #[] :=
        Array.isEmpty_iff.mp paramsEq
      have calleeFrame :=
        cacheInvariant.generatedNullaryCalleeEntryAtCost generatedRow
          parametersEmpty stepFits
      have declarationNameEq : sourceDeclaration.name = declaration :=
        declarationName_of_findDecl? targetEq
      have exactCallIndex :
          callIndex? sourceModule (.declaration declaration) =
            some generatedRow.targetFunctionIndex := by
        simpa [declarationNameEq] using generatedRow.callIndexEq
      have hereditary :
          LazyCacheInternalHereditaryInduction context sourceModule
            target.wasmModule hosts.env sourceExternals sourceRuntime
            declaration calleeCode resultKind initial initialWitness
            sourceValue stepCost := by
        intro declarationId declarationCall
        rw [exactCallIndex] at declarationCall
        have declarationIdEq := Option.some.inj declarationCall
        subst declarationId
        obtain ⟨afterCall, callWitness, physical, calleeResult⟩ :=
          declarations generatedRow resultClassified calleeEvaluation
            calleeFrame
            (generatedRow.targetParameterCount_nullary parametersEmpty)
        exact ⟨loweredRow.context, calleeFunction,
          generatedRow.targetFunction, callRuntime, afterCall, callWitness,
          physical, loweredRow.contextsCoherent rfl rfl, calleeResult,
          trivial⟩
      have missSupported :
          LazyCacheInternalMissSupported context decl declaration
            sourceDeclaration resultKind calleeCode :=
        .intro (.intro valueEq kindEq targetEq paramsEq resultCompiled) bodyEq
      have publication :
          LazyCacheInternalPublicationInduction context sourceModule
            target.wasmModule hosts.env sourceExternals facts sourceRuntime
            sourceEnv declaration calleeCode resultKind initial initialWitness
            sourceValue stepCost :=
        LazyCacheInternalHereditaryInduction.publication_of_nonHeapKind
          hereditary notObject notTObject
      obtain ⟨nextStore, nextLocals, nextWitness, physical, step, transfer,
          nextCache⟩ :=
        BudgetedCapacityPreservingLazyStep.miss_of_supportedFunctionCompiler
          context sourceModule callerFunction labels target hosts spec
          sourceExternals missSupported
          generated sourceStep cacheInvariant valueCompiled valueAdapted
          resultFound
          (LazyCacheInternalPublicationInduction.toMissInduction
            (resultId := decl.fvarId) publication)
      have ordinary :
          OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
        SourceLazyLetResult.miss_ordinaryTransport_of_internalCompiler_nonHeap
          (stepCost := stepCost) missSupported
          sourceStep valueCompiled valueAdapted hereditary notObject notTObject
      obtain ⟨simulates, externalsPreserved, hostDescriptorsPreserved,
          witnessDescriptorsPreserved, nextTransfer, nextCacheInvariant⟩ :=
        cacheInvariant.ofLazyCacheResult stepFits step (fun _ => nextCache)
          resultFound transfer
      have nextEntry :
          ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
            nextStore entryWitness nextWitness :=
        entryTransports.step step.witnessTransport step.capacityTransport
          ordinary step.externalsPreserved step.toClosureTablesTransport
      exact ⟨nextStore, nextLocals, nextWitness,
        eraseReuseCapacityFact facts decl.fvarId, simulates,
        externalsPreserved, hostDescriptorsPreserved,
        witnessDescriptorsPreserved, nextTransfer,
        ⟨nextCacheInvariant, nextEntry⟩⟩

/-- Production operation laws with one hereditary lazy layer.

Every generated row receives the same validated cache table through context
coherence. Its hit/miss law invokes the no-lazy generated-declaration theorem
only for the finite initializer derivation stored in the source admission;
ordinary direct callees remain recursive in the enclosing one-layer family.
-/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal_effects_oneLazy
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (contextCaches :
      rootContext.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl)
    (generated : LazyCacheGeneratedEnvironment rootContext sourceModule) :
    DirectHereditaryGeneratedOperationLaws program sourceModule target hosts
      sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun context => PureExternalSupported context sourceExternals)
      (fun context =>
        ProductionHereditaryLazySupported sourceExternals context)
      (fun context => ProductionCasesSupported context)
      (fun context =>
        OwnershipTagAndAllFieldMutationEffectSupported context) := by
  have initializerDeclarations :
      DirectHereditaryGeneratedDeclarationInduction program sourceModule target
        hosts sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun context => ProductionCasesSupported context)
        (fun context =>
          OwnershipTagAndAllFieldMutationEffectSupported context) :=
    DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws
      spec.programNamesUnique spec.lowered spec.adapted
      (spec.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal_effects
        sourceExternals)
  constructor
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    exact
      (row.toSupportedFunction spec).reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
        sourceExternals
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness
    have contexts : DeclarationContextsCoherent rootContext context := {
      program := spec.contextProgram.trans row.contextProgram.symm
      cachedDeclarations := contextCaches.trans row.contextCaches.symm }
    unfold ReuseCapacityLazyLetRuntimeRefinesWithCost
    intro path facts sourceRuntime nextRuntime sourceEnv decl continuation
      sourceValue valueCode targetValue initial locals resultIndex
      remainingBytes stepCost witness supported stepFits invariant sourceStep
      valueCompiled valueAdapted resultFound
    exact
      (row.toSupportedFunction spec).internalNonHeapHereditaryLazyRuntimeRefines_entryRelativeCache
        (labels := []) (entryRuntime := entryRuntime)
        (entryStore := entryStore) (entryWitness := entryWitness)
        row.contextCaches (generated.ofCoherent contexts)
        initializerDeclarations supported stepFits invariant sourceStep
        valueCompiled valueAdapted resultFound
  · intro declaration context sourceCode sourceFunction row
    exact (row.toSupportedFunction spec).caseRuntimeRefines_productionCases
  · intro declaration context sourceCode sourceFunction row entryRuntime
      entryStore entryWitness facts
    exact
      (row.toSupportedFunction spec).effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache
        sourceExternals

/-- Generated declarations with direct calls, pure externals, production
effects/cases, and one hereditary lazy layer satisfy the recursive declaration
contract from source evaluation and the production compiler/runtime laws. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal_effects_oneLazy
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (contextCaches :
      rootContext.cachedDeclarations =
        Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl)
    (generated : LazyCacheGeneratedEnvironment rootContext sourceModule) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun context => PureExternalSupported context sourceExternals)
      (fun context =>
        ProductionHereditaryLazySupported sourceExternals context)
      (fun context => ProductionCasesSupported context)
      (fun context =>
        OwnershipTagAndAllFieldMutationEffectSupported context) :=
  DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws
    spec.programNamesUnique spec.lowered spec.adapted
    (spec.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal_effects_oneLazy
      contextCaches sourceExternals generated)

/-- Compiler-generated declarations in the direct/no-calls fragment satisfy
the recursive declaration contract solely from the production operation
theorems and the successful lowering/adaptation pipeline. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_noCalls
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun _ => NoReuseCapacityExternalsSupported)
      (fun _ => NoReuseCapacityLazySupported)
      (fun _ => DefaultOnlyCaseSupported)
      (fun _ => NoEffectsSupported) :=
  DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws
    spec.programNamesUnique spec.lowered spec.adapted
    (spec.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_noCalls
      sourceExternals)

/-- Compiler-generated declarations with pure external calls satisfy the
recursive declaration contract from the production operation theorems and
the successful lowering/adaptation pipeline alone. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun context => PureExternalSupported context sourceExternals)
      (fun _ => NoReuseCapacityLazySupported)
      (fun _ => DefaultOnlyCaseSupported)
      (fun _ => NoEffectsSupported) :=
  DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws
    spec.programNamesUnique spec.lowered spec.adapted
    (spec.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal
      sourceExternals)

/-- Generated declarations with pure externals, supported no-result runtime
effects, and production cases satisfy the recursive declaration contract
directly from the operation laws. -/
theorem
    ConcreteSupportedExport.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal_effects
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program rootContext rootCode sourceModule
      rootFunction target hosts exportName)
    (sourceExternals : ExternalImpl) :
    DirectHereditaryGeneratedDeclarationInduction program sourceModule target
      hosts sourceExternals
      (fun context => ReuseBudgetedDirectSupported context)
      (fun context => PureExternalSupported context sourceExternals)
      (fun _ => NoReuseCapacityLazySupported)
      (fun context => ProductionCasesSupported context)
      (fun context => OwnershipTagAndAllFieldMutationEffectSupported context) :=
  DirectHereditaryGeneratedDeclarationInduction.ofOperationLaws
    spec.programNamesUnique spec.lowered spec.adapted
    (spec.directHereditaryGeneratedOperationLaws_reuseBudgetedDirect_pureExternal_effects
      sourceExternals)

/--
The production named-call implementation consumes the hereditary source
payload directly.

The exact lowerer row carried by the source derivation is recovered in the
real module, and `callIndexEq` identifies it with the adapter-selected numeric
target. The recursive declaration premise is asked only for the nested finite
source derivation at the generated callee entry; callers provide neither an
index equation nor a target execution certificate.
-/
theorem
    DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {sourceExternals : ExternalImpl}
    {DirectSupported :
      Fir.Wasm.Context → ReuseCapacityFacts → LCNF.LetDecl .impure → Prop}
    {ExternalSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.LetDecl .impure →
        LCNF.Code .impure → RuntimeState → Value → Nat → Prop}
    {LazySupported :
      Fir.Wasm.Context → LazyCachePath → RuntimeState → Env →
        LCNF.LetDecl .impure → LCNF.Code .impure → RuntimeState →
          Value → Nat → Prop}
    {CaseSupported :
      Fir.Wasm.Context → RuntimeState → Env → LCNF.Cases .impure →
        LCNF.Code .impure → Prop}
    {EffectSupported : Fir.Wasm.Context → EffectSupportedPredicate}
    (contextProgram : context.program = program)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (namesUnique : program.NamesUnique)
    (lowered : Fir.Wasm.lowerSupported program = .ok sourceModule)
    (adapted : FirTalos.adapt sourceModule = .ok target)
    (callerLocalsAligned : LocalLayoutAligned context callerFunction)
    (declarations :
      DirectHereditaryGeneratedDeclarationInduction program sourceModule target
        hosts sourceExternals DirectSupported ExternalSupported LazySupported
        CaseSupported EffectSupported) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      callerFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        DirectSupported ExternalSupported LazySupported CaseSupported
        EffectSupported directLetAllocationCost context) := by
  subst program
  intro facts sourceRuntime nextRuntime sourceEnv decl continuation sourceValue
    valueCode targetValue initial locals resultIndex remainingBytes stepCost
    initialWitness supported stepFits sourceStep invariant valueCompiled
    valueAdapted resultFound
  rcases supported with ⟨site, loweredRow, calleeEvaluation⟩
  have expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (site.argumentCode ++
          [.call (.declaration site.declaration)]) := by
    simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind, site.valueEq,
      site.kindEq, site.argumentsCompiled, site.declarationFound,
      site.nonCached, Bind.bind, Except.bind, pure, Except.pure]
  have valueCodeEq :
      valueCode =
        site.argumentCode ++ [.call (.declaration site.declaration)] := by
    rw [expectedCompiled] at valueCompiled
    exact (Except.ok.inj valueCompiled).symm
  subst valueCode
  obtain ⟨targetArguments, functionIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  subst targetValue
  obtain ⟨physicalArgs, argumentsReady, _, argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs callerLocalsAligned
      site.argumentsCompiled argumentsAdapted site.argumentsEvaluated
      invariant.1.1.1.1.stateRelated
  have assembled :
      ClosureArgumentAssembly target.wasmModule hosts.env targetArguments
        physicalArgs initial locals :=
    ClosureArgumentAssembly.ofConstructorArgsReady argumentsReady
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    callerLocalsAligned site.resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  have declarationFound :
      context.program.findDecl? site.declaration =
        some site.sourceDeclaration :=
    site.declarationFound
  have resultClassified :
      Fir.Wasm.abiKind? site.sourceDeclaration.type =
        .ok (some site.calleeResultKind) :=
    abiKind?_eq_ok_some_of_directAbiKind?_eq_some site.calleeResult
  obtain ⟨generatedRow⟩ :=
    ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
      rfl contextCaches namesUnique lowered adapted declarationFound
      loweredRow resultClassified
  have calleeFrame :=
    invariant.generatedDirectCalleeEntryAtCost site generatedRow
      argumentsRelated stepFits
  obtain ⟨afterCall, resultWitness, physical, calleeResult⟩ :=
    declarations generatedRow resultClassified calleeEvaluation
      (by simpa using calleeFrame)
      (generatedRow.targetParameterCount site argumentsRelated)
  have declarationNameEq :
      site.sourceDeclaration.name = site.declaration :=
    declarationName_of_findDecl? site.declarationFound
  have exactCallIndex :
      callIndex? sourceModule (.declaration site.declaration) =
        some generatedRow.targetFunctionIndex := by
    simpa [declarationNameEq] using generatedRow.callIndexEq
  rw [exactCallIndex] at callFound
  have functionIndexEq : generatedRow.targetFunctionIndex = functionIndex :=
    Option.some.inj callFound
  subst functionIndex
  obtain ⟨updated, targetSet, _⟩ :=
    invariant.1.1.1.2.2.1.set?
      (nextRuntime := nextRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := afterCall)
      (nextWitness := resultWitness)
      (physical := physical) resultFound
  refine
    ⟨loweredRow.context, _, site.calleeEnv, site.calleeCode,
      generatedRow.targetFunction, generatedRow.targetFunctionIndex,
      targetArguments, afterCall, updated, resultWitness, physicalArgs,
      site.resultKind, physical, loweredRow.contextsCoherent rfl rfl,
      rfl, resultKindAt, assembled,
      calleeResult.ofRefines site.calleeResultRefines, targetSet, ?_⟩
  simp [Fir.Wasm.reuseCapacityLetFacts?, site.valueEq]

/-- Saturated named calls in the direct/no-calls fragment are implemented by
the generated callee selected by the production compiler. The only additional
root-context fact identifies the compiler's canonical lazy-cache name table;
all recursive target correctness is derived internally. -/
theorem
    ConcreteSupportedExport.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_noCalls
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      sourceFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun _ => NoReuseCapacityExternalsSupported)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context) :=
  DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler
    spec.contextProgram contextCaches spec.programNamesUnique spec.lowered
    spec.adapted spec.localsAligned
    (spec.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_noCalls
      sourceExternals)

/-- Saturated named calls in the direct/pure-external fragment are implemented
by the exact generated callee. Recursive callees may themselves execute any
admitted pure external operation; their target behavior is still derived by
the generated-declaration induction. -/
theorem
    ConcreteSupportedExport.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_pureExternal
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      sourceFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context) :=
  DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler
    spec.contextProgram contextCaches spec.programNamesUnique spec.lowered
    spec.adapted spec.localsAligned
    (spec.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal
      sourceExternals)

/-- Saturated named calls in the direct/pure-external/effect/case fragment
execute the exact compiler-generated callee. Recursive callees may use the
same ownership, mutation, and production case operations, with their
correctness derived internally from the hereditary declaration induction. -/
theorem
    ConcreteSupportedExport.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_pureExternal_effects
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      sourceFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun context => ProductionCasesSupported context)
        (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost context) :=
  DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler
    spec.contextProgram contextCaches spec.programNamesUnique spec.lowered
    spec.adapted spec.localsAligned
    (spec.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal_effects
      sourceExternals)

/-- Saturated named calls in the production fragment with one lazy-cache
layer execute the exact compiler-generated callee. Ordinary recursive callees
may use the same lazy family; a cache-miss initializer is discharged from its
finite source derivation by the no-nested-lazy declaration induction. -/
theorem
    ConcreteSupportedExport.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_pureExternal_effects_oneLazy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (sourceExternals : ExternalImpl)
    (generated : LazyCacheGeneratedEnvironment context sourceModule) :
    DirectDeclarationCallImplementationWithCache context sourceModule
      sourceFunction labels target.wasmModule hosts.env sourceExternals
      (ReuseCapacityDirectHereditaryCallSupported sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun context =>
          ProductionHereditaryLazySupported sourceExternals context)
        (fun context => ProductionCasesSupported context)
        (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost context) :=
  DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler
    spec.contextProgram contextCaches spec.programNamesUnique spec.lowered
    spec.adapted spec.localsAligned
    (spec.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal_effects_oneLazy
      contextCaches sourceExternals generated)

/-- Certificate-free partial correctness for a generated root export whose
finite source derivation contains supported direct operations and recursively
supported saturated named calls, but no external, lazy, or no-result effects.

The theorem returns the exact concrete execution together with resource,
ownership, immutable-table, and whole-cache transports. Nested callees are
proved by the compiler-generated declaration induction above; the caller
does not provide their target executions. -/
theorem
    ConcreteSupportedExport.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_noCalls
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun _ => NoReuseCapacityExternalsSupported)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical
        requiredBytes := by
  exact
    spec.toSupportedDeclaration
      |>.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates
        evaluation invariant
        (spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
          sourceExternals)
        reuseCapacityExternalLetRuntimeRefinesWithCost_noExternals
        (DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative
          (spec.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_noCalls
            contextCaches sourceExternals))
        reuseCapacityLazyLetRuntimeRefinesWithCost_noLazy
        caseRuntimeRefines_defaultOnly
        (fun _ => effectRuntimeRefines_noEffects)
        parameterCount

/-- Public partial-correctness corollary for the first recursive production
fragment.

If the source export has the finite hereditary evaluation described above,
then invoking the compiler-selected Wasm export terminates with a concrete
runtime and physical result that refine the exact source runtime and value.
The proof is derived from lowering, adaptation, generated declaration rows,
and the individual runtime-operation theorems; no target run is assumed. -/
theorem
    ConcreteSupportedExport.correct_reuseBudgetedDirect_noCalls
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun _ => NoReuseCapacityExternalsSupported)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  obtain ⟨resultStore, resultWitness, physical, result⟩ :=
    spec.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_noCalls
      contextCaches evaluation invariant parameterCount
  have successful := result.declaration.capacityPreserving.successful
  exact ⟨successful.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    successful.terminatesWith callerTail⟩

/-- Certificate-free declaration correctness for recursively generated direct
code that may execute the complete admitted pure `Nat`/`Int`/scalar external
family.  Both external steps and recursive named calls are discharged from
the production compiler/runtime laws. -/
theorem
    ConcreteSupportedExport.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_pureExternal
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical
        requiredBytes := by
  exact
    spec.toSupportedDeclaration
      |>.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates
        evaluation invariant
        (spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
          sourceExternals)
        (spec.reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
          sourceExternals)
        (DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative
          (spec.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_pureExternal
            contextCaches sourceExternals))
        reuseCapacityLazyLetRuntimeRefinesWithCost_noLazy
        caseRuntimeRefines_defaultOnly
        (fun _ => effectRuntimeRefines_noEffects)
        parameterCount

/-- Public partial correctness for the recursive direct/pure-external
production fragment.

If the LCNF export has a finite hereditary evaluation, the compiler-selected
Wasm export terminates with the same semantic result and a related concrete
runtime.  No target execution, translation certificate, or recursive callee
correctness theorem is supplied by the caller. -/
theorem
    ConcreteSupportedExport.correct_reuseBudgetedDirect_pureExternal
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun _ => DefaultOnlyCaseSupported)
        (fun _ => NoEffectsSupported)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  obtain ⟨resultStore, resultWitness, physical, result⟩ :=
    spec.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_pureExternal
      contextCaches evaluation invariant parameterCount
  have successful := result.declaration.capacityPreserving.successful
  exact ⟨successful.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    successful.terminatesWith callerTail⟩

/-- Certificate-free declaration correctness for recursively generated code
with direct operations, pure externals, the complete supported no-result
ownership/tag/field-mutation family, and production cases. -/
theorem
    ConcreteSupportedExport.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_pureExternal_effects
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun context => ProductionCasesSupported context)
        (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical
        requiredBytes := by
  exact
    spec.toSupportedDeclaration
      |>.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates
        evaluation invariant
        (spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
          sourceExternals)
        (spec.reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
          sourceExternals)
        (DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative
          (spec.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_pureExternal_effects
            contextCaches sourceExternals))
        reuseCapacityLazyLetRuntimeRefinesWithCost_noLazy
        spec.caseRuntimeRefines_productionCases
        (fun _ =>
          spec.effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache
            sourceExternals)
        parameterCount

/-- Public partial correctness for the recursive production fragment with
direct operations, pure externals, supported ownership/tag/field effects, and
default/object-constructor/scalar-`UInt8` cases.

For every finite hereditary LCNF evaluation in this fragment, the generated
Wasm export terminates with the same semantic result and a related concrete
runtime. The caller supplies no target run, translation certificate, or
recursive callee correctness theorem. -/
theorem
    ConcreteSupportedExport.correct_reuseBudgetedDirect_pureExternal_effects
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun _ => NoReuseCapacityLazySupported)
        (fun context => ProductionCasesSupported context)
        (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  obtain ⟨resultStore, resultWitness, physical, result⟩ :=
    spec.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_pureExternal_effects
      contextCaches evaluation invariant parameterCount
  have successful := result.declaration.capacityPreserving.successful
  exact ⟨successful.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    successful.terminatesWith callerTail⟩

/-- Certificate-free declaration correctness for the production fragment
with one lazy-cache layer.

A cache hit is executed directly from the related cache entry. On a miss, the
source admission contains the finite evaluation of the selected nullary
initializer; lowering and adaptation identify its actual generated row, and
the no-nested-lazy declaration induction derives its target execution. The
caller supplies neither a target execution nor a recursive correctness
theorem. -/
theorem
    ConcreteSupportedExport.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_pureExternal_effects_oneLazy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun context =>
          ProductionHereditaryLazySupported sourceExternals context)
        (fun context => ProductionCasesSupported context)
        (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ∃ resultStore resultWitness physical,
      BudgetedCapacityPreservingSuccessfulDeclarationWithCache context
        sourceModule sourceFunction target.wasmModule hosts.env sourceExternals
        sourceRuntime resultRuntime sourceEnv sourceCode spec.targetFunction
        spec.targetFunctionIndex initial resultStore initialWitness
        resultWitness parameters resultKind resultValue physical
        requiredBytes := by
  exact
    spec.toSupportedDeclaration
      |>.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates
        evaluation invariant
        (spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
          sourceExternals)
        (spec.reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
          sourceExternals)
        (DirectDeclarationCallImplementationWithCache.runtimeRefinesEntryRelative
          (spec.directDeclarationCallImplementationWithCache_reuseBudgetedDirect_pureExternal_effects_oneLazy
            contextCaches sourceExternals generated))
        (spec.toConcreteSupportedFunction.internalNonHeapHereditaryLazyRuntimeRefines_entryRelativeCache
          contextCaches generated
          (spec.directHereditaryGeneratedDeclarationInduction_reuseBudgetedDirect_pureExternal_effects
            sourceExternals))
        spec.caseRuntimeRefines_productionCases
        (fun _ =>
          spec.effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache
            sourceExternals)
        parameterCount

/-- Public partial correctness for the first production fragment containing
real lazy-cache hits and misses.

For every finite hereditary LCNF evaluation admitted by the one-layer lazy
family, invoking the generated Wasm export terminates with the same semantic
result and a related concrete runtime. Cache-miss initializer execution and
cache publication are consequences of the compiler/runtime proof, rather
than assumptions about the target. -/
theorem
    ConcreteSupportedExport.correct_reuseBudgetedDirect_pureExternal_effects_oneLazy
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction target hosts exportName)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    {sourceExternals : ExternalImpl}
    {resultKind : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityDirectHereditaryCodeEvaluates sourceExternals
        (fun context => ReuseBudgetedDirectSupported context)
        (fun context => PureExternalSupported context sourceExternals)
        (fun context =>
          ProductionHereditaryLazySupported sourceExternals context)
        (fun context => ProductionCasesSupported context)
        (fun context => OwnershipTagAndAllFieldMutationEffectSupported context)
        directLetAllocationCost context resultKind facts sourceRuntime sourceEnv
        sourceCode resultFacts resultRuntime resultEnv resultValue
        requiredBytes)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
        sourceExternals facts requiredBytes sourceRuntime sourceEnv initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (ReturnedObservation resultRuntime resultValue) ∧
      ConcreteExportTerminatesWith hosts.env target.wasmModule exportName
        initial (parameters ++ callerTail)
        (RefinedReturnPost resultRuntime resultValue resultKind callerTail) := by
  obtain ⟨resultStore, resultWitness, physical, result⟩ :=
    spec.budgetedDeclarationWithCache_of_reuseCapacityDirectHereditaryCodeEvaluates_reuseBudgetedDirect_pureExternal_effects_oneLazy
      contextCaches generated evaluation invariant parameterCount
  have successful := result.declaration.capacityPreserving.successful
  exact ⟨successful.sourceEvaluates, spec.targetFunctionIndex, spec.exported,
    successful.terminatesWith callerTail⟩

end FirTalos.Concrete
