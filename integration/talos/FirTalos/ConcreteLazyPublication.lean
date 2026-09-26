import FirTalos.ConcreteReuseCapacityCacheCorrectness

/-!
Facts-aware source transport for callee prefixes and complete internal misses.

Publication deliberately makes the returned ownership graph persistent. It
need not preserve ordinaryness at every heap location; it must preserve the
retained reuse-token facts of the caller. These lemmas compose the existing
callee and publication proofs at that narrower boundary. They do not change
the structured simulator's stronger declaration-entry transport invariant.
-/

namespace FirTalos.Concrete

open Lean Lean.Compiler Fir.Wasm Fir.LeanIR.Impure Fir.Wasm.Concrete
open FirTalos.Correctness

/-- A callee prefix preserves the suspended caller's retained-token facts.
The environment is the caller's fixed environment, not the callee's active
locals. Publishing unrelated heap graphs is allowed. This proof-side boundary
does not assert that arbitrary executions satisfy publication disjointness. -/
def ReuseTokenOrdinaryTransport (facts : ReuseCapacityFacts) (sourceEnv : Env)
    (before after : RuntimeState) : Prop :=
  ReuseTokenOrdinaryRel facts before sourceEnv →
    ReuseTokenOrdinaryRel facts after sourceEnv

theorem ReuseTokenOrdinaryTransport.refl
    (facts : ReuseCapacityFacts) (sourceEnv : Env) (runtime : RuntimeState) :
    ReuseTokenOrdinaryTransport facts sourceEnv runtime runtime :=
  fun ordinary => ordinary

/-- Prefixes compose at the same suspended caller, including prefixes that
themselves publish heap-valued lazy results. -/
theorem ReuseTokenOrdinaryTransport.trans
    {facts : ReuseCapacityFacts} {sourceEnv : Env}
    {before middle after : RuntimeState}
    (left : ReuseTokenOrdinaryTransport facts sourceEnv before middle)
    (right : ReuseTokenOrdinaryTransport facts sourceEnv middle after) :
    ReuseTokenOrdinaryTransport facts sourceEnv before after :=
  fun ordinary => right (left ordinary)

/-- Existing ordinary runtime-operation proofs provide the narrower caller
frame without modification. -/
theorem ReuseTokenOrdinaryTransport.ofOrdinaryPersistence
    {facts : ReuseCapacityFacts} {sourceEnv : Env}
    {before after : RuntimeState}
    (transport : OrdinaryPersistenceTransport before after) :
    ReuseTokenOrdinaryTransport facts sourceEnv before after :=
  fun ordinary => ordinary.transport transport

/-- Publication preserves a suspended caller when its tracked tokens are
outside the published ownership graph. The published root need not remain
ordinary; the premise concerns only the caller's retained locations. -/
theorem ReuseTokenOrdinaryTransport.ofPublicationDisjoint
    {facts : ReuseCapacityFacts} {sourceEnv : Env}
    {runtime : RuntimeState} {result : Value}
    (name : Name)
    (disjoint : ReuseTokenPublicationDisjoint facts runtime sourceEnv result) :
    ReuseTokenOrdinaryTransport facts sourceEnv runtime
      (runtime.setGlobal name result) := by
  intro ordinary tokenId available location cell tracked tokenLookup found
  apply ordinary.markPersistent_of_publicationDisjoint disjoint
    tokenId available location cell tracked tokenLookup
  simpa [RuntimeState.setGlobal] using found

/-- At return, erase the destination's old fact and bind the result using
only the suspended caller's facts-aware transport. -/
theorem ReuseTokenOrdinaryTransport.eraseBind
    {facts : ReuseCapacityFacts} {sourceEnv : Env}
    {before after : RuntimeState} {resultId : FVarId} {result : Value}
    (transport : ReuseTokenOrdinaryTransport facts sourceEnv before after) :
    ReuseTokenOrdinaryBindTransport facts resultId before after sourceEnv
      result := by
  intro ordinary
  exact (transport ordinary).eraseBind (OrdinaryPersistenceTransport.refl after)

/-- A facts-aware callee prefix and a facts-aware publication/binding step
compose without demanding all-location ordinaryness of the prefix. -/
theorem ReuseTokenOrdinaryBindTransport.precomposeRetained
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {before middle after : RuntimeState} {sourceEnv : Env} {result : Value}
    (calleePrefix : ReuseTokenOrdinaryTransport facts sourceEnv before middle)
    (publication : ReuseTokenOrdinaryBindTransport facts resultId middle after
      sourceEnv result) :
    ReuseTokenOrdinaryBindTransport facts resultId before after sourceEnv
      result :=
  fun ordinary => publication (calleePrefix ordinary)

/-- An ordinary callee prefix followed by facts-aware publication preserves
exactly the caller's retained facts after binding, without requiring the
published graph itself to remain ordinary. -/
theorem ReuseTokenOrdinaryBindTransport.precompose
    {facts : ReuseCapacityFacts} {resultId : FVarId}
    {before middle after : RuntimeState} {sourceEnv : Env} {result : Value}
    (beforePublication : OrdinaryPersistenceTransport before middle)
    (publication : ReuseTokenOrdinaryBindTransport facts resultId middle after
      sourceEnv result) :
    ReuseTokenOrdinaryBindTransport facts resultId before after sourceEnv
      result :=
  publication.precomposeRetained
    (ReuseTokenOrdinaryTransport.ofOrdinaryPersistence beforePublication)

/-- A retained token resolved through the existing concrete state relation
names an allocated source cell, hence precedes the next allocation frontier.
Ordinaryness alone would not suffice: it permits absent token locations. -/
theorem ReuseCapacityStateRelated.retainedToken_beforeNext
    {facts : ReuseCapacityFacts} {function : Fir.Wasm.Function}
    {runtime : RuntimeState} {env : Env} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    (related : ReuseCapacityStateRelated facts function runtime env store locals
      witness)
    {id : FVarId} {available location : Nat}
    (tracked : findReuseCapacityEvidence? facts id = some (.retainedAtLeast available))
    (tokenLookup : lookup env id = some (.reuseToken (some location))) :
    location < runtime.nextLocation := by
  obtain ⟨index, kind, lane, semantic, found, _, _, _, capacity⟩ :=
    related.2.resolve tracked
  rw [tokenLookup] at found
  cases Option.some.inj found
  cases capacity with
  | retainedToken value header owned minimum =>
    cases value with
    | reuseSome reference =>
      cases reference with
      | mapped mapped =>
        obtain ⟨cell, found, _⟩ := related.1.1.heap.concreteToSemantic _ _ mapped
        exact related.1.1.heap.locationsBeforeNext _ _ found

/-- A heap object without owned values has a singleton reachable graph.
This is a semantic object-shape fact, not a restriction on its ABI kind. -/
theorem reachable_eq_leafRoot
    {heap : Heap} {root location : Location} {cell : HeapCell}
    (found : findCell? heap root = some cell)
    (leaf : cell.object.ownedValues = #[])
    (reachable : Reachable heap [.object (.heap root)] location) :
    location = root := by
  induction reachable with
  | root member => simpa using member
  | child parentReachable childFound member reference ih =>
    subst_vars
    rw [found] at childFound
    cases Option.some.inj childFound
    simp [leaf] at member

/-- Fresh leaf allocation derives publication disjointness from the normal
entry relation. Neither freshness nor reachability separation is supplied by
the caller. Nonempty owned graphs require a separate ownership argument. -/
theorem ReuseTokenPublicationDisjoint.of_allocLeaf
    {facts : ReuseCapacityFacts} {function : Fir.Wasm.Function}
    {before after : RuntimeState} {env : Env} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    {object : HeapObject} {reference : ObjectRef}
    (related : ReuseCapacityStateRelated facts function before env store locals
      witness)
    (allocation : alloc before object false = (after, reference))
    (leaf : object.ownedValues = #[]) :
    ReuseTokenPublicationDisjoint facts after env (.object reference) := by
  cases allocation
  intro id available location tracked tokenLookup reachable
  have beforeNext := related.retainedToken_beforeNext tracked tokenLookup
  have rootOnly : location = before.nextLocation :=
    reachable_eq_leafRoot (cell := { object })
      (by simp [alloc, findCell?]) leaf reachable
  exact Nat.ne_of_lt beforeNext rootOnly

/-- Allocate and publish a fresh leaf, then bind its result, preserving the
saved caller's retained facts. The allocation and publication are actual
runtime operations; their graph separation is derived from entry refinement. -/
theorem ReuseTokenOrdinaryBindTransport.allocLeaf_setGlobal
    {facts : ReuseCapacityFacts} {function : Fir.Wasm.Function}
    {before after : RuntimeState} {env : Env} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    {object : HeapObject} {reference : ObjectRef}
    (related : ReuseCapacityStateRelated facts function before env store locals
      witness)
    (allocation : alloc before object false = (after, reference))
    (leaf : object.ownedValues = #[])
    (name : Name) (result : FVarId) :
    ReuseTokenOrdinaryBindTransport facts result before
      (after.setGlobal name (.object reference)) env (.object reference) :=
  (ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint name
    (.of_allocLeaf related allocation leaf)).precompose
      (alloc_ordinaryPersistenceTransport allocation)

/-- An allocation region owns no edge into the older heap. This local heap
property is independent of caller facts and is preserved by allocating objects
whose heap-valued fields stay in the region. It is not a source-machine invariant
or a claim that arbitrary initializer bodies respect this allocation policy. -/
def HeapRegionClosed (cutoff : Location) (heap : Heap) : Prop :=
  ∀ parent cell child, cutoff ≤ parent → findCell? heap parent = some cell →
    Value.object (.heap child) ∈ cell.object.ownedValues.toList → cutoff ≤ child

/-- Before the first allocation, the region above the source frontier is empty. -/
theorem ReuseCapacityStateRelated.freshRegionClosed
    {facts : ReuseCapacityFacts} {function : Fir.Wasm.Function}
    {runtime : RuntimeState} {env : Env} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    (related : ReuseCapacityStateRelated facts function runtime env store locals
      witness) :
    HeapRegionClosed runtime.nextLocation runtime.heap := by
  intro parent cell child above found member
  exact False.elim ((Nat.not_le_of_lt
    (related.1.1.heap.locationsBeforeNext _ _ found)) above)

/-- Allocation preserves the region using only its new object's immediate
owned fields; clients need not supply transitive reachability separation. -/
theorem HeapRegionClosed.alloc
    {cutoff : Location} {before after : RuntimeState}
    {object : HeapObject} {reference : ObjectRef} {persistent : Bool}
    (closed : HeapRegionClosed cutoff before.heap)
    (allocation : Fir.LeanIR.Impure.alloc before object persistent =
      (after, reference))
    (fields : ∀ child, Value.object (.heap child) ∈ object.ownedValues.toList →
      cutoff ≤ child) :
    HeapRegionClosed cutoff after.heap := by
  cases allocation
  intro parent cell child above found member
  by_cases atNew : before.nextLocation = parent
  · simp [Fir.LeanIR.Impure.alloc, findCell?, atNew] at found
    cases found
    exact fields _ member
  · simp [Fir.LeanIR.Impure.alloc, findCell?, atNew] at found
    exact closed _ _ _ above found member

/-- A real cell replacement preserves the region when its new immediate
owned edges stay inside the region. Updates below the cutoff impose no new
edge obligation: their outgoing edges are outside this predicate's scope. -/
theorem HeapRegionClosed.setCell
    {cutoff location : Location} {before after : RuntimeState}
    {current replacement : HeapCell}
    (closed : HeapRegionClosed cutoff before.heap)
    (found : findCell? before.heap location = some current)
    (operation : setCell before location replacement = .ok after)
    (fields : cutoff ≤ location → ∀ child,
      Value.object (.heap child) ∈ replacement.object.ownedValues.toList →
      cutoff ≤ child) :
    HeapRegionClosed cutoff after.heap := by
  obtain ⟨expected, expectedStep, targetAfter, frame, _, _, _, _, _⟩ :=
    Fir.LeanIR.Impure.setCell_spec_of_find before location current replacement found
  have same : expected = after := Except.ok.inj (expectedStep.symm.trans operation)
  subst expected
  intro parent cell child above cellFound member
  by_cases atTarget : parent = location
  · subst parent
    rw [targetAfter] at cellFound
    cases cellFound
    exact fields above child member
  · rw [frame parent atTarget] at cellFound
    exact closed parent cell child above cellFound member

/-- An in-place Array push needs a bound only for the added owned value;
the existing elements' bounds follow from the pre-state region. This is the
exact semantic mutation exposed by the concrete raw-push refinement. -/
theorem HeapRegionClosed.pushArray
    {cutoff location : Location} {before after : RuntimeState}
    {cell : HeapCell} {elements : Array Value} {capacity : Nat} {value : Value}
    (closed : HeapRegionClosed cutoff before.heap)
    (found : findCell? before.heap location = some cell)
    (objectEq : cell.object = .array elements capacity)
    (operation : Fir.LeanIR.Impure.setCell before location
      { cell with object := .array (elements.push value) capacity } = .ok after)
    (added : cutoff ≤ location → ∀ child,
      value = .object (.heap child) → cutoff ≤ child) :
    HeapRegionClosed cutoff after.heap := by
  apply closed.setCell found operation
  intro above child member
  simp only [HeapObject.ownedValues, Array.toList_push, List.mem_append,
    List.mem_singleton] at member
  rcases member with old | new
  · apply closed location cell child above found
    simpa [objectEq, HeapObject.ownedValues] using old
  · exact added above child new.symm

/-- The existing concrete in-place push also preserves a source allocation
region and ordinary caller tokens. The source mutation equation is obtained
from the concrete refinement, not supplied as a separate client certificate.
As in the raw-push theorem, retain/transfer policy is a caller obligation;
this is not a compiler admission or initializer-execution theorem. -/
theorem pushResidentArrayElementInPlaceRaw_refines_region
    {state : MemoryState} {witness : RefinementWitness} {runtime : RuntimeState}
    {cutoff location : Location} {address : Word32} {cell : HeapCell}
    {elements : Array Value} {capacity : Nat}
    (related : LiveHeapRel state witness runtime)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .array elements capacity)
    (descriptorFound : witness.descriptors.lookup? address = some (.array capacity))
    (value : Value) (word : Word32) (spare : elements.size < capacity)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (closed : HeapRegionClosed cutoff runtime.heap)
    (added : cutoff ≤ location → ∀ child,
      value = .object (.heap child) → cutoff ≤ child) :
    ∃ result nextRuntime,
      pushResidentArrayElementInPlaceRaw state address word = .ok result ∧
      Fir.LeanIR.Impure.setCell runtime location
          { cell with object := .array (elements.push value) capacity } =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      MappedHeaderCapacityTransport state result witness ∧
      result.heapCursor = state.heapCursor ∧
      HeapRegionClosed cutoff nextRuntime.heap ∧
      OrdinaryPersistenceTransport runtime nextRuntime := by
  obtain ⟨result, nextRuntime, operation, mutation, nextRelated, capacityFrame,
      cursor⟩ :=
    related.pushResidentArrayElementInPlaceRaw_refines mapped found live objectEq
      descriptorFound value word spare valueRelated
  exact ⟨result, nextRuntime, operation, mutation, nextRelated, capacityFrame,
    cursor, closed.pushArray found objectEq mutation added,
    setCell_ordinaryPersistenceTransport
      (replacement := { cell with object := .array (elements.push value) capacity })
      found rfl mutation⟩

/-- All paths from region roots stay in the region, including shared graphs
and cycles. There is no acyclicity or traversal-fuel premise. -/
theorem HeapRegionClosed.reachable
    {cutoff : Location} {heap : Heap} {roots : List Value} {location : Location}
    (closed : HeapRegionClosed cutoff heap)
    (rootBound : ∀ root, Value.object (.heap root) ∈ roots → cutoff ≤ root)
    (reachable : Reachable heap roots location) :
    cutoff ≤ location := by
  induction reachable with
  | root member => exact rootBound _ member
  | child parentReachable found member reference ih =>
    subst_vars
    exact closed _ _ _ ih found member

/-- The original concrete caller relation places its tokens below the region;
allocation-local closure places every published reachable node above it. -/
theorem ReuseTokenPublicationDisjoint.of_freshRegion
    {facts : ReuseCapacityFacts} {function : Fir.Wasm.Function}
    {before after : RuntimeState} {env : Env} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness} {root : Location}
    (related : ReuseCapacityStateRelated facts function before env store locals
      witness)
    (closed : HeapRegionClosed before.nextLocation after.heap)
    (rootBound : before.nextLocation ≤ root) :
    ReuseTokenPublicationDisjoint facts after env (.object (.heap root)) := by
  intro id available location tracked tokenLookup reachable
  have below := related.retainedToken_beforeNext tracked tokenLookup
  have above := closed.reachable
    (by intro candidate member; simpa using
      (show candidate = root from by simpa using member) ▸ rootBound) reachable
  exact (Nat.not_le_of_lt below) above

/-- Consume a locally established region at publication and bind. The prefix
transport is explicit; this theorem does not certify arbitrary callee code. -/
theorem ReuseTokenOrdinaryBindTransport.freshRegion_setGlobal
    {facts : ReuseCapacityFacts} {function : Fir.Wasm.Function}
    {before after : RuntimeState} {env : Env} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness} {root : Location}
    (related : ReuseCapacityStateRelated facts function before env store locals
      witness)
    (calleePrefix : ReuseTokenOrdinaryTransport facts env before after)
    (closed : HeapRegionClosed before.nextLocation after.heap)
    (rootBound : before.nextLocation ≤ root)
    (name : Name) (result : FVarId) :
    ReuseTokenOrdinaryBindTransport facts result before
      (after.setGlobal name (.object (.heap root))) env (.object (.heap root)) :=
  (ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint name
    (.of_freshRegion related closed rootBound)).precomposeRetained calleePrefix

section InternalMiss

variable
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts}
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

/-- The complete compiler-selected internal miss transports retained token
ordinaryness from caller entry through initializer execution, recursive
publication, and destination binding. Unlike the all-location transport,
this theorem admits heap-valued initializer results.

The actual lowering/adapter equations select the recursive callee. Its
existing miss induction supplies the exact publication transport, rather
than a new caller-selected target path or a non-heap result restriction. -/
theorem SourceLazyLetResult.miss_ordinaryBindTransport_of_internalCompiler
    (supported : LazyCacheInternalMissSupported context decl declaration
      sourceDeclaration resultKind calleeCode)
    (sourceStep : SourceLazyLetResult .miss context sourceExternals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted : instructions sourceModule callerFunction labels valueCode =
      .ok targetValue)
    (induction : LazyCacheInternalMissInduction context sourceModule module
      hostEnv sourceExternals facts sourceRuntime sourceEnv decl.fvarId
      declaration calleeCode resultKind initial initialWitness sourceValue
      stepCost) :
    ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime nextRuntime
      sourceEnv sourceValue := by
  rcases supported with
    ⟨⟨valueEq, kindEq, targetEq, _targetResultEq, _resultCompatible, paramsEq,
      _resultCompiled⟩, bodyEq⟩
  obtain ⟨_targetResultKind, _cacheIndex, declarationId, _cacheSetId,
      _recoveredTargetResultEq, _cacheEq, declarationCall, _cacheSetCall,
      _valueCodeEq, _targetValueEq⟩ :=
    compileCachedLetValue_adapted_inv context sourceModule callerFunction
      labels decl declaration sourceDeclaration _ valueCode targetValue
      valueEq kindEq targetEq paramsEq valueCompiled valueAdapted
  obtain ⟨calleeContext, calleeFunction, targetFunction, callRuntime,
      afterCall, callWitness, physical, contexts, callee, publication⟩ :=
    induction declarationCall
  have publicationRuntimeEq :
      nextRuntime = callRuntime.setGlobal declaration sourceValue :=
    (SourceLazyLetResult.miss_cacheFacts_of_callee valueEq targetEq
      (Array.isEmpty_iff.mp paramsEq) bodyEq sourceStep
      (contexts.sourceCodeResult
        callee.declaration.capacityPreserving.successful.sourceResult)).2
  rw [publicationRuntimeEq]
  exact publication.precompose callee.declaration.ordinaryTransport

/-- The preferred semantic postcondition, disjointness from the returned
ownership graph, supplies the complete miss transport. No ABI result kind is
excluded. Proving this disjointness for arbitrary admitted callers remains a
separate ownership obligation; this theorem does not assume it from typing. -/
theorem SourceLazyLetResult.miss_ordinaryBindTransport_of_publicationInduction
    (supported : LazyCacheInternalMissSupported context decl declaration
      sourceDeclaration resultKind calleeCode)
    (sourceStep : SourceLazyLetResult .miss context sourceExternals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted : instructions sourceModule callerFunction labels valueCode =
      .ok targetValue)
    (induction : LazyCacheInternalPublicationInduction context sourceModule
      module hostEnv sourceExternals facts sourceRuntime sourceEnv declaration
      calleeCode resultKind initial initialWitness sourceValue stepCost) :
    ReuseTokenOrdinaryBindTransport facts decl.fvarId sourceRuntime nextRuntime
      sourceEnv sourceValue :=
  SourceLazyLetResult.miss_ordinaryBindTransport_of_internalCompiler supported
    sourceStep valueCompiled valueAdapted induction.toMissInduction

end InternalMiss

end FirTalos.Concrete
