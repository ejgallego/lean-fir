import FirTalos.ConcreteLazyPublication
import FirTalos.ConcreteStructuredSimulation

namespace FirTalos.Concrete

open Lean Lean.Compiler Fir.Wasm Fir.LeanIR.Impure Fir.Wasm.Concrete
open FirTalos.Correctness

private def publishedLocation : Location := 0
private def retainedLocation : Location := 1

private def publishedCell : HeapCell := {
  object := .string "published"
  rc := 1
  persistent := false
  live := true }

private def retainedCell : HeapCell := {
  object := .string "retained"
  rc := 1
  persistent := false
  live := true }

private def publicationRuntime : RuntimeState := {
  heap := [(publishedLocation, publishedCell), (retainedLocation, retainedCell)]
  nextLocation := 2 }

private def publishedRoot : Value := .object (.heap publishedLocation)
private def retainedToken : FVarId := FVarId.mk `retained
private def resultId : FVarId := FVarId.mk `result
private def retainedFacts : ReuseCapacityFacts :=
  [(retainedToken, .retainedAtLeast 1)]
private def retainedEnv : Env :=
  [(retainedToken, .reuseToken (some retainedLocation))]

private def twoPublicationRuntime : RuntimeState :=
  (publicationRuntime.setGlobal `cache publishedRoot).setGlobal
    `outerCache publishedRoot

private theorem publication_marks_root_persistent :
    findCell? (publicationRuntime.setGlobal `cache publishedRoot).heap
        publishedLocation =
      some { publishedCell with rc := 0, persistent := true } := by
  rfl

private theorem publication_keeps_distinct_cell_ordinary :
    findCell? (publicationRuntime.setGlobal `cache publishedRoot).heap
        retainedLocation = some retainedCell := by
  rfl

theorem publication_not_ordinaryPersistenceTransport :
    ¬ OrdinaryPersistenceTransport publicationRuntime
      (publicationRuntime.setGlobal `cache publishedRoot) := by
  intro transport
  have afterFound := publication_marks_root_persistent
  have beforeFound : findCell? publicationRuntime.heap publishedLocation =
      some publishedCell := by
    simp [publicationRuntime, publishedLocation, publishedCell, findCell?]
  have result := transport publishedLocation
    { publishedCell with rc := 0, persistent := true } afterFound
      (fun beforeCell found => by
        have beforeEq : beforeCell = publishedCell :=
          Option.some.inj (found.symm.trans beforeFound)
        rw [beforeEq]
        rfl)
  simp at result

private theorem publication_initial_retainedToken_ordinary :
    ReuseTokenOrdinaryRel retainedFacts publicationRuntime retainedEnv := by
  intro tokenId available location cell tracked tokenLookup found
  have tokenLookup' := tokenLookup
  simp [retainedEnv, retainedToken, retainedLocation, lookup] at tokenLookup'
  have locationEq : location = retainedLocation := tokenLookup'.2.symm
  rw [locationEq] at found
  have cellEq : cell = retainedCell := by
    simpa [publicationRuntime, publishedLocation, retainedLocation,
      retainedCell, findCell?] using found.symm
  rw [cellEq]
  simp [retainedCell]

private theorem publication_disjoint :
    ReuseTokenPublicationDisjoint retainedFacts publicationRuntime retainedEnv
      publishedRoot := by
  intro tokenId available location tracked tokenLookup reachable
  have tokenLookup' := tokenLookup
  simp [retainedEnv, retainedToken, retainedLocation, lookup] at tokenLookup'
  have locationEq : location = retainedLocation := tokenLookup'.2.symm
  have rootNe : retainedLocation ≠ publishedLocation := by
    decide
  have noOtherReach :
      ∀ {loc : Location}, loc ≠ publishedLocation →
        ¬ Reachable publicationRuntime.heap [publishedRoot] loc := by
    intro loc locNe reachable
    induction reachable with
    | root member =>
        apply locNe
        simpa [publishedRoot] using member
    | child parentReachable found member reference ih =>
        rename_i parent child cell value
        by_cases parentEq : parent = publishedLocation
        · subst parent
          simp [publicationRuntime, publishedCell, retainedCell, findCell?]
            at found
          subst cell
          simp [HeapObject.ownedValues] at member
        · exact ih parentEq
  exact (noOtherReach (by
    intro locationEqZero
    apply rootNe
    exact locationEq.symm.trans locationEqZero)) reachable

theorem publication_preserves_distinctRetainedTokenFacts :
    ReuseTokenOrdinaryBindTransport retainedFacts resultId
      publicationRuntime (publicationRuntime.setGlobal `cache publishedRoot)
      retainedEnv publishedRoot := by
  apply ReuseTokenOrdinaryBindTransport.precompose
    (beforePublication := OrdinaryPersistenceTransport.refl publicationRuntime)
  exact ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint `cache
    publication_disjoint

/-- The same publication which refutes all-location transport above is a
valid prefix for the fixed caller's nonempty retained-token frame. -/
theorem publication_retainedTransport :
    ReuseTokenOrdinaryTransport retainedFacts retainedEnv publicationRuntime
      (publicationRuntime.setGlobal `cache publishedRoot) :=
  ReuseTokenOrdinaryTransport.ofPublicationDisjoint `cache publication_disjoint

private theorem publication_after_disjoint :
    ReuseTokenPublicationDisjoint retainedFacts
      (publicationRuntime.setGlobal `cache publishedRoot) retainedEnv
      publishedRoot := by
  intro tokenId available location tracked tokenLookup reachable
  have tokenLookup' := tokenLookup
  simp [retainedEnv, retainedToken, retainedLocation, lookup] at tokenLookup'
  have locationEq : location = retainedLocation := tokenLookup'.2.symm
  have noOtherReach :
      ∀ {loc : Location}, loc ≠ publishedLocation →
        ¬ Reachable (publicationRuntime.setGlobal `cache publishedRoot).heap
          [publishedRoot] loc := by
    intro loc locNe reachable
    induction reachable with
    | root member =>
        apply locNe
        simpa [publishedRoot] using member
    | child parentReachable found member reference ih =>
        rename_i parent child cell value
        have noChildren : cell.object.ownedValues = #[] := by
          change findCell? [(0, { publishedCell with rc := 0, persistent := true }),
            (1, retainedCell)] parent = some cell at found
          simp only [findCell?] at found
          split at found
          · cases Option.some.inj found
            rfl
          · split at found
            · cases Option.some.inj found
              rfl
            · contradiction
        rw [noChildren] at member
        simp at member
  exact noOtherReach (by simp [locationEq, retainedLocation, publishedLocation])
    reachable

/-- Nested heap-cache publication followed by destination binding preserves
the caller frame even though its first prefix lacks all-location transport. -/
theorem twoPublications_preserve_retainedTokenFacts :
    ReuseTokenOrdinaryBindTransport retainedFacts resultId publicationRuntime
      ((publicationRuntime.setGlobal `cache publishedRoot).setGlobal
        `outerCache publishedRoot) retainedEnv publishedRoot := by
  exact ReuseTokenOrdinaryBindTransport.precomposeRetained
    publication_retainedTransport
    (ReuseTokenOrdinaryTransport.eraseBind
      (ReuseTokenOrdinaryTransport.ofPublicationDisjoint `outerCache
        publication_after_disjoint))

/-- Non-vacuous use of the composed transport, starting with an actual
ordinary retained token and ending with both cache publications installed. -/
theorem twoPublications_post_retainedToken_ordinary :
    ReuseTokenOrdinaryRel (eraseReuseCapacityFact retainedFacts resultId)
      ((publicationRuntime.setGlobal `cache publishedRoot).setGlobal
        `outerCache publishedRoot) (bind retainedEnv resultId publishedRoot) := by
  have complete := publication_retainedTransport.trans
    (ReuseTokenOrdinaryTransport.ofPublicationDisjoint `outerCache
      publication_after_disjoint)
  exact complete.eraseBind publication_initial_retainedToken_ordinary

/-- A conditional consumer regression for the facts-aware caller-frame
    restoration boundary. This is deliberately a frame theorem with explicit
    checked transport premises, not a compiled-call or structured-stack
    execution claim. -/
theorem twoPublications_restoreCallerFrame
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {initial afterCall : Wasm.Store Host}
    {initialWitness resultWitness : RefinementWitness}
    {calleeFacts : ReuseCapacityFacts}
    {calleeEnv : Env}
    {callerBytes resultBytes : Nat}
    {callerLocals calleeLocals resumedLocals : Wasm.Locals}
    {resultIndex : Nat} {physical : Wasm.Value}
    (caller : ConcreteReuseCapacityCacheFrame sourceModule callerFunction
      externals retainedFacts callerBytes publicationRuntime retainedEnv
      initial callerLocals initialWitness)
    (callee : ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
      externals calleeFacts resultBytes
      ((publicationRuntime.setGlobal `cache publishedRoot).setGlobal
        `outerCache publishedRoot)
      calleeEnv afterCall calleeLocals resultWitness)
    (witnessTransport : WitnessTransport initialWitness resultWitness)
    (capacityTransport : HeaderCapacityTransport initial.host.runtime.heap
      afterCall.host.runtime.heap initialWitness)
    (finalRelated : StateRelated callerFunction
      ((publicationRuntime.setGlobal `cache publishedRoot).setGlobal
        `outerCache publishedRoot)
      (bind retainedEnv resultId publishedRoot) afterCall resumedLocals
      resultWitness)
    (finalAligned : ConcreteLocalFrameAligned callerFunction
      ((publicationRuntime.setGlobal `cache publishedRoot).setGlobal
        `outerCache publishedRoot)
      (bind retainedEnv resultId publishedRoot) afterCall resumedLocals
      resultWitness)
    (resultFound :
      findFVar? (functionBindings callerFunction) resultId = some resultIndex)
    (localUpdate : FirTalos.Correctness.LocalUpdate callerLocals resumedLocals
      resultIndex physical) :
    ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
      (eraseReuseCapacityFact retainedFacts resultId) resultBytes
      ((publicationRuntime.setGlobal `cache publishedRoot).setGlobal
        `outerCache publishedRoot)
      (bind retainedEnv resultId publishedRoot) afterCall resumedLocals
      resultWitness := by
  exact ConcreteReuseCapacityCacheFrame.restoreCaller_of_retainedTransport
    caller callee witnessTransport capacityTransport
    twoPublications_preserve_retainedTokenFacts finalRelated finalAligned
    resultFound localUpdate

/-- This conditional regression reaches the actual structured direct-pop
    consumer. It keeps the suspended caller scope and historical tail explicit,
    but returns the retained caller cache/ABI frame rather than claiming
    reconstruction of the stronger entry-relative resource stack. -/
theorem twoPublications_advance_popRetainedCache
    {context calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction calleeFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {outerRuntime : RuntimeState}
    {outerStore callStore targetStore : Wasm.Store Host}
    {outerWitness callWitness resultWitness : RefinementWitness}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {callerFunctionResult : AbiKind}
    {tailResult : Option AbiKind}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    {calleeFacts : ReuseCapacityFacts}
    {callerBytes resultBytes : Nat}
    {calleeEnv : Env}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels twoPublicationRuntime retainedEnv publishedRoot
      resultId continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail resultWitness kind
      physical resultIndex source target)
    (callerScope : ConcreteStructuredResourceScope context sourceModule
      sourceFunction externals outerRuntime outerStore outerWitness retainedFacts
      callerBytes publicationRuntime retainedEnv callStore callerLocals
      callWitness)
    (callee : ConcreteReuseCapacityCacheAbiFrame calleeContext sourceModule
      calleeFunction externals calleeFacts resultBytes twoPublicationRuntime
      calleeEnv targetStore calleeLocals resultWitness)
    (witnessTransport : WitnessTransport callWitness resultWitness)
    (capacityTransport : HeaderCapacityTransport callStore.host.runtime.heap
      targetStore.host.runtime.heap callWitness)
    (programEq : calleeContext.program = context.program)
    (tail : ConcreteStructuredSuspendedResourceStack externals context.program
      outerRuntime outerStore outerWitness callerFunctionResult tailResult
      sourceFrames targetFrames) :
    ∃ sourceAfter targetAfter resumedLocals,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredStackRel sourceAfter targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        twoPublicationRuntime (bind retainedEnv resultId publishedRoot)
        continuation targetStore resumedLocals targetRest resultWitness
        sourceAfter targetAfter ∧
      ConcreteReuseCapacityCacheAbiFrame context sourceModule sourceFunction
        externals (eraseReuseCapacityFact retainedFacts resultId) resultBytes
        twoPublicationRuntime (bind retainedEnv resultId publishedRoot)
        targetStore resumedLocals resultWitness ∧
      sourceAfter.joins = callerJoins ∧
      sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = targetFrames := by
  have ordinaryTransport :
      ReuseTokenOrdinaryBindTransport retainedFacts resultId
        publicationRuntime twoPublicationRuntime retainedEnv publishedRoot := by
    simpa [twoPublicationRuntime] using
      twoPublications_preserve_retainedTokenFacts
  exact related.advance_popRetainedCache callerScope callee witnessTransport
    capacityTransport ordinaryTransport programEq tail

theorem publication_post_retainedToken_ordinary :
    ReuseTokenOrdinaryRel (eraseReuseCapacityFact retainedFacts resultId)
      (publicationRuntime.setGlobal `cache publishedRoot)
      (bind retainedEnv resultId publishedRoot) := by
  exact publication_preserves_distinctRetainedTokenFacts
    publication_initial_retainedToken_ordinary

theorem publication_rejects_aliasingRetainedToken :
    ¬ ReuseTokenPublicationDisjoint retainedFacts publicationRuntime retainedEnv
        (.object (.heap retainedLocation)) := by
  intro disjoint
  have tracked : findReuseCapacityEvidence? retainedFacts retainedToken =
      some (.retainedAtLeast 1) := by
    simp [retainedFacts, retainedToken, findReuseCapacityEvidence?]
  have tokenLookup : lookup retainedEnv retainedToken =
      some (.reuseToken (some retainedLocation)) := by
    simp [retainedEnv, retainedToken, retainedLocation, lookup]
  have reachable : Reachable publicationRuntime.heap
      [.object (.heap retainedLocation)] retainedLocation := by
    exact .root (by simp)
  exact disjoint retainedToken 1 retainedLocation tracked tokenLookup reachable

/-- Allocation freshness alone is insufficient: an owned field can still
publish an older retained token. This is the existing alias-safety boundary,
not a reason to weaken the concrete reuse protocol. -/
theorem freshConstructorPublication_rejects_ownedRetainedToken :
    let allocated := alloc publicationRuntime
      (.ctor { tag := 0, objectFields := #[.object (.heap retainedLocation)],
               usizeFields := #[], scalarFields := [] }) false
    ¬ReuseTokenOrdinaryBindTransport retainedFacts resultId publicationRuntime
      (allocated.1.setGlobal `bad (.object allocated.2)) retainedEnv
      (.object allocated.2) := by
  dsimp
  intro transport
  have ordinary := transport publication_initial_retainedToken_ordinary
  have impossible := ordinary retainedToken 1 retainedLocation
    { retainedCell with rc := 0, persistent := true }
    (by simp [retainedFacts, resultId, retainedToken,
      findReuseCapacityEvidence?, eraseReuseCapacityFact])
    (by simp [Fir.LeanIR.Impure.bind, retainedEnv, resultId, retainedToken, lookup])
    (by rfl)
  cases impossible

private def freshStringAllocation (text : String) : RuntimeState × ObjectRef :=
  alloc publicationRuntime (.string text) false

private def freshStringRuntime (text : String) : RuntimeState :=
  (freshStringAllocation text).1.setGlobal `leafCache
    (.object (freshStringAllocation text).2)

/-- The actual pop consumer needs no supplied freshness, reachability, or
ordinary-binding premise for this fresh string publication. Those facts follow
from the saved caller's existing capacity/state relation and actual allocation.
The nonempty token map is unchanged. Physical bind focus and callee frame remain
explicit: this is not a proof of the preceding compiled callee execution. -/
theorem freshString_advance_popRetainedCache
    (text : String)
    {context calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction calleeFunction : Fir.Wasm.Function}
    {labels : LabelContext} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {outerRuntime : RuntimeState}
    {outerStore callStore targetStore : Wasm.Store Host}
    {outerWitness callWitness resultWitness : RefinementWitness}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv} {sourceFrames : List Frame}
    {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program} {targetFrames : List StructuredWasmFrame}
    {callerFunctionResult : AbiKind} {tailResult : Option AbiKind}
    {kind : AbiKind} {physical : Wasm.Value} {resultIndex : Nat}
    {source : MachineState} {target : StructuredWasmState Host}
    {calleeFacts : ReuseCapacityFacts} {callerBytes resultBytes : Nat}
    {calleeEnv : Env}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels (freshStringRuntime text) retainedEnv
      (.object (freshStringAllocation text).2) resultId continuation callerJoins
      sourceFrames targetStore callerLocals callerRemainder targetRest
      targetFrames returnedTail resultWitness kind physical resultIndex source target)
    (callerScope : ConcreteStructuredResourceScope context sourceModule
      sourceFunction externals outerRuntime outerStore outerWitness retainedFacts
      callerBytes publicationRuntime retainedEnv callStore callerLocals callWitness)
    (callee : ConcreteReuseCapacityCacheAbiFrame calleeContext sourceModule
      calleeFunction externals calleeFacts resultBytes (freshStringRuntime text)
      calleeEnv targetStore calleeLocals resultWitness)
    (witnessTransport : WitnessTransport callWitness resultWitness)
    (capacityTransport : HeaderCapacityTransport callStore.host.runtime.heap
      targetStore.host.runtime.heap callWitness)
    (programEq : calleeContext.program = context.program)
    (tail : ConcreteStructuredSuspendedResourceStack externals context.program
      outerRuntime outerStore outerWitness callerFunctionResult tailResult
      sourceFrames targetFrames) :
    ∃ sourceAfter targetAfter resumedLocals,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredStackRel sourceAfter targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        (freshStringRuntime text)
        (bind retainedEnv resultId (.object (freshStringAllocation text).2))
        continuation targetStore resumedLocals targetRest resultWitness
        sourceAfter targetAfter ∧
      ConcreteReuseCapacityCacheAbiFrame context sourceModule sourceFunction
        externals (eraseReuseCapacityFact retainedFacts resultId) resultBytes
        (freshStringRuntime text)
        (bind retainedEnv resultId (.object (freshStringAllocation text).2))
        targetStore resumedLocals resultWitness ∧
      sourceAfter.joins = callerJoins ∧
      sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = targetFrames := by
  have ordinaryTransport :=
    ReuseTokenOrdinaryBindTransport.allocLeaf_setGlobal
      callerScope.1.1.stateRelated (object := .string text) rfl rfl `leafCache resultId
  exact related.advance_popRetainedCache callerScope callee witnessTransport
    capacityTransport ordinaryTransport programEq tail

/-- A new parent owns the same new leaf twice. Publication must preserve the
old retained token despite this nonempty, shared ownership graph. -/
private def sharedStringParent (reference : ObjectRef) : HeapObject :=
  .ctor { tag := 0, objectFields := #[.object reference, .object reference], usizeFields := #[], scalarFields := [] }

private def freshSharedAllocation (text : String) : RuntimeState × ObjectRef :=
  let leaf := freshStringAllocation text
  alloc leaf.1 (sharedStringParent leaf.2) false

/-- The positive fixture genuinely reaches an owned child distinct from its
published root; it does not reduce to the previous leaf-only test. -/
theorem freshSharedGraph_reaches_leaf (text : String) :
    Reachable (freshSharedAllocation text).1.heap
      [.object (freshSharedAllocation text).2] publicationRuntime.nextLocation := by
  apply Reachable.child (parent := publicationRuntime.nextLocation + 1)
    (cell := { object := sharedStringParent (freshStringAllocation text).2 })
    (value := .object (.heap publicationRuntime.nextLocation))
  · exact .root (by simp [freshSharedAllocation, freshStringAllocation, alloc])
  · simp [freshSharedAllocation, freshStringAllocation, alloc, findCell?]
  · simp [sharedStringParent, HeapObject.ownedValues, freshStringAllocation, alloc]
  · rfl

/-- Actual two-allocation publication discharges graph safety from local field
construction and the existing entry relation, with no supplied freshness,
disjointness, or ordinary-binding premise. The caller fact map is nonempty.
This is source-runtime ownership transport, not execution of a compiled body. -/
theorem freshSharedGraph_publication
    (text : String)
    {function : Fir.Wasm.Function} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {witness : RefinementWitness}
    (related : ReuseCapacityStateRelated retainedFacts function publicationRuntime
      retainedEnv store locals witness) :
    ReuseTokenOrdinaryBindTransport retainedFacts resultId publicationRuntime
      ((freshSharedAllocation text).1.setGlobal `sharedCache
        (.object (freshSharedAllocation text).2))
      retainedEnv (.object (freshSharedAllocation text).2) := by
  have leafClosed : HeapRegionClosed publicationRuntime.nextLocation
      (freshStringAllocation text).1.heap :=
    related.freshRegionClosed.alloc
      (object := .string text) (persistent := false) rfl
      (by simp [HeapObject.ownedValues])
  have graphClosed : HeapRegionClosed publicationRuntime.nextLocation
      (freshSharedAllocation text).1.heap :=
    leafClosed.alloc (object := sharedStringParent (freshStringAllocation text).2)
      (persistent := false) rfl (by
        intro child member
        have same : child = publicationRuntime.nextLocation := by
          simpa [sharedStringParent, HeapObject.ownedValues, freshStringAllocation,
            alloc] using member
        exact same.ge)
  have leafTransport : OrdinaryPersistenceTransport publicationRuntime
      (freshStringAllocation text).1 :=
    alloc_ordinaryPersistenceTransport (object := .string text) rfl
  have graphTransport : OrdinaryPersistenceTransport
      (freshStringAllocation text).1 (freshSharedAllocation text).1 :=
    alloc_ordinaryPersistenceTransport
      (object := sharedStringParent (freshStringAllocation text).2) rfl
  exact ReuseTokenOrdinaryBindTransport.freshRegion_setGlobal related
    (.ofOrdinaryPersistence (leafTransport.trans graphTransport)) graphClosed
    (by simp [freshSharedAllocation, freshStringAllocation, alloc]) `sharedCache resultId

end FirTalos.Concrete
