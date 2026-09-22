import FirTalos.ConcreteLazyPublication

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

theorem publication_preserves_distinctRetainedTokenFacts :
    ReuseTokenOrdinaryBindTransport retainedFacts resultId
      publicationRuntime (publicationRuntime.setGlobal `cache publishedRoot)
      retainedEnv publishedRoot := by
  apply ReuseTokenOrdinaryBindTransport.precompose
    (beforePublication := OrdinaryPersistenceTransport.refl publicationRuntime)
  apply ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint
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

end FirTalos.Concrete
