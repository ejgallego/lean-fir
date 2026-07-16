import FirTalos.Correctness.ABI
import FirTalos.Adapter
import Interpreter.Wasm.Locals

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

/-- A checked target-local write, including its frame-preservation contract. -/
def LocalUpdate (before after : Wasm.Locals) (index : Nat)
    (value : Wasm.Value) : Prop :=
  after.get index = some value ∧
    ∀ {other : Nat}, other ≠ index → after.get other = before.get other

/-- Talos's checked `set?` operation implements the abstract local update. -/
theorem localUpdate_of_set?
    {before after : Wasm.Locals} {index : Nat} {value : Wasm.Value}
    (updated : before.set? index value = some after) :
    LocalUpdate before after index value := by
  unfold Wasm.Locals.set? at updated
  by_cases inParams : index < before.params.length
  · simp only [inParams, ↓reduceIte] at updated
    cases updated
    constructor
    · simp only [Wasm.Locals.get, List.length_set, inParams, ↓reduceIte]
      exact List.getElem?_set_self inParams
    · intro other different
      by_cases otherInParams : other < before.params.length
      · simp only [Wasm.Locals.get, List.length_set, otherInParams, ↓reduceIte]
        rw [List.getElem?_set_ne different.symm]
      · simp [Wasm.Locals.get, otherInParams]
  · simp only [inParams, ↓reduceIte] at updated
    by_cases inLocals : index < before.params.length + before.locals.length
    · simp only [inLocals, ↓reduceIte] at updated
      cases updated
      constructor
      · have shiftedInLocals :
            index - before.params.length < before.locals.length := by
          omega
        simp only [Wasm.Locals.get, inParams, ↓reduceIte,
          List.length_set, inLocals]
        exact List.getElem?_set_self shiftedInLocals
      · intro other different
        by_cases otherInParams : other < before.params.length
        · simp [Wasm.Locals.get, otherInParams]
        · by_cases otherInLocals :
              other < before.params.length + before.locals.length
          · have shiftedDifferent :
                other - before.params.length ≠ index - before.params.length := by
              omega
            simp only [Wasm.Locals.get, otherInParams, ↓reduceIte,
              List.length_set, otherInLocals]
            rw [List.getElem?_set_ne shiftedDifferent.symm]
          · simp [Wasm.Locals.get, otherInParams, otherInLocals]
    · simp [inLocals] at updated

theorem findFVar?_eq_of_name_eq
    (bindings : List (Lean.FVarId × AbiKind)) {left right : Lean.FVarId}
    (names : left.name = right.name) :
    findFVar? bindings left = findFVar? bindings right := by
  induction bindings with
  | nil => rfl
  | cons binding bindings ih =>
      simp only [findFVar?]
      rw [names]
      split <;> simp [ih]

/-- Distinct source names cannot resolve to the same generated local slot. -/
theorem findFVar?_ne_of_name_ne
    (bindings : List (Lean.FVarId × AbiKind)) {left right : Lean.FVarId}
    {leftIndex rightIndex : Nat}
    (names : left.name ≠ right.name)
    (leftFound : findFVar? bindings left = some leftIndex)
    (rightFound : findFVar? bindings right = some rightIndex) :
    leftIndex ≠ rightIndex := by
  induction bindings generalizing leftIndex rightIndex with
  | nil => simp [findFVar?] at leftFound
  | cons binding bindings ih =>
      simp only [findFVar?] at leftFound rightFound
      by_cases leftHead : binding.1.name == left.name
      · rw [if_pos leftHead] at leftFound
        by_cases rightHead : binding.1.name == right.name
        · rw [if_pos rightHead] at rightFound
          have leftName : binding.1.name = left.name := LawfulBEq.eq_of_beq leftHead
          have rightName : binding.1.name = right.name := LawfulBEq.eq_of_beq rightHead
          exfalso
          exact names (leftName.symm.trans rightName)
        · rw [if_neg rightHead] at rightFound
          simp at leftFound
          subst leftIndex
          cases found : findFVar? bindings right with
          | none => simp [found] at rightFound
          | some index =>
              simp [found] at rightFound
              omega
      · rw [if_neg leftHead] at leftFound
        by_cases rightHead : binding.1.name == right.name
        · rw [if_pos rightHead] at rightFound
          simp at rightFound
          subst rightIndex
          cases found : findFVar? bindings left with
          | none => simp [found] at leftFound
          | some index =>
              simp [found] at leftFound
              omega
        · rw [if_neg rightHead] at rightFound
          cases leftTail : findFVar? bindings left with
          | none => simp [leftTail] at leftFound
          | some nextLeft =>
              cases rightTail : findFVar? bindings right with
              | none => simp [rightTail] at rightFound
              | some nextRight =>
                  simp [leftTail] at leftFound
                  simp [rightTail] at rightFound
                  subst leftIndex
                  subst rightIndex
                  have tailDifferent := ih leftTail rightTail
                  omega

/--
Every live source binding has a compiler-resolved target slot whose physical
value decodes to the source value under the current handle table.
-/
def EnvLocalsRelated (bindings : List (Lean.FVarId × AbiKind))
    (source : Env) (handles : HandleTable) (target : Wasm.Locals) : Prop :=
  ∀ {fvar : Lean.FVarId} {value : Value}, lookup source fvar = some value →
    ∃ index kind physical,
      findFVar? bindings fvar = some index ∧
      bindings[index]?.map Prod.snd = some kind ∧
      target.get index = some physical ∧
      DecodesValue handles kind physical value

/-- Growing the handle table preserves every already-related source local. -/
theorem EnvLocalsRelated.of_handleTableExtends
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {before after : HandleTable} {target : Wasm.Locals}
    (related : EnvLocalsRelated bindings source before target)
    (extension : HandleTableExtends before after) :
    EnvLocalsRelated bindings source after target := by
  intro fvar value sourceLookup
  rcases related sourceLookup with
    ⟨index, kind, physical, found, kindAt, targetLookup, decoded⟩
  exact ⟨index, kind, physical, found, kindAt, targetLookup,
    decodesValue_of_handleTableExtends extension decoded⟩

/--
Binding one source result and writing its generated destination slot preserves
the source-environment/target-local relation. Existing handle-backed locals
remain valid through the explicit table-extension premise.
-/
theorem EnvLocalsRelated.bind
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {before after : HandleTable} {target updated : Wasm.Locals}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {sourceValue : Value} {physical : Wasm.Value}
    (related : EnvLocalsRelated bindings source before target)
    (resultFound : findFVar? bindings result = some resultIndex)
    (kindAt : bindings[resultIndex]?.map Prod.snd = some kind)
    (localUpdate : LocalUpdate target updated resultIndex physical)
    (extension : HandleTableExtends before after)
    (decoded : DecodesValue after kind physical sourceValue) :
    EnvLocalsRelated bindings (Fir.LeanIR.Impure.bind source result sourceValue)
      after updated := by
  intro fvar value sourceLookup
  by_cases sameName : (result.name == fvar.name) = true
  · have names : result.name = fvar.name := LawfulBEq.eq_of_beq sameName
    have sameFind := findFVar?_eq_of_name_eq bindings names
    have found : findFVar? bindings fvar = some resultIndex := by
      rw [← sameFind]
      exact resultFound
    have valueEq : value = sourceValue := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup.symm
    subst value
    exact ⟨resultIndex, kind, physical, found, kindAt, localUpdate.1, decoded⟩
  · have oldLookup : lookup source fvar = some value := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup
    rcases related oldLookup with
      ⟨index, oldKind, oldPhysical, found, oldKindAt, targetLookup, oldDecoded⟩
    have names : result.name ≠ fvar.name := by
      intro equal
      apply sameName
      rw [equal]
      exact beq_self_eq_true _
    have different :=
      findFVar?_ne_of_name_ne bindings names resultFound found
    exact ⟨index, oldKind, oldPhysical, found, oldKindAt,
      (localUpdate.2 different.symm).trans targetLookup,
      decodesValue_of_handleTableExtends extension oldDecoded⟩

/--
The common generated handle-result path: successful encoding grows the codec
monotonically, the checked `local.set` writes the new handle, and the source
environment may be extended with the encoded semantic value.
-/
theorem EnvLocalsRelated.bind_handle_of_encode
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {before after : HandleTable} {target updated : Wasm.Locals}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {sourceValue : Value} {handle : Handle}
    (related : EnvLocalsRelated bindings source before target)
    (invariant : HandleTableInvariant before)
    (resultFound : findFVar? bindings result = some resultIndex)
    (kindAt : bindings[resultIndex]?.map Prod.snd = some kind)
    (usesHandle : kind.usesHandle = true)
    (encoded : before.encode kind sourceValue = .ok (after, handle))
    (targetSet : target.set? resultIndex (.i32 handle) = some updated) :
    EnvLocalsRelated bindings (Fir.LeanIR.Impure.bind source result sourceValue)
      after updated := by
  apply EnvLocalsRelated.bind related resultFound kindAt
    (localUpdate_of_set? targetSet)
    (handleTableExtends_of_encode invariant usesHandle encoded)
  exact decodeValue_handle_of_decodeAs usesHandle
    (decodeAs_of_encode invariant.coherent usesHandle encoded)

end FirTalos.Correctness
