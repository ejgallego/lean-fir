import Batteries.Tactic.OpenPrivate
import Fir.Wasm.Validate

open private firstDuplicateIndexed? validateModuleShapeWithIndex from Fir.Wasm.Validate

namespace FirTalos.Concrete

private def scanStep [BEq α] [Hashable α]
    (state : Std.HashSet α × Std.HashSet α) (value : α) :
    Std.HashSet α × Std.HashSet α :=
  if state.1.contains value then (state.1, state.2.insert value)
  else (state.1.insert value, state.2)

private def scan [BEq α] [Hashable α] (xs : List α)
    (state : Std.HashSet α × Std.HashSet α) :
    Std.HashSet α × Std.HashSet α :=
  xs.foldl scanStep state

private theorem scan_duplicates_monotone [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (xs : List α) (state : Std.HashSet α × Std.HashSet α) (value : α)
    (present : state.2.contains value = true) :
    (scan xs state).2.contains value = true := by
  induction xs generalizing state with
  | nil => simpa [scan] using present
  | cons x xs ih =>
      apply ih
      unfold scanStep
      split <;> simp_all [scan, Std.HashSet.contains_insert]

private theorem scan_no_duplicates [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (xs : List α) (state : Std.HashSet α × Std.HashSet α)
    (clear : ∀ value ∈ xs, (scan xs state).2.contains value = false) :
    (∀ value ∈ xs, state.1.contains value = false) ∧ xs.Nodup := by
  induction xs generalizing state with
  | nil => simp
  | cons x xs ih =>
      have headClear : (scan (x :: xs) state).2.contains x = false :=
        clear x (by simp)
      have unseen : state.1.contains x = false := by
        by_cases h : state.1.contains x = true
        · have inserted : (scanStep state x).2.contains x = true := by
            simp [scanStep, h]
          have persists := scan_duplicates_monotone xs (scanStep state x) x inserted
          simp only [scan, List.foldl_cons] at headClear
          exact False.elim (by simpa [scan] using headClear.symm.trans persists)
        · exact Bool.eq_false_iff.mpr h
      let next := scanStep state x
      have tailClear : ∀ value ∈ xs, (scan xs next).2.contains value = false := by
        intro value member
        exact clear value (by simp [member])
      obtain ⟨tailUnseen, tailNodup⟩ := ih next tailClear
      constructor
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact unseen
        · have h := tailUnseen value member
          simp [next, scanStep, unseen, Std.HashSet.contains_insert] at h
          simpa [Std.HashSet.contains_iff_mem] using h.2
      · apply List.nodup_cons.mpr
        constructor
        · intro member
          have h := tailUnseen x member
          simp [next, scanStep, unseen, Std.HashSet.contains_insert] at h
        · exact tailNodup

private theorem forIn_none_no_duplicate_members [BEq α] [Hashable α]
    (xs : List α) (duplicates : Std.HashSet α)
    (noResult : (match ((forIn xs ((none : Option (Option α)), ()) fun value _ =>
        if duplicates.contains value then
          pure (ForInStep.done (some (some value), ()))
        else pure (ForInStep.yield (none, ()))) :
          Id (Option (Option α) × Unit)).1 with
        | some result => result
        | none => none) = none) :
    ∀ value ∈ xs, duplicates.contains value = false := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases h : duplicates.contains x = true
      · have member : x ∈ duplicates := (Std.HashSet.contains_iff_mem).mp h
        simp [List.forIn_cons, member] at noResult
      · have hx : duplicates.contains x = false := Bool.eq_false_iff.mpr h
        have notMember : x ∉ duplicates := by
          intro member
          exact h ((Std.HashSet.contains_iff_mem).mpr member)
        simp [List.forIn_cons, notMember] at noResult
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact hx
        · exact ih noResult value member

private theorem firstPass_eq_scan [BEq α] [Hashable α]
    (xs : List α) (state : Std.HashSet α × Std.HashSet α) :
    (forIn xs state fun value state =>
        if state.1.contains value then
          pure (ForInStep.yield (state.1, state.2.insert value))
        else pure (ForInStep.yield (state.1.insert value, state.2)) :
      Id (Std.HashSet α × Std.HashSet α)) = scan xs state := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x ∈ state.1
      · simpa [List.forIn_cons, h, scan, scanStep] using
          ih (state.1, state.2.insert x)
      · simpa [List.forIn_cons, h, scan, scanStep] using
          ih (state.1.insert x, state.2)

/-- The indexed two-pass duplicate search cannot miss a repeated value. -/
theorem firstDuplicateIndexed_none_nodup [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (values : Array α) (hnone : firstDuplicateIndexed? values = none) :
    values.toList.Nodup := by
  unfold firstDuplicateIndexed? at hnone
  simp only [Id.run, ← Array.forIn_toList, firstPass_eq_scan] at hnone
  have clear : ∀ value ∈ values.toList,
      (scan values.toList (Std.HashSet.emptyWithCapacity values.size,
        Std.HashSet.emptyWithCapacity values.size)).2.contains value = false := by
    apply forIn_none_no_duplicate_members
    cases hscan : scan values.toList (Std.HashSet.emptyWithCapacity values.size,
        Std.HashSet.emptyWithCapacity values.size) with
    | mk seen duplicates =>
        simp only [hscan, Bind.bind, Pure.pure] at hnone
        simp only [Pure.pure] at hnone ⊢
        cases hloop : ((forIn values.toList ((none : Option (Option α)), ())
            fun value _ =>
              if duplicates.contains value then
                ForInStep.done (some (some value), ())
              else ForInStep.yield (none, ())) :
            Id (Option (Option α) × Unit)).1 with
        | none => simp_all only
        | some result =>
            cases result <;> simp_all only
  exact (scan_no_duplicates values.toList _ clear).2

private theorem throw_except_eq (error : Fir.Wasm.SymbolicError) :
    (throw error : Except Fir.Wasm.SymbolicError α) = .error error := rfl

private theorem no_duplicate_declarations_of_shape
    (source : Fir.Wasm.Module)
    (shape : validateModuleShapeWithIndex source.checkIndex source = .ok ()) :
    firstDuplicateIndexed?
      (source.imports.filterMap (·.declaration?) ++ source.functions.map (·.name)) = none := by
  cases h : firstDuplicateIndexed?
      (source.imports.filterMap (·.declaration?) ++ source.functions.map (·.name)) with
  | none => rfl
  | some name =>
      exfalso
      unfold validateModuleShapeWithIndex at shape
      simp only [h] at shape
      cases hf : firstDuplicateIndexed? (source.functions.map (·.name)) <;>
        simp only [hf, throw_except_eq, Bind.bind, Except.bind] at shape
      cases hc : firstDuplicateIndexed? source.closureDispatch <;>
        simp only [hc] at shape
      cases hd : firstDuplicateIndexed? source.closureDescriptors <;>
        simp only [hd] at shape
      all_goals try contradiction
      repeat (split at shape <;> try contradiction)

/-- Successful symbolic validation makes external and internal declaration names
pairwise distinct in the source module's declaration order. -/
theorem declarationNames_nodup_of_validateModule
    {source : Fir.Wasm.Module}
    (validated : Fir.Wasm.validateModule source = .ok ()) :
    (source.imports.toList.filterMap (·.declaration?) ++
      source.functions.toList.map (·.name)).Nodup := by
  have shape : validateModuleShapeWithIndex source.checkIndex source = .ok () := by
    unfold Fir.Wasm.validateModule at validated
    simp only [Bind.bind, Except.bind] at validated
    cases result : validateModuleShapeWithIndex source.checkIndex source with
    | error error => simp [result] at validated
    | ok value => cases value; rfl
  have unique := firstDuplicateIndexed_none_nodup
    (source.imports.filterMap (·.declaration?) ++ source.functions.map (·.name))
    (no_duplicate_declarations_of_shape source shape)
  simpa using unique

end FirTalos.Concrete
