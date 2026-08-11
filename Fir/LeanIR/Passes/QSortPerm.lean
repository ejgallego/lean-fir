import Init.Data.Array.QSort
import Init.Data.Vector.Perm
import Lean.Elab.Term

namespace Fir.LeanIR.Passes.QSortPerm

/-!
Lean 4.33's executable quicksort keeps its two recursive workers private.  The
kernel declarations are still present in the imported environment, but their
private names contain a numeric component that cannot be written as an ordinary
Lean identifier.  Give those declarations stable, proof-local aliases so this
module can state induction lemmas about the implementation itself.
-/
run_elab
  let baseName := Lean.Name.num "_private.Init.Data.Array.QSort.Basic".toName 0
  let privateName (suffix : List String) := suffix.foldl Lean.Name.str baseName
  Lean.modifyEnv fun env =>
    let env := Lean.addAlias env `Fir.LeanIR.Passes.QSortPerm.qpartitionLoop
      (privateName ["Array", "qpartition", "loop"])
    let env := Lean.addAlias env `Fir.LeanIR.Passes.QSortPerm.qpartitionLoop_eq_def
      (privateName ["Array", "qpartition", "loop", "eq_def"])
    let env := Lean.addAlias env `Fir.LeanIR.Passes.QSortPerm.qsortLoop
      (privateName ["Array", "qsort", "sort"])
    Lean.addAlias env `Fir.LeanIR.Passes.QSortPerm.qsortLoop_eq_def
      (privateName ["Array", "qsort", "sort", "eq_def"])

/-- The partition worker changes its vector only by in-bounds swaps. -/
theorem qpartitionLoop_perm {α : Type u} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n)
    (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    Vector.Perm (qpartitionLoop lt lo hi hhi pivot as i k ilo ik w).2 as := by
  rw [qpartitionLoop_eq_def]
  split
  · split
    · exact
        (qpartitionLoop_perm lt lo hi hhi pivot (as.swap i k) (i + 1) (k + 1)
          (by omega) (by omega) (by omega)).trans
          (Vector.swap_perm (by omega) (by omega))
    · exact qpartitionLoop_perm lt lo hi hhi pivot as i (k + 1)
        ilo (by omega) (by omega)
  · exact Vector.swap_perm (by omega) hhi
termination_by hi - k

/-- Lean 4.33's partition implementation returns a permutation of its input. -/
theorem qpartition_perm {α : Type u} {n : Nat} (as : Vector α n)
    (lt : α → α → Bool) (lo hi : Nat) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) :
    Vector.Perm (Array.qpartition as lt lo hi w hlo hhi).2 as := by
  let mid := (lo + hi) / 2
  let as₁ := if lt as[mid] as[lo] then as.swap lo mid else as
  let as₂ := if lt as₁[hi] as₁[lo] then as₁.swap lo hi else as₁
  let as₃ := if lt as₂[mid] as₂[hi] then as₂.swap mid hi else as₂
  let pivot := as₃[hi]
  have mid_lt : mid < n := by
    dsimp [mid]
    omega
  have as₁_perm : Vector.Perm as₁ as := by
    dsimp [as₁]
    split
    · exact Vector.swap_perm hlo mid_lt
    · exact .rfl
  have as₂_perm : Vector.Perm as₂ as₁ := by
    dsimp [as₂]
    split
    · exact Vector.swap_perm hlo hhi
    · exact .rfl
  have as₃_perm : Vector.Perm as₃ as₂ := by
    dsimp [as₃]
    split
    · exact Vector.swap_perm mid_lt hhi
    · exact .rfl
  change Vector.Perm
    (qpartitionLoop lt lo hi hhi pivot as₃ lo lo (by omega) (by omega) w).2 as
  exact (qpartitionLoop_perm lt lo hi hhi pivot as₃ lo lo (by omega) (by omega) w).trans
    (as₃_perm.trans (as₂_perm.trans as₁_perm))

/-- The recursive vector worker used by `Array.qsort` preserves permutations. -/
theorem qsortLoop_perm {α : Type u} (lt : α → α → Bool) {n : Nat}
    (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi)
    (hlo : lo < n) (hhi : hi < n) :
    Vector.Perm (qsortLoop lt as lo hi w hlo hhi) as := by
  rw [qsortLoop_eq_def]
  split
  · rcases hpartition : Array.qpartition as lt lo hi w hlo hhi with
      ⟨⟨mid, hmid⟩, partitioned⟩
    simp only
    have partitioned_perm := qpartition_perm as lt lo hi w hlo hhi
    rw [hpartition] at partitioned_perm
    split
    · exact partitioned_perm
    · have left_perm := qsortLoop_perm lt partitioned lo mid
        (by omega) hlo (by omega)
      have right_perm := qsortLoop_perm lt
        (qsortLoop lt partitioned lo mid (by omega) hlo (by omega)) (mid + 1) hi
        (by omega) (by omega) hhi
      exact right_perm.trans (left_perm.trans partitioned_perm)
  · exact .rfl
termination_by (hi, hi - lo)

/-- Lean 4.33's public quicksort returns a permutation of its input array. -/
theorem qsort_perm {α : Type u} (as : Array α) (lt : α → α → Bool)
    (lo := 0) (hi := as.size - 1) :
    Array.Perm (Array.qsort as lt lo hi) as := by
  unfold Array.qsort
  split
  · exact .rfl
  · simpa using
      (qsortLoop_perm lt as.toVector (min lo (as.size - 1))
        (max (min lo (as.size - 1)) (min hi (as.size - 1)))
        (by omega) (by omega) (by omega)).toArray

end Fir.LeanIR.Passes.QSortPerm
