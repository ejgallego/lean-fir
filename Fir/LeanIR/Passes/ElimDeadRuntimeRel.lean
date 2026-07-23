import Fir.LeanIR.Passes.ElimDeadLiveness
import Fir.LeanIR.Passes.Structural

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.NonLockstep.Structural
open Fir.LeanIR.Passes.AlphaEqv

/-!
Reachability-aware runtime infrastructure for `elimDeadVars`.

The pass may remove allocations and writes to objects that cannot influence
future observations.  Consequently, the complete heaps and fresh-location
counters need not be equal.  This module builds on the shared address-renaming
and reachable-heap relations; it does not introduce a competing observation
notion.
-/

def RootSubset (smaller larger : List Value) : Prop :=
  ∀ value, value ∈ smaller → value ∈ larger

namespace RootSubset

theorem refl (roots : List Value) : RootSubset roots roots := by
  intro value member
  exact member

theorem trans
    (first : RootSubset left middle) (second : RootSubset middle right) :
    RootSubset left right := by
  intro value member
  exact second value (first value member)

end RootSubset

/-- Extend a partial address bijection with one fresh source/target pair. -/
def AddressRenaming.extend (rho : AddressRenaming)
    (left right : Location)
    (leftFresh : rho.forward left = none)
    (rightFresh : rho.reverse right = none) : AddressRenaming where
  forward := fun candidate =>
    if candidate = left then some right else rho.forward candidate
  reverse := fun candidate =>
    if candidate = right then some left else rho.reverse candidate
  leftInverse := by
    intro source target mapped
    by_cases sourceNew : source = left
    · subst source
      simp only [if_pos] at mapped
      cases mapped
      simp
    · simp only [sourceNew, if_false] at mapped
      have oldInverse := rho.leftInverse mapped
      have targetOld : target ≠ right := by
        intro same
        subst target
        rw [rightFresh] at oldInverse
        contradiction
      simp [targetOld, oldInverse]
  rightInverse := by
    intro source target mapped
    by_cases targetNew : target = right
    · subst target
      simp only [if_pos] at mapped
      cases mapped
      simp
    · simp only [targetNew, if_false] at mapped
      have oldInverse := rho.rightInverse mapped
      have sourceOld : source ≠ left := by
        intro same
        subst source
        rw [leftFresh] at oldInverse
        contradiction
      simp [sourceOld, oldInverse]

/-- Every mapping known before an extension remains known afterwards. -/
structure RenamingExtends (smaller larger : AddressRenaming) : Prop where
  forward : ∀ {left right}, smaller.forward left = some right →
    larger.forward left = some right
  reverse : ∀ {left right}, smaller.reverse right = some left →
    larger.reverse right = some left

namespace RenamingExtends

theorem refl (rho : AddressRenaming) : RenamingExtends rho rho := by
  exact ⟨fun mapped => mapped, fun mapped => mapped⟩

theorem trans
    (firstStep : RenamingExtends small middle)
    (secondStep : RenamingExtends middle large) :
    RenamingExtends small large := by
  exact ⟨fun mapped => secondStep.forward (firstStep.forward mapped),
    fun mapped => secondStep.reverse (firstStep.reverse mapped)⟩

end RenamingExtends

@[simp] theorem renamingExtend_forward_new
    (leftFresh : rho.forward left = none)
    (rightFresh : rho.reverse right = none) :
    (AddressRenaming.extend rho left right leftFresh rightFresh).forward left =
      some right := by
  simp [AddressRenaming.extend]

@[simp] theorem renamingExtend_reverse_new
    (leftFresh : rho.forward left = none)
    (rightFresh : rho.reverse right = none) :
    (AddressRenaming.extend rho left right leftFresh rightFresh).reverse right =
      some left := by
  simp [AddressRenaming.extend]

theorem renamingExtend_extends
    (leftFresh : rho.forward left = none)
    (rightFresh : rho.reverse right = none) :
    RenamingExtends rho
      (AddressRenaming.extend rho left right leftFresh rightFresh) := by
  constructor
  · intro source target mapped
    have different : source ≠ left := by
      intro same
      subst source
      rw [leftFresh] at mapped
      contradiction
    simp [AddressRenaming.extend, different, mapped]
  · intro source target mapped
    have different : target ≠ right := by
      intro same
      subst target
      rw [rightFresh] at mapped
      contradiction
    simp [AddressRenaming.extend, different, mapped]

theorem valueRel_mono
    (extension : RenamingExtends smaller larger)
    (related : ValueRel smaller left right) :
    ValueRel larger left right := by
  cases related with
  | tagged payload => exact .tagged payload
  | heap mapped => exact .heap (extension.forward mapped)
  | usize value => exact .usize value
  | scalar value => exact .scalar value
  | erased => exact .erased
  | reuseNone => exact .reuseNone
  | reuseSome mapped => exact .reuseSome (extension.forward mapped)

theorem listRel_mono
    (element : ∀ {left right}, relation left right → larger left right)
    (related : ListRel relation left right) :
    ListRel larger left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (element head) ih

theorem listRel_append
    (first : ListRel relation leftFirst rightFirst)
    (second : ListRel relation leftSecond rightSecond) :
    ListRel relation (leftFirst ++ leftSecond) (rightFirst ++ rightSecond) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem listRel_length_eq
    (related : ListRel relation left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem listRel_take (count : Nat)
    (related : ListRel relation left right) :
    ListRel relation (left.take count) (right.take count) := by
  induction related generalizing count with
  | nil => cases count <;> exact .nil
  | cons head tail ih =>
      cases count with
      | zero => exact .nil
      | succ count => exact .cons head (ih count)

theorem listRel_drop (count : Nat)
    (related : ListRel relation left right) :
    ListRel relation (left.drop count) (right.drop count) := by
  induction related generalizing count with
  | nil => cases count <;> exact .nil
  | cons head tail ih =>
      cases count with
      | zero => exact .cons head tail
      | succ count => exact ih count

/-- Replacing the same position by related elements preserves a pointwise
list relation. -/
theorem listRel_set (index : Nat)
    (related : ListRel relation left right)
    (element : relation leftValue rightValue) :
    ListRel relation
      (left.set index leftValue) (right.set index rightValue) := by
  induction related generalizing index with
  | nil =>
      cases index <;> exact .nil
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.set]
          exact .cons element tail
      | succ index =>
          simp only [List.set]
          exact .cons head (ih index)

theorem listRel_extract (start stop : Nat)
    (related : ListRel relation left right) :
    ListRel relation (left.extract start stop) (right.extract start stop) := by
  rw [List.extract_eq_take_drop, List.extract_eq_take_drop]
  exact listRel_take (stop - start) (listRel_drop start related)

theorem listRel_flatMap
    (related : ListRel relation left right)
    (elements : ∀ {leftValue rightValue}, relation leftValue rightValue →
      ListRel output (leftItems leftValue) (rightItems rightValue)) :
    ListRel output
      (left.flatMap leftItems) (right.flatMap rightItems) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact listRel_append (elements head) ih

theorem listRel_exists_right_of_mem
    (related : ListRel relation left right)
    (member : value ∈ left) :
    ∃ target, target ∈ right ∧ relation value target := by
  induction related with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      cases member with
      | inl same =>
          subst value
          exact ⟨_, List.mem_cons_self, head⟩
      | inr member =>
          rcases ih member with ⟨target, targetMember, targetRelated⟩
          exact ⟨target, List.mem_cons_of_mem _ targetMember, targetRelated⟩

theorem listRel_exists_left_of_mem
    (related : ListRel relation left right)
    (member : value ∈ right) :
    ∃ source, source ∈ left ∧ relation source value := by
  induction related with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      cases member with
      | inl same =>
          subst value
          exact ⟨_, List.mem_cons_self, head⟩
      | inr member =>
          rcases ih member with ⟨source, sourceMember, sourceRelated⟩
          exact ⟨source, List.mem_cons_of_mem _ sourceMember, sourceRelated⟩

theorem arrayRel_mono
    (element : ∀ {left right}, relation left right → larger left right)
    (related : ArrayRel relation left right) :
    ArrayRel larger left right :=
  listRel_mono element related

theorem arrayRel_size_eq
    (related : ArrayRel relation left right) : left.size = right.size := by
  simpa [ArrayRel] using listRel_length_eq related

/-- Replacing one array position by related elements preserves `ArrayRel`. -/
theorem arrayRel_set (index : Nat)
    (related : ArrayRel relation left right)
    (element : relation leftValue rightValue)
    (leftBound : index < left.size)
    (rightBound : index < right.size) :
    ArrayRel relation
      (left.set index leftValue) (right.set index rightValue) := by
  unfold ArrayRel at related ⊢
  simpa only [Array.toList_set] using
    listRel_set index related element

theorem arrayRel_extract (related : ArrayRel relation left right)
    (start stop : Nat) :
    ArrayRel relation (left.extract start stop) (right.extract start stop) := by
  unfold ArrayRel
  simp only [Array.toList_extract]
  exact listRel_extract start stop related

theorem arrayRel_append
    (first : ArrayRel relation leftFirst rightFirst)
    (second : ArrayRel relation leftSecond rightSecond) :
    ArrayRel relation (leftFirst ++ leftSecond) (rightFirst ++ rightSecond) := by
  unfold ArrayRel at first second ⊢
  simpa using listRel_append first second

theorem heapObjectRel_mono
    (extension : RenamingExtends smaller larger)
    (related : HeapObjectRel smaller left right) :
    HeapObjectRel larger left right := by
  cases related with
  | ctor tag objects usizes scalars =>
      exact .ctor tag (arrayRel_mono (valueRel_mono extension) objects)
        usizes scalars
  | closure fixed =>
      exact .closure (arrayRel_mono (valueRel_mono extension) fixed)
  | boxed value => exact .boxed (valueRel_mono extension value)
  | string value => exact .string value
  | natural value => exact .natural value
  | integer value => exact .integer value
  | byteArray value => exact .byteArray value
  | «opaque» typeName => exact .opaque typeName

theorem heapCellRel_mono
    (extension : RenamingExtends smaller larger)
    (related : HeapCellRel smaller left right) :
    HeapCellRel larger left right := by
  rcases related with ⟨rc, persistent, live, object⟩
  exact ⟨rc, persistent, live, heapObjectRel_mono extension object⟩

theorem heapObjectRel_ownedValues
    (related : HeapObjectRel rho left right) :
    ListRel (ValueRel rho)
      left.ownedValues.toList right.ownedValues.toList := by
  cases related with
  | ctor tag objects usizes scalars => exact objects
  | closure fixed => exact fixed
  | boxed value => exact .cons value .nil
  | string value | natural value | integer value | byteArray value
  | «opaque» value => exact .nil

theorem heapCellRel_ownedValues
    (related : HeapCellRel rho left right) :
    ListRel (ValueRel rho)
      left.object.ownedValues.toList right.object.ownedValues.toList :=
  heapObjectRel_ownedValues related.2.2.2

/-- Values retained by globals must remain available to later declarations. -/
def NamedValueRel (rho : AddressRenaming)
    (left right : Name × Value) : Prop :=
  left.1 = right.1 ∧ ValueRel rho left.2 right.2

/-- Related global tables make the same cache-hit decision and return related
values.  This is the address-renamed counterpart of exact global equality. -/
theorem findGlobal?_related
    (related : ListRel (NamedValueRel rho) left right) (name : Name) :
    OptionalRel (ValueRel rho)
      (findGlobal? left name) (findGlobal? right name) := by
  induction related with
  | nil => exact .none
  | cons head tail ih =>
      rename_i leftHead rightHead leftTail rightTail
      obtain ⟨nameEq, value⟩ := head
      obtain ⟨leftName, leftValue⟩ := leftHead
      obtain ⟨rightName, rightValue⟩ := rightHead
      simp only at nameEq value
      simp only [findGlobal?]
      rw [nameEq]
      cases rightName == name with
      | false => exact ih
      | true => exact .some value

theorem findGlobal?_value_mem
    (found : findGlobal? globals name = some value) :
    value ∈ globals.map Prod.snd := by
  induction globals with
  | nil => simp [findGlobal?] at found
  | cons head tail ih =>
      obtain ⟨candidate, candidateValue⟩ := head
      by_cases same : candidate == name
      · simp [findGlobal?, same] at found
        subst value
        exact List.mem_cons_self
      · have member := ih (by simpa [findGlobal?, same] using found)
        exact List.mem_cons_of_mem _ member

theorem eventRel_mono
    (extension : RenamingExtends smaller larger)
    (related : EventRel smaller left right) :
    EventRel larger left right := by
  rcases related with ⟨name, arguments, result⟩
  exact ⟨name, arrayRel_mono (valueRel_mono extension) arguments,
    valueRel_mono extension result⟩

theorem namedValueRel_mono
    (extension : RenamingExtends smaller larger)
    (related : NamedValueRel smaller left right) :
    NamedValueRel larger left right := by
  exact ⟨related.1, valueRel_mono extension related.2⟩

theorem outcomeRel_mono
    (extension : RenamingExtends smaller larger)
    (related : OutcomeRel smaller left right) :
    OutcomeRel larger left right := by
  cases left with
  | returned leftValue =>
      cases right with
      | returned rightValue => exact valueRel_mono extension related
      | fault fault => exact related.elim
  | fault leftFault =>
      cases right with
      | returned rightValue => exact related.elim
      | fault rightFault => exact related

theorem heapRel_monoRenaming
    (extension : RenamingExtends smaller larger)
    (related : HeapRel smaller left right leftRoots rightRoots) :
    HeapRel larger left right leftRoots rightRoots := by
  constructor
  · intro location reachable
    rcases related.1 location reachable with
      ⟨mapped, leftCell, rightCell, mapping, leftFound, rightFound, cell⟩
    exact ⟨mapped, leftCell, rightCell, extension.forward mapping, leftFound,
      rightFound, heapCellRel_mono extension cell⟩
  · intro location reachable
    rcases related.2 location reachable with
      ⟨mapped, rightCell, leftCell, mapping, rightFound, leftFound, cell⟩
    exact ⟨mapped, rightCell, leftCell, extension.reverse mapping, rightFound,
      leftFound, heapCellRel_mono extension cell⟩

/-- Reachability is monotone in the root set. -/
theorem reachable_monoRoots
    (subset : RootSubset smaller larger)
    (reachable : Reachable heap smaller location) :
    Reachable heap larger location := by
  induction reachable with
  | root member => exact .root (subset _ member)
  | child parentReachable cellFound member reference ih =>
      exact .child ih cellFound member reference

/-- A new root presentation may be justified semantically rather than by
literal list inclusion: it is enough that every heap reference named by a new
root is already reachable from the old roots. -/
theorem reachable_monoRootReachability
    (roots : ∀ location,
      Value.object (.heap location) ∈ smaller → Reachable heap larger location)
    (reachable : Reachable heap smaller location) :
    Reachable heap larger location := by
  induction reachable with
  | root member => exact roots _ member
  | child parentReachable cellFound member reference ih =>
      exact .child ih cellFound member reference

/-- A reachable-heap relation can be restricted to smaller roots without
changing either heap or the address renaming. -/
theorem heapRel_monoRoots
    (related : HeapRel rho left right leftLarger rightLarger)
    (leftSubset : RootSubset leftSmaller leftLarger)
    (rightSubset : RootSubset rightSmaller rightLarger) :
    HeapRel rho left right leftSmaller rightSmaller := by
  constructor
  · intro location reachable
    exact related.1 location (reachable_monoRoots leftSubset reachable)
  · intro location reachable
    exact related.2 location (reachable_monoRoots rightSubset reachable)

/-- Related roots and heap cells transport every reachable source location
to its renamed reachable target location. -/
theorem reachable_forward
    (roots : ListRel (ValueRel rho) leftRoots rightRoots)
    (related : HeapRel rho left right leftRoots rightRoots)
    (reachable : Reachable left leftRoots location) :
    ∃ target, rho.forward location = some target ∧
      Reachable right rightRoots target := by
  induction reachable with
  | root member =>
      rcases listRel_exists_right_of_mem roots member with
        ⟨targetValue, targetMember, value⟩
      cases value with
      | heap mapped => exact ⟨_, mapped, .root targetMember⟩
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      subst value
      rcases ih with ⟨targetParent, parentMapping, targetParentReachable⟩
      rcases related.1 parent parentReachable with
        ⟨mappedParent, sourceCell, targetCell, mapped, sourceFound,
          targetFound, cells⟩
      have parentEq : mappedParent = targetParent := by
        rw [parentMapping] at mapped
        exact (Option.some.inj mapped).symm
      subst mappedParent
      have cellEq : sourceCell = cell := by
        rw [cellFound] at sourceFound
        exact (Option.some.inj sourceFound).symm
      subst sourceCell
      rcases listRel_exists_right_of_mem
          (heapCellRel_ownedValues cells) member with
        ⟨targetValue, targetMember, value⟩
      cases value with
      | heap childMapping =>
          exact ⟨_, childMapping,
            .child targetParentReachable targetFound targetMember rfl⟩

/-- Symmetric reachable-location transport, stated with the reverse map. -/
theorem reachable_reverse
    (roots : ListRel (ValueRel rho) leftRoots rightRoots)
    (related : HeapRel rho left right leftRoots rightRoots)
    (reachable : Reachable right rightRoots location) :
    ∃ source, rho.reverse location = some source ∧
      Reachable left leftRoots source := by
  induction reachable with
  | root member =>
      rcases listRel_exists_left_of_mem roots member with
        ⟨sourceValue, sourceMember, value⟩
      cases value with
      | heap mapped =>
          exact ⟨_, rho.leftInverse mapped, .root sourceMember⟩
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      subst value
      rcases ih with ⟨sourceParent, parentMapping, sourceParentReachable⟩
      rcases related.2 parent parentReachable with
        ⟨mappedParent, targetCell, sourceCell, mapped, targetFound,
          sourceFound, cells⟩
      have parentEq : mappedParent = sourceParent := by
        rw [parentMapping] at mapped
        exact (Option.some.inj mapped).symm
      subst mappedParent
      have cellEq : targetCell = cell := by
        rw [cellFound] at targetFound
        exact (Option.some.inj targetFound).symm
      subst targetCell
      rcases listRel_exists_left_of_mem
          (heapCellRel_ownedValues cells) member with
        ⟨sourceValue, sourceMember, value⟩
      cases value with
      | heap childMapping =>
          exact ⟨_, rho.leftInverse childMapping,
            .child sourceParentReachable sourceFound sourceMember rfl⟩

/-- Replacing an unreachable cell cannot create a new path from the existing
roots: every traversed parent is either different from the replacement point
or would itself contradict unreachability. -/
theorem reachable_of_heapFrame_of_unreachable
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (unreachable : ¬Reachable before roots modified)
    (reachable : Reachable after roots location) :
    Reachable before roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      have different : parent ≠ modified := by
        intro same
        subst parent
        exact unreachable ih
      have beforeFound : findCell? before parent = some cell := by
        rw [← frame parent different]
        exact cellFound
      exact .child ih beforeFound member reference

/-- Existing reachability is likewise preserved by a heap update outside the
reachable subgraph. -/
theorem reachable_heapFrame_of_unreachable
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (unreachable : ¬Reachable before roots modified)
    (reachable : Reachable before roots location) :
    Reachable after roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      have different : parent ≠ modified := by
        intro same
        subst parent
        exact unreachable parentReachable
      have afterFound : findCell? after parent = some cell := by
        rw [frame parent different]
        exact cellFound
      exact .child ih afterFound member reference

/-- Replacing one cell without changing its owned values preserves the
reachability graph.  This is the live-cell counterpart of the unreachable
frame lemmas above: mutation may change metadata or non-owning fields, but it
cannot add or remove an ownership edge. -/
theorem reachable_replace_of_ownedValues_eq
    (beforeFound : findCell? before modified = some beforeCell)
    (afterFound : findCell? after modified = some afterCell)
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (owned : afterCell.object.ownedValues = beforeCell.object.ownedValues)
    (reachable : Reachable after roots location) :
    Reachable before roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      by_cases same : parent = modified
      · subst parent
        have cellEq : cell = afterCell := by
          rw [afterFound] at cellFound
          exact (Option.some.inj cellFound).symm
        subst cell
        exact .child ih beforeFound (by simpa [owned] using member) reference
      · have found : findCell? before parent = some cell := by
          rw [← frame parent same]
          exact cellFound
        exact .child ih found member reference

/-- Replacing a cell may add ownership edges when every newly owned heap
reference was already reachable from the published roots.  This is the live
object-field update rule: overwriting an edge can forget reachability, while
the inserted live value cannot reveal a previously hidden component. -/
theorem reachable_replace_of_ownedValues_rooted
    (beforeFound : findCell? before modified = some beforeCell)
    (afterFound : findCell? after modified = some afterCell)
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (owned : ∀ {child},
      Value.object (.heap child) ∈ afterCell.object.ownedValues.toList →
        Value.object (.heap child) ∈
            beforeCell.object.ownedValues.toList ∨
          Reachable before roots child)
    (reachable : Reachable after roots location) :
    Reachable before roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      by_cases same : parent = modified
      · subst parent
        have cellEq : cell = afterCell := by
          rw [afterFound] at cellFound
          exact (Option.some.inj cellFound).symm
        subst cell
        subst value
        rcases owned member with oldMember | rooted
        · exact .child ih beforeFound oldMember rfl
        · exact rooted
      · have found : findCell? before parent = some cell := by
          rw [← frame parent same]
          exact cellFound
        exact .child ih found member reference

/-- Replacing one mapped pair with related cells while preserving ownership
edges preserves the bidirectional reachable-heap relation. -/
theorem heapRel_replaceBoth
    (related : HeapRel rho leftBefore rightBefore leftRoots rightRoots)
    (mapping : rho.forward leftModified = some rightModified)
    (leftBeforeFound :
      findCell? leftBefore leftModified = some leftBeforeCell)
    (rightBeforeFound :
      findCell? rightBefore rightModified = some rightBeforeCell)
    (leftAfterFound :
      findCell? leftAfter leftModified = some leftAfterCell)
    (rightAfterFound :
      findCell? rightAfter rightModified = some rightAfterCell)
    (leftFrame : ∀ other, other ≠ leftModified →
      findCell? leftAfter other = findCell? leftBefore other)
    (rightFrame : ∀ other, other ≠ rightModified →
      findCell? rightAfter other = findCell? rightBefore other)
    (leftOwned :
      leftAfterCell.object.ownedValues =
        leftBeforeCell.object.ownedValues)
    (rightOwned :
      rightAfterCell.object.ownedValues =
        rightBeforeCell.object.ownedValues)
    (cells : HeapCellRel rho leftAfterCell rightAfterCell) :
    HeapRel rho leftAfter rightAfter leftRoots rightRoots := by
  constructor
  · intro location afterReachable
    have beforeReachable := reachable_replace_of_ownedValues_eq
      leftBeforeFound leftAfterFound leftFrame leftOwned afterReachable
    rcases related.1 location beforeReachable with
      ⟨mapped, leftCell, rightCell, mappedEq, leftFound, rightFound,
        oldCells⟩
    by_cases same : location = leftModified
    · subst location
      have mappedSame : mapped = rightModified := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mapped
      have leftCellSame : leftCell = leftBeforeCell := by
        rw [leftBeforeFound] at leftFound
        exact (Option.some.inj leftFound).symm
      have rightCellSame : rightCell = rightBeforeCell := by
        rw [rightBeforeFound] at rightFound
        exact (Option.some.inj rightFound).symm
      subst leftCell
      subst rightCell
      exact ⟨rightModified, leftAfterCell, rightAfterCell, mapping,
        leftAfterFound, rightAfterFound, cells⟩
    · have mappedDifferent : mapped ≠ rightModified := by
        intro mappedSame
        subst mapped
        have oldInverse := rho.leftInverse mappedEq
        have newInverse := rho.leftInverse mapping
        rw [newInverse] at oldInverse
        exact same (Option.some.inj oldInverse).symm
      exact ⟨mapped, leftCell, rightCell, mappedEq,
        by simpa [leftFrame location same] using leftFound,
        by simpa [rightFrame mapped mappedDifferent] using rightFound,
        oldCells⟩
  · intro location afterReachable
    have beforeReachable := reachable_replace_of_ownedValues_eq
      rightBeforeFound rightAfterFound rightFrame rightOwned afterReachable
    rcases related.2 location beforeReachable with
      ⟨mapped, rightCell, leftCell, mappedEq, rightFound, leftFound,
        oldCells⟩
    have reverseMapping := rho.leftInverse mapping
    by_cases same : location = rightModified
    · subst location
      have mappedSame : mapped = leftModified := by
        rw [reverseMapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mapped
      have rightCellSame : rightCell = rightBeforeCell := by
        rw [rightBeforeFound] at rightFound
        exact (Option.some.inj rightFound).symm
      have leftCellSame : leftCell = leftBeforeCell := by
        rw [leftBeforeFound] at leftFound
        exact (Option.some.inj leftFound).symm
      subst rightCell
      subst leftCell
      exact ⟨leftModified, rightAfterCell, leftAfterCell, reverseMapping,
        rightAfterFound, leftAfterFound, cells⟩
    · have mappedDifferent : mapped ≠ leftModified := by
        intro mappedSame
        subst mapped
        have oldForward := rho.rightInverse mappedEq
        rw [mapping] at oldForward
        exact same (Option.some.inj oldForward).symm
      exact ⟨mapped, rightCell, leftCell, mappedEq,
        by simpa [rightFrame location same] using rightFound,
        by simpa [leftFrame mapped mappedDifferent] using leftFound,
        oldCells⟩

/-- Replacing one mapped pair with related cells also preserves `HeapRel`
when any newly introduced ownership edge points into the already reachable
subgraph on its respective side. -/
theorem heapRel_replaceBothRooted
    (related : HeapRel rho leftBefore rightBefore leftRoots rightRoots)
    (mapping : rho.forward leftModified = some rightModified)
    (leftBeforeFound :
      findCell? leftBefore leftModified = some leftBeforeCell)
    (rightBeforeFound :
      findCell? rightBefore rightModified = some rightBeforeCell)
    (leftAfterFound :
      findCell? leftAfter leftModified = some leftAfterCell)
    (rightAfterFound :
      findCell? rightAfter rightModified = some rightAfterCell)
    (leftFrame : ∀ other, other ≠ leftModified →
      findCell? leftAfter other = findCell? leftBefore other)
    (rightFrame : ∀ other, other ≠ rightModified →
      findCell? rightAfter other = findCell? rightBefore other)
    (leftOwned : ∀ {child},
      Value.object (.heap child) ∈
          leftAfterCell.object.ownedValues.toList →
        Value.object (.heap child) ∈
            leftBeforeCell.object.ownedValues.toList ∨
          Reachable leftBefore leftRoots child)
    (rightOwned : ∀ {child},
      Value.object (.heap child) ∈
          rightAfterCell.object.ownedValues.toList →
        Value.object (.heap child) ∈
            rightBeforeCell.object.ownedValues.toList ∨
          Reachable rightBefore rightRoots child)
    (cells : HeapCellRel rho leftAfterCell rightAfterCell) :
    HeapRel rho leftAfter rightAfter leftRoots rightRoots := by
  constructor
  · intro location afterReachable
    have beforeReachable := reachable_replace_of_ownedValues_rooted
      leftBeforeFound leftAfterFound leftFrame leftOwned afterReachable
    rcases related.1 location beforeReachable with
      ⟨mapped, leftCell, rightCell, mappedEq, leftFound, rightFound,
        oldCells⟩
    by_cases same : location = leftModified
    · subst location
      have mappedSame : mapped = rightModified := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mapped
      have leftCellSame : leftCell = leftBeforeCell := by
        rw [leftBeforeFound] at leftFound
        exact (Option.some.inj leftFound).symm
      have rightCellSame : rightCell = rightBeforeCell := by
        rw [rightBeforeFound] at rightFound
        exact (Option.some.inj rightFound).symm
      subst leftCell
      subst rightCell
      exact ⟨rightModified, leftAfterCell, rightAfterCell, mapping,
        leftAfterFound, rightAfterFound, cells⟩
    · have mappedDifferent : mapped ≠ rightModified := by
        intro mappedSame
        subst mapped
        have oldInverse := rho.leftInverse mappedEq
        have newInverse := rho.leftInverse mapping
        rw [newInverse] at oldInverse
        exact same (Option.some.inj oldInverse).symm
      exact ⟨mapped, leftCell, rightCell, mappedEq,
        by simpa [leftFrame location same] using leftFound,
        by simpa [rightFrame mapped mappedDifferent] using rightFound,
        oldCells⟩
  · intro location afterReachable
    have beforeReachable := reachable_replace_of_ownedValues_rooted
      rightBeforeFound rightAfterFound rightFrame rightOwned afterReachable
    rcases related.2 location beforeReachable with
      ⟨mapped, rightCell, leftCell, mappedEq, rightFound, leftFound,
        oldCells⟩
    have reverseMapping := rho.leftInverse mapping
    by_cases same : location = rightModified
    · subst location
      have mappedSame : mapped = leftModified := by
        rw [reverseMapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mapped
      have rightCellSame : rightCell = rightBeforeCell := by
        rw [rightBeforeFound] at rightFound
        exact (Option.some.inj rightFound).symm
      have leftCellSame : leftCell = leftBeforeCell := by
        rw [leftBeforeFound] at leftFound
        exact (Option.some.inj leftFound).symm
      subst rightCell
      subst leftCell
      exact ⟨leftModified, rightAfterCell, leftAfterCell, reverseMapping,
        rightAfterFound, leftAfterFound, cells⟩
    · have mappedDifferent : mapped ≠ leftModified := by
        intro mappedSame
        subst mapped
        have oldForward := rho.rightInverse mappedEq
        rw [mapping] at oldForward
        exact same (Option.some.inj oldForward).symm
      exact ⟨mapped, rightCell, leftCell, mappedEq,
        by simpa [rightFrame location same] using rightFound,
        by simpa [leftFrame mapped mappedDifferent] using leftFound,
        oldCells⟩

/-- Updating a source cell outside the reachable subgraph preserves the
reachable-heap relation.  Target-to-source reachability transport is what
rules out the modified cell in the reverse half of `HeapRel`. -/
theorem heapRel_frameLeft_of_unreachable
    (roots : ListRel (ValueRel rho) leftRoots rightRoots)
    (related : HeapRel rho before right leftRoots rightRoots)
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (unreachable : ¬Reachable before leftRoots modified) :
    HeapRel rho after right leftRoots rightRoots := by
  constructor
  · intro location afterReachable
    have beforeReachable :=
      reachable_of_heapFrame_of_unreachable frame unreachable afterReachable
    rcases related.1 location beforeReachable with
      ⟨mapped, sourceCell, targetCell, mapping, sourceFound,
        targetFound, cells⟩
    have different : location ≠ modified := by
      intro same
      subst location
      exact unreachable beforeReachable
    exact ⟨mapped, sourceCell, targetCell, mapping,
      by simpa [frame location different] using sourceFound,
      targetFound, cells⟩
  · intro location targetReachable
    rcases related.2 location targetReachable with
      ⟨mapped, targetCell, sourceCell, mapping, targetFound,
        sourceFound, cells⟩
    rcases reachable_reverse roots related targetReachable with
      ⟨reachableSource, reachableMapping, sourceReachable⟩
    have sourceEq : reachableSource = mapped := by
      rw [mapping] at reachableMapping
      exact (Option.some.inj reachableMapping).symm
    subst reachableSource
    have different : mapped ≠ modified := by
      intro same
      subst mapped
      exact unreachable sourceReachable
    exact ⟨mapped, targetCell, sourceCell, mapping, targetFound,
      by simpa [frame mapped different] using sourceFound, cells⟩

/-- A whole-heap update is observationally outside `roots` when every cell
reachable before the update has exactly the same lookup afterwards. -/
def HeapReachableFrame (before after : Heap) (roots : List Value) : Prop :=
  ∀ location, Reachable before roots location →
    findCell? after location = findCell? before location

theorem reachable_of_heapReachableFrame
    (frame : HeapReachableFrame before after roots)
    (reachable : Reachable after roots location) :
    Reachable before roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      have beforeFound : findCell? before parent = some cell := by
        rw [← frame parent ih]
        exact cellFound
      exact .child ih beforeFound member reference

theorem reachable_heapReachableFrame
    (frame : HeapReachableFrame before after roots)
    (reachable : Reachable before roots location) :
    Reachable after roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      have afterFound : findCell? after parent = some cell := by
        rw [frame parent parentReachable]
        exact cellFound
      exact .child ih afterFound member reference

/-- A whole-heap source update preserving every live-root-reachable lookup
preserves the bidirectional reachable heap relation. -/
theorem heapRel_frameLeft_of_reachableFrame
    (roots : ListRel (ValueRel rho) leftRoots rightRoots)
    (related : HeapRel rho before right leftRoots rightRoots)
    (frame : HeapReachableFrame before after leftRoots) :
    HeapRel rho after right leftRoots rightRoots := by
  constructor
  · intro location afterReachable
    have beforeReachable :=
      reachable_of_heapReachableFrame frame afterReachable
    rcases related.1 location beforeReachable with
      ⟨mapped, sourceCell, targetCell, mapping, sourceFound,
        targetFound, cells⟩
    exact ⟨mapped, sourceCell, targetCell, mapping,
      by simpa [frame location beforeReachable] using sourceFound,
      targetFound, cells⟩
  · intro location targetReachable
    rcases related.2 location targetReachable with
      ⟨mapped, targetCell, sourceCell, mapping, targetFound,
        sourceFound, cells⟩
    rcases reachable_reverse roots related targetReachable with
      ⟨reachableSource, reachableMapping, sourceReachable⟩
    have sourceEq : reachableSource = mapped := by
      rw [mapping] at reachableMapping
      exact (Option.some.inj reachableMapping).symm
    subst reachableSource
    exact ⟨mapped, targetCell, sourceCell, mapping, targetFound,
      by simpa [frame mapped sourceReachable] using sourceFound, cells⟩

/-- Prepending a cell at an unmapped source location cannot make it reachable
from roots already governed by the old heap relation. -/
theorem reachable_cons_of_forward_unmapped
    (related : HeapRel rho heap other roots otherRoots)
    (unmapped : rho.forward fresh = none)
    (reachable : Reachable ((fresh, garbage) :: heap) roots location) :
    Reachable heap roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      have parentDifferent : fresh ≠ parent := by
        intro same
        subst parent
        rcases related.1 fresh ih with
          ⟨mapped, leftCell, rightCell, mapping, leftFound, rightFound, cell⟩
        rw [unmapped] at mapping
        contradiction
      have oldFound : findCell? heap parent = some cell := by
        simpa [findCell?, parentDifferent] using cellFound
      exact .child ih oldFound member reference

/-- Adding unreachable garbage at an unmapped source address preserves the
reachable-heap relation. -/
theorem heapRel_consLeft_of_forward_unmapped
    (related : HeapRel rho left right leftRoots rightRoots)
    (unmapped : rho.forward fresh = none) :
    HeapRel rho ((fresh, garbage) :: left) right leftRoots rightRoots := by
  constructor
  · intro location reachable
    have oldReachable :=
      reachable_cons_of_forward_unmapped related unmapped reachable
    rcases related.1 location oldReachable with
      ⟨mapped, leftCell, rightCell, mapping, leftFound, rightFound, cell⟩
    have different : fresh ≠ location := by
      intro same
      subst location
      rw [unmapped] at mapping
      contradiction
    exact ⟨mapped, leftCell, rightCell, mapping,
      by simpa [findCell?, different] using leftFound, rightFound, cell⟩
  · intro location reachable
    rcases related.2 location reachable with
      ⟨mapped, rightCell, leftCell, mapping, rightFound, leftFound, cell⟩
    have forward := rho.rightInverse mapping
    have different : fresh ≠ mapped := by
      intro same
      subst mapped
      rw [unmapped] at forward
      contradiction
    exact ⟨mapped, rightCell, leftCell, mapping, rightFound,
      by simpa [findCell?, different] using leftFound, cell⟩

/-- Adding a fresh root and its cell exposes either that new location or a
location already reachable through the old roots, provided every child of the
new cell was already live. -/
theorem reachable_cons_root_cases_forward
    (related : HeapRel rho heap other roots otherRoots)
    (unmapped : rho.forward fresh = none)
    (owned : RootSubset newCell.object.ownedValues.toList roots)
    (reachable : Reachable ((fresh, newCell) :: heap)
      (.object (.heap fresh) :: roots) location) :
    location = fresh ∨ Reachable heap roots location := by
  induction reachable with
  | root member =>
      simp only [List.mem_cons] at member
      cases member with
      | inl same =>
          simp at same
          exact .inl same
      | inr old => exact .inr (.root old)
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      cases ih with
      | inl parentNew =>
          subst parent
          have cellEq : cell = newCell := by
            symm
            simpa [findCell?] using cellFound
          subst cell
          subst value
          exact .inr (.root (owned _ member))
      | inr parentOld =>
          have parentDifferent : fresh ≠ parent := by
            intro same
            subst parent
            rcases related.1 fresh parentOld with
              ⟨mapped, leftCell, rightCell, mapping, leftFound, rightFound,
                cellRelated⟩
            rw [unmapped] at mapping
            contradiction
          have oldFound : findCell? heap parent = some cell := by
            simpa [findCell?, parentDifferent] using cellFound
          exact .inr (.child parentOld oldFound member reference)

/-- Reverse-oriented companion of `reachable_cons_root_cases_forward`. -/
theorem reachable_cons_root_cases_reverse
    (related : HeapRel rho other heap otherRoots roots)
    (unmapped : rho.reverse fresh = none)
    (owned : RootSubset newCell.object.ownedValues.toList roots)
    (reachable : Reachable ((fresh, newCell) :: heap)
      (.object (.heap fresh) :: roots) location) :
    location = fresh ∨ Reachable heap roots location := by
  induction reachable with
  | root member =>
      simp only [List.mem_cons] at member
      cases member with
      | inl same =>
          simp at same
          exact .inl same
      | inr old => exact .inr (.root old)
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      cases ih with
      | inl parentNew =>
          subst parent
          have cellEq : cell = newCell := by
            symm
            simpa [findCell?] using cellFound
          subst cell
          subst value
          exact .inr (.root (owned _ member))
      | inr parentOld =>
          have parentDifferent : fresh ≠ parent := by
            intro same
            subst parent
            rcases related.2 fresh parentOld with
              ⟨mapped, rightCell, leftCell, mapping, rightFound, leftFound,
                cellRelated⟩
            rw [unmapped] at mapping
            contradiction
          have oldFound : findCell? heap parent = some cell := by
            simpa [findCell?, parentDifferent] using cellFound
          exact .inr (.child parentOld oldFound member reference)

/-- Simultaneous allocation extends the address bijection at the two fresh
locations.  New object children must already occur among the old live roots;
all old mappings and reachable cells are preserved. -/
theorem heapRel_consBoth
    (related : HeapRel rho leftHeap rightHeap leftRoots rightRoots)
    (leftUnmapped : rho.forward leftLocation = none)
    (rightUnmapped : rho.reverse rightLocation = none)
    (cells : HeapCellRel rho leftCell rightCell)
    (leftOwned : RootSubset leftCell.object.ownedValues.toList leftRoots)
    (rightOwned : RootSubset rightCell.object.ownedValues.toList rightRoots) :
    HeapRel
      (AddressRenaming.extend rho leftLocation rightLocation
        leftUnmapped rightUnmapped)
      ((leftLocation, leftCell) :: leftHeap)
      ((rightLocation, rightCell) :: rightHeap)
      (.object (.heap leftLocation) :: leftRoots)
      (.object (.heap rightLocation) :: rightRoots) := by
  let larger := AddressRenaming.extend rho leftLocation rightLocation
    leftUnmapped rightUnmapped
  have extension : RenamingExtends rho larger :=
    renamingExtend_extends leftUnmapped rightUnmapped
  have largerCells : HeapCellRel larger leftCell rightCell :=
    heapCellRel_mono extension cells
  change HeapRel larger _ _ _ _
  constructor
  · intro location reachable
    rcases reachable_cons_root_cases_forward related leftUnmapped leftOwned
      reachable with new | old
    · subst location
      exact ⟨rightLocation, leftCell, rightCell,
        renamingExtend_forward_new leftUnmapped rightUnmapped,
        by simp [findCell?], by simp [findCell?], largerCells⟩
    · rcases related.1 location old with
        ⟨mapped, oldLeftCell, oldRightCell, mapping, leftFound, rightFound,
          oldCells⟩
      have leftDifferent : leftLocation ≠ location := by
        intro same
        subst location
        rw [leftUnmapped] at mapping
        contradiction
      have rightDifferent : rightLocation ≠ mapped := by
        intro same
        subst mapped
        have inverse := rho.leftInverse mapping
        rw [rightUnmapped] at inverse
        contradiction
      exact ⟨mapped, oldLeftCell, oldRightCell, extension.forward mapping,
        by simpa [findCell?, leftDifferent] using leftFound,
        by simpa [findCell?, rightDifferent] using rightFound,
        heapCellRel_mono extension oldCells⟩
  · intro location reachable
    rcases reachable_cons_root_cases_reverse related rightUnmapped rightOwned
      reachable with new | old
    · subst location
      exact ⟨leftLocation, rightCell, leftCell,
        renamingExtend_reverse_new leftUnmapped rightUnmapped,
        by simp [findCell?], by simp [findCell?], largerCells⟩
    · rcases related.2 location old with
        ⟨mapped, oldRightCell, oldLeftCell, mapping, rightFound, leftFound,
          oldCells⟩
      have rightDifferent : rightLocation ≠ location := by
        intro same
        subst location
        rw [rightUnmapped] at mapping
        contradiction
      have leftDifferent : leftLocation ≠ mapped := by
        intro same
        subst mapped
        have inverse := rho.rightInverse mapping
        rw [leftUnmapped] at inverse
        contradiction
      exact ⟨mapped, oldRightCell, oldLeftCell, extension.reverse mapping,
        by simpa [findCell?, rightDifferent] using rightFound,
        by simpa [findCell?, leftDifferent] using leftFound,
        heapCellRel_mono extension oldCells⟩

theorem not_reachable_from_empty
    (reachable : Reachable heap [] location) : False := by
  induction reachable with
  | root member => simp at member
  | child parentReachable cellFound member reference ih => exact ih

def traceRoots (trace : Array ExternalEvent) : List Value :=
  trace.toList.flatMap fun event => event.result :: event.args.toList

theorem globalsRoots_related
    (related : ListRel (NamedValueRel rho) left right) :
    ListRel (ValueRel rho)
      (left.map Prod.snd) (right.map Prod.snd) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.2 ih

theorem traceRoots_related
    (related : ArrayRel (EventRel rho) left right) :
    ListRel (ValueRel rho) (traceRoots left) (traceRoots right) := by
  unfold ArrayRel at related
  unfold traceRoots
  apply listRel_flatMap related
  intro leftEvent rightEvent event
  exact .cons event.2.2 event.2.1

def outcomeRoots : Outcome → List Value
  | .returned value => [value]
  | .fault _ => []

/-- `extra` contains control-, environment-, and frame-specific roots.  The
runtime contributes globals and the already observable external trace. -/
def runtimeRoots (runtime : RuntimeState) (extra : List Value) : List Value :=
  extra ++ runtime.globals.map Prod.snd ++ traceRoots runtime.trace

theorem extra_subset_runtimeRoots (runtime : RuntimeState) (extra : List Value) :
    RootSubset extra (runtimeRoots runtime extra) := by
  intro value member
  simp [runtimeRoots, member]

theorem runtimeRoots_monoExtra
    (subset : RootSubset smaller larger) :
    RootSubset (runtimeRoots runtime smaller) (runtimeRoots runtime larger) := by
  intro value member
  simp only [runtimeRoots, List.mem_append] at member ⊢
  rcases member with (member | member) | member
  · exact Or.inl (Or.inl (subset value member))
  · exact Or.inl (Or.inr member)
  · exact Or.inr member

/-- Environments agree relationally on precisely the variables retained by
the backwards liveness graph. -/
def EnvRelOn (rho : AddressRenaming) (used : UsedLocals)
    (left right : Env) : Prop :=
  ∀ fvarId, used.contains fvarId = true →
    OptionalRel (ValueRel rho) (lookup left fvarId) (lookup right fvarId)

theorem EnvRelOn.empty (rho : AddressRenaming) (used : UsedLocals) :
    EnvRelOn rho used [] [] := by
  intro fvarId member
  exact .none

/-- Canonical runtime roots contributed by the live portion of an
environment.  `filterMap` drops malformed/missing live lookups symmetrically. -/
def envRootsOn (used : UsedLocals) (env : Env) : List Value :=
  used.toList.filterMap (lookup env)

theorem lookup_mem_envRootsOn
    (member : used.contains fvarId = true)
    (found : lookup env fvarId = some value) :
    value ∈ envRootsOn used env := by
  unfold envRootsOn
  simp only [List.mem_filterMap]
  exact ⟨fvarId, Std.HashSet.mem_toList.mpr member, found⟩

theorem filterMap_eq_of_mem_eq
    (keys : List α) (left right : α → Option β)
    (equal : ∀ key, key ∈ keys → left key = right key) :
    keys.filterMap left = keys.filterMap right := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      have head := equal key (by simp)
      have tail : ∀ candidate, candidate ∈ rest →
          left candidate = right candidate := by
        intro candidate member
        exact equal candidate (by simp [member])
      simp [List.filterMap, head, ih tail]

/-- Binding a variable excluded by the active liveness set leaves the
canonical environment roots definitionally unchanged. -/
theorem envRootsOn_bind_of_absent
    (absent : used.contains binder = false) :
    envRootsOn used (bind env binder value) = envRootsOn used env := by
  unfold envRootsOn
  apply filterMap_eq_of_mem_eq
  intro fvarId member
  apply lookup_bind_of_name_ne
  apply fvarId_name_ne_of_contains_of_absent used fvarId binder
  · change fvarId ∈ used
    exact Std.HashSet.mem_toList.mp member
  · exact absent

/-- Every root published after a binding is either the newly bound value or
an old environment root.  This is the root-set fact used when a yielded value
is installed into a saved bind frame. -/
theorem envRootsOn_bind_subset :
    RootSubset (envRootsOn used (bind env binder value))
      (value :: envRootsOn used env) := by
  intro root member
  unfold envRootsOn at member
  simp only [List.mem_filterMap] at member
  rcases member with ⟨fvarId, keyMember, found⟩
  by_cases sameName : binder.name = fvarId.name
  · have sameId : binder = fvarId := by
      cases binder with
      | mk binderName =>
          cases fvarId with
          | mk fvarName => simp_all
    subst fvarId
    rw [lookup_bind_self] at found
    cases found
    simp
  · right
    unfold envRootsOn
    apply List.mem_filterMap.mpr
    exact ⟨fvarId, keyMember,
      by simpa [lookup_bind_of_name_ne sameName] using found⟩

/-- Roots in an environment produced by binding a parameter/value prefix
come either from those values or from the starting environment. -/
theorem envRootsOn_bindPairs_subset
    (params : List (LCNF.Param .impure)) (values : List Value) :
    RootSubset
      (envRootsOn used
        ((params.zip values).foldl
          (fun env pair => bind env pair.1.fvarId pair.2) sourceEnv))
      (values ++ envRootsOn used sourceEnv) := by
  induction values generalizing params sourceEnv with
  | nil =>
      simpa using (RootSubset.refl (envRootsOn used sourceEnv))
  | cons value values ih =>
      cases params with
      | nil =>
          intro root member
          simp only [List.zip, List.foldl_nil, List.mem_append,
            List.mem_cons]
          exact Or.inr member
      | cons param params =>
          simp only [List.zip, List.foldl_cons]
          intro root member
          have next := ih (params := params)
            (sourceEnv := bind sourceEnv param.fvarId value) root member
          simp only [List.mem_append, List.mem_cons] at next ⊢
          rcases next with later | rebound
          · exact Or.inl (Or.inr later)
          · have rooted := envRootsOn_bind_subset root rebound
            simp only [List.mem_cons] at rooted
            rcases rooted with same | old
            · exact Or.inl (Or.inl same)
            · exact Or.inr old

theorem envRootsOn_bindParams_subset
    (bound : bindParams params arguments = .ok env) :
    RootSubset (envRootsOn used env) arguments.toList := by
  unfold bindParams at bound
  cases arityEq : params.size == arguments.size with
  | false => simp [arityEq] at bound
  | true =>
      simp [arityEq] at bound
      subst env
      have roots := envRootsOn_bindPairs_subset
        (used := used) (sourceEnv := []) params.toList arguments.toList
      intro root member
      rcases List.mem_append.mp (roots root member) with
        inArguments | inEmpty
      · exact inArguments
      · simp [envRootsOn, lookup] at inEmpty

/-- Binding join parameters over an existing environment publishes only
argument values or roots that were already published by that environment. -/
theorem envRootsOn_bindParamsOver_subset
    (bound : bindParamsOver sourceEnv params arguments = .ok targetEnv) :
    RootSubset (envRootsOn used targetEnv)
      (arguments.toList ++ envRootsOn used sourceEnv) := by
  unfold bindParamsOver at bound
  cases arityEq : params.size == arguments.size with
  | false => simp [arityEq] at bound
  | true =>
      simp [arityEq] at bound
      subst targetEnv
      exact envRootsOn_bindPairs_subset params.toList arguments.toList

/-- The call and extra-argument slices used by `invokeDecl` partition the
original argument array. -/
theorem array_extract_partition (values : Array α) (split : Nat) :
    (values.extract 0 split).toList ++
      (values.extract split values.size).toList = values.toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  rw [← Array.length_toList]
  have tail :
      List.take (values.toList.length - split) (values.toList.drop split) =
        values.toList.drop split := by
    rw [← List.length_drop]
    exact List.take_length
  rw [tail]
  exact List.take_append_drop split values.toList

theorem lookupRoots_related
    (keys : List FVarId)
    (agree : ∀ key, key ∈ keys →
      OptionalRel (ValueRel rho) (lookup left key) (lookup right key)) :
    ListRel (ValueRel rho)
      (keys.filterMap (lookup left)) (keys.filterMap (lookup right)) := by
  induction keys with
  | nil => exact .nil
  | cons key rest ih =>
      have head := agree key (by simp)
      have tail : ∀ candidate, candidate ∈ rest →
          OptionalRel (ValueRel rho) (lookup left candidate)
            (lookup right candidate) := by
        intro candidate member
        exact agree candidate (by simp [member])
      cases leftLookup : lookup left key with
      | none =>
          cases rightLookup : lookup right key with
          | none => simpa [List.filterMap, leftLookup, rightLookup] using ih tail
          | some rightValue =>
              rw [leftLookup, rightLookup] at head
              cases head
      | some leftValue =>
          cases rightLookup : lookup right key with
          | none =>
              rw [leftLookup, rightLookup] at head
              cases head
          | some rightValue =>
              rw [leftLookup, rightLookup] at head
              cases head with
              | some related =>
                  simpa [List.filterMap, leftLookup, rightLookup] using
                    ListRel.cons related (ih tail)

theorem envRootsOn_related
    (agree : EnvRelOn rho used left right) :
    ListRel (ValueRel rho) (envRootsOn used left) (envRootsOn used right) := by
  apply lookupRoots_related
  intro key member
  apply agree key
  change key ∈ used
  exact Std.HashSet.mem_toList.mp member

theorem envRelOn_monoRenaming
    (extension : RenamingExtends smaller larger)
    (agree : EnvRelOn smaller used left right) :
    EnvRelOn larger used left right := by
  intro fvarId member
  have related := agree fvarId member
  generalize leftLookup : lookup left fvarId = leftValue at related ⊢
  generalize rightLookup : lookup right fvarId = rightValue at related ⊢
  cases related with
  | none => exact .none
  | some value => exact .some (valueRel_mono extension value)

theorem EnvRelOn.mono
    (subset : UsedSubset smaller larger)
    (agree : EnvRelOn rho larger left right) :
    EnvRelOn rho smaller left right := by
  intro fvarId member
  exact agree fvarId (subset fvarId member)

theorem EnvRelOn.bindLeft_of_absent
    (agree : EnvRelOn rho used left right)
    (absent : used.contains binder = false) :
    EnvRelOn rho used (bind left binder value) right := by
  intro fvarId member
  rw [lookup_bind_of_name_ne
    (fvarId_name_ne_of_contains_of_absent used fvarId binder member absent)]
  exact agree fvarId member

theorem EnvRelOn.bindRight_of_absent
    (agree : EnvRelOn rho used left right)
    (absent : used.contains binder = false) :
    EnvRelOn rho used left (bind right binder value) := by
  intro fvarId member
  rw [lookup_bind_of_name_ne
    (fvarId_name_ne_of_contains_of_absent used fvarId binder member absent)]
  exact agree fvarId member

/-- Binding related values under the same compiler identifier preserves all
live lookups, including a live lookup of the newly bound identifier itself. -/
theorem EnvRelOn.bindBoth
    (agree : EnvRelOn rho used left right)
    (related : ValueRel rho leftValue rightValue) :
    EnvRelOn rho used
      (bind left binder leftValue) (bind right binder rightValue) := by
  intro fvarId member
  by_cases sameName : binder.name = fvarId.name
  · have sameId : binder = fvarId := by
      cases binder with
      | mk binderName =>
          cases fvarId with
          | mk fvarName => simp_all
    subst fvarId
    simpa using OptionalRel.some related
  · rw [lookup_bind_of_name_ne sameName, lookup_bind_of_name_ne sameName]
    exact agree fvarId member

/-- Binding pointwise-related argument values to the same parameter list
preserves relational lookup agreement from arbitrary starting environments. -/
theorem EnvRelOn.bindPairsBoth
    (agree : EnvRelOn rho used sourceEnv targetEnv)
    (params : List (LCNF.Param .impure))
    (values : ListRel (ValueRel rho) sourceValues targetValues) :
    EnvRelOn rho used
      ((params.zip sourceValues).foldl
        (fun env pair => bind env pair.1.fvarId pair.2) sourceEnv)
      ((params.zip targetValues).foldl
        (fun env pair => bind env pair.1.fvarId pair.2) targetEnv) := by
  induction values generalizing params sourceEnv targetEnv with
  | nil => simpa using agree
  | cons value rest ih =>
      cases params with
      | nil => simpa using agree
      | cons param params =>
          simp only [List.zip, List.foldl_cons]
          exact ih (agree.bindBoth (binder := param.fvarId) value) params

/-- An interpreter computation either raises the same address-free runtime
fault on both sides or returns values related by its result relation. -/
inductive RuntimeResultRel (relation : α → β → Prop) :
    Except RuntimeFault α → Except RuntimeFault β → Prop where
  | error (fault : RuntimeFault) :
      RuntimeResultRel relation (.error fault) (.error fault)
  | ok (value : relation source target) :
      RuntimeResultRel relation (.ok source) (.ok target)

/-- Evaluation of one covered argument produces the same lookup fault or a
pair of address-related runtime values. -/
theorem evalArg_relOn
    (agree : EnvRelOn rho used sourceEnv targetEnv)
    (covered : ArgCovered used argument) :
    RuntimeResultRel (ValueRel rho)
      (evalArg sourceEnv argument) (evalArg targetEnv argument) := by
  cases argument with
  | erased => exact .ok .erased
  | fvar fvarId =>
      have related := agree fvarId covered
      generalize sourceLookup : lookup sourceEnv fvarId = sourceResult
        at related
      generalize targetLookup : lookup targetEnv fvarId = targetResult
        at related
      cases related with
      | none =>
          simpa [evalArg, sourceLookup, targetLookup] using
            (RuntimeResultRel.error (relation := ValueRel rho)
              (.unknownVar fvarId))
      | some value =>
          simpa [evalArg, sourceLookup, targetLookup] using
            (RuntimeResultRel.ok value)
  | type type impossible => nomatch impossible

/-- Pointwise covered argument-list evaluation short-circuits on the same
fault or returns pointwise address-related values. -/
theorem evalArgList_relOn
    (arguments : List (LCNF.Arg .impure))
    (agree : EnvRelOn rho used sourceEnv targetEnv)
    (covered : ∀ argument, argument ∈ arguments →
      ArgCovered used argument) :
    RuntimeResultRel (ListRel (ValueRel rho))
      (arguments.mapM (evalArg sourceEnv))
      (arguments.mapM (evalArg targetEnv)) := by
  induction arguments with
  | nil => exact .ok .nil
  | cons head tail ih =>
      have headResult := evalArg_relOn agree (covered head (by simp))
      have tailCovered : ∀ argument, argument ∈ tail →
          ArgCovered used argument := by
        intro argument member
        exact covered argument (by simp [member])
      have tailResult := ih tailCovered
      generalize sourceHeadEq : evalArg sourceEnv head = sourceHead
        at headResult
      generalize targetHeadEq : evalArg targetEnv head = targetHead
        at headResult
      cases headResult with
      | error fault =>
          rw [List.mapM_cons, List.mapM_cons, sourceHeadEq, targetHeadEq]
          exact .error fault
      | ok headValue =>
          generalize sourceTailEq : tail.mapM (evalArg sourceEnv) = sourceTail
            at tailResult
          generalize targetTailEq : tail.mapM (evalArg targetEnv) = targetTail
            at tailResult
          cases tailResult with
          | error fault =>
              rw [List.mapM_cons, List.mapM_cons, sourceHeadEq, targetHeadEq,
                sourceTailEq, targetTailEq]
              exact .error fault
          | ok tailValues =>
              rw [List.mapM_cons, List.mapM_cons, sourceHeadEq, targetHeadEq,
                sourceTailEq, targetTailEq]
              exact .ok (ListRel.cons headValue tailValues)

/-- Covered argument-array evaluation is relational under `EnvRelOn`. -/
theorem evalArgs_relOn
    (agree : EnvRelOn rho used sourceEnv targetEnv)
    (covered : ArgsCovered used arguments) :
    RuntimeResultRel (ArrayRel (ValueRel rho))
      (evalArgs sourceEnv arguments) (evalArgs targetEnv arguments) := by
  unfold evalArgs
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  have evaluated := evalArgList_relOn arguments.toList agree covered
  generalize sourceListEq : arguments.toList.mapM (evalArg sourceEnv) =
      sourceList at evaluated
  generalize targetListEq : arguments.toList.mapM (evalArg targetEnv) =
      targetList at evaluated
  cases evaluated with
  | error fault =>
      exact .error fault
  | ok values =>
      exact .ok (by simpa [ArrayRel] using values)

/-- A successfully evaluated covered argument is either the interpreter's
synthetic erased value or an existing live environment root. -/
theorem evalArg_value_rooted
    (covered : ArgCovered used argument)
    (evaluated : evalArg env argument = .ok value) :
    value = .erased ∨ value ∈ envRootsOn used env := by
  cases argument with
  | erased =>
      simp [evalArg] at evaluated
      subst value
      exact Or.inl rfl
  | fvar fvarId =>
      cases found : lookup env fvarId with
      | none => simp [evalArg, found] at evaluated
      | some foundValue =>
          simp [evalArg, found] at evaluated
          subst value
          exact Or.inr (lookup_mem_envRootsOn covered found)
  | type type impossible => nomatch impossible

/-- Every value returned by covered list evaluation is rooted by the old
environment, apart from `.erased`, which carries no heap address. -/
theorem evalArgList_values_subset
    (arguments : List (LCNF.Arg .impure))
    (covered : ∀ argument, argument ∈ arguments →
      ArgCovered used argument)
    (evaluated : arguments.mapM (evalArg env) = .ok values) :
    RootSubset values (.erased :: envRootsOn used env) := by
  induction arguments generalizing values with
  | nil =>
      simp [Pure.pure, Except.pure] at evaluated
      subst values
      exact fun value member => by simp at member
  | cons head tail ih =>
      rw [List.mapM_cons] at evaluated
      cases headResult : evalArg env head with
      | error fault =>
          simp [headResult, Bind.bind, Except.bind] at evaluated
      | ok headValue =>
          cases tailResult : tail.mapM (evalArg env) with
          | error fault =>
              simp [headResult, tailResult, Bind.bind, Except.bind] at evaluated
          | ok tailValues =>
              simp [headResult, tailResult, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at evaluated
              subst values
              intro value member
              simp only [List.mem_cons] at member ⊢
              rcases member with same | tailMember
              · subst value
                exact evalArg_value_rooted
                  (covered head (by simp)) headResult
              · simpa only [List.mem_cons] using
                  ih (fun argument member =>
                    covered argument (by simp [member]))
                    tailResult value tailMember

/-- Array form of `evalArgList_values_subset`. -/
theorem evalArgs_values_subset
    (covered : ArgsCovered used arguments)
    (evaluated : evalArgs env arguments = .ok values) :
    RootSubset values.toList (.erased :: envRootsOn used env) := by
  unfold evalArgs at evaluated
  rw [Array.mapM_eq_mapM_toList] at evaluated
  generalize listResultEq : arguments.toList.mapM (evalArg env) = listResult
    at evaluated
  cases listResult with
  | error fault => simp [Functor.map, Except.map] at evaluated
  | ok listValues =>
      simp [Functor.map, Except.map] at evaluated
      subst values
      simpa using
        evalArgList_values_subset arguments.toList covered listResultEq

inductive EnvResultRelOn (rho : AddressRenaming) (used : UsedLocals) :
    Except RuntimeFault Env → Except RuntimeFault Env → Prop where
  | error (fault : RuntimeFault) :
      EnvResultRelOn rho used (.error fault) (.error fault)
  | ok (env : EnvRelOn rho used source target) :
      EnvResultRelOn rho used (.ok source) (.ok target)

/-- Relational parameter binding for declaration entry.  Related argument
arrays have equal arity; successful binding yields environments related on
every liveness set requested by the entered body. -/
theorem bindParams_relOn (used : UsedLocals)
    (values : ArrayRel (ValueRel rho) sourceArguments targetArguments) :
    EnvResultRelOn rho used
      (bindParams params sourceArguments)
      (bindParams params targetArguments) := by
  have sizeEq := arrayRel_size_eq values
  unfold bindParams
  rw [← sizeEq]
  generalize arityEq : (params.size == sourceArguments.size) = arity
  cases arity with
  | false => exact .error _
  | true =>
      exact .ok ((EnvRelOn.empty rho used).bindPairsBoth
        params.toList values)

/-- Relational parameter binding over already-live environments, as used by
join-point entry. -/
theorem bindParamsOver_relOn (used : UsedLocals)
    (agree : EnvRelOn rho used sourceEnv targetEnv)
    (values : ArrayRel (ValueRel rho) sourceArguments targetArguments) :
    EnvResultRelOn rho used
      (bindParamsOver sourceEnv params sourceArguments)
      (bindParamsOver targetEnv params targetArguments) := by
  have sizeEq := arrayRel_size_eq values
  unfold bindParamsOver
  rw [← sizeEq]
  generalize arityEq : (params.size == sourceArguments.size) = arity
  cases arity with
  | false => exact .error _
  | true => exact .ok (agree.bindPairsBoth params.toList values)

/-- Runtime states agree observationally on all supplied live roots, while
allowing different unreachable heap cells and fresh-location counters. -/
structure ShadowRuntimeRel (rho : AddressRenaming)
    (left right : RuntimeState) (leftExtra rightExtra : List Value) : Prop where
  extra : ListRel (ValueRel rho) leftExtra rightExtra
  globals : ListRel (NamedValueRel rho) left.globals right.globals
  world_eq : left.world = right.world
  trace : ArrayRel (EventRel rho) left.trace right.trace
  heap : HeapRel rho left.heap right.heap
    (runtimeRoots left leftExtra) (runtimeRoots right rightExtra)
  leftMappingFresh : ∀ location, left.nextLocation ≤ location →
    rho.forward location = none
  rightMappingFresh : ∀ location, right.nextLocation ≤ location →
    rho.reverse location = none
  leftHeapFresh : ∀ location, left.nextLocation ≤ location →
    findCell? left.heap location = none
  rightHeapFresh : ∀ location, right.nextLocation ≤ location →
    findCell? right.heap location = none

/-- Updating one mapped live cell on each side preserves the complete runtime
relation when the replacement cells remain related and keep the same ownership
edges. -/
theorem ShadowRuntimeRel.setCellBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (rightFound : findCell? right.heap rightLocation = some rightCell)
    (leftOwned :
      leftReplacement.object.ownedValues = leftCell.object.ownedValues)
    (rightOwned :
      rightReplacement.object.ownedValues = rightCell.object.ownedValues)
    (replacement :
      HeapCellRel rho leftReplacement rightReplacement) :
    ∃ leftResult rightResult,
      setCell left leftLocation leftReplacement = .ok leftResult ∧
      setCell right rightLocation rightReplacement = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases setCell_spec_of_find left leftLocation leftCell leftReplacement
      leftFound with
    ⟨leftResult, leftEffect, leftTarget, leftFrame, _leftLength,
      leftNext, leftGlobals, leftWorld, leftTrace⟩
  rcases setCell_spec_of_find right rightLocation rightCell rightReplacement
      rightFound with
    ⟨rightResult, rightEffect, rightTarget, rightFrame, _rightLength,
      rightNext, rightGlobals, rightWorld, rightTrace⟩
  refine ⟨leftResult, rightResult, leftEffect, rightEffect, ?_⟩
  have leftLocationLt : leftLocation < left.nextLocation := by
    apply Nat.lt_of_not_ge
    intro bounded
    have fresh := related.leftHeapFresh leftLocation bounded
    rw [leftFound] at fresh
    contradiction
  have rightLocationLt : rightLocation < right.nextLocation := by
    apply Nat.lt_of_not_ge
    intro bounded
    have fresh := related.rightHeapFresh rightLocation bounded
    rw [rightFound] at fresh
    contradiction
  exact {
    extra := related.extra
    globals := by
      rw [leftGlobals, rightGlobals]
      exact related.globals
    world_eq := leftWorld.trans (related.world_eq.trans rightWorld.symm)
    trace := by
      rw [leftTrace, rightTrace]
      exact related.trace
    heap := by
      have heaps := heapRel_replaceBoth related.heap mapping
        leftFound rightFound leftTarget rightTarget leftFrame rightFrame
        leftOwned rightOwned replacement
      simpa [runtimeRoots, leftGlobals, rightGlobals, leftTrace, rightTrace]
        using heaps
    leftMappingFresh := by
      intro location bounded
      exact related.leftMappingFresh location (leftNext ▸ bounded)
    rightMappingFresh := by
      intro location bounded
      exact related.rightMappingFresh location (rightNext ▸ bounded)
    leftHeapFresh := by
      intro location bounded
      have oldBounded : left.nextLocation ≤ location := leftNext ▸ bounded
      have different : location ≠ leftLocation :=
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le leftLocationLt oldBounded)).symm
      rw [leftFrame location different]
      exact related.leftHeapFresh location oldBounded
    rightHeapFresh := by
      intro location bounded
      have oldBounded : right.nextLocation ≤ location := rightNext ▸ bounded
      have different : location ≠ rightLocation :=
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le rightLocationLt oldBounded)).symm
      rw [rightFrame location different]
      exact related.rightHeapFresh location oldBounded
  }

/-- Updating a mapped live pair may replace ownership edges when every newly
owned heap reference was already reachable from the published runtime roots.
This is the generic heap operation needed by retained object-field writes. -/
theorem ShadowRuntimeRel.setCellBothRooted
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (rightFound : findCell? right.heap rightLocation = some rightCell)
    (leftOwned : ∀ {child},
      Value.object (.heap child) ∈
          leftReplacement.object.ownedValues.toList →
        Value.object (.heap child) ∈
            leftCell.object.ownedValues.toList ∨
          Reachable left.heap (runtimeRoots left leftExtra) child)
    (rightOwned : ∀ {child},
      Value.object (.heap child) ∈
          rightReplacement.object.ownedValues.toList →
        Value.object (.heap child) ∈
            rightCell.object.ownedValues.toList ∨
          Reachable right.heap (runtimeRoots right rightExtra) child)
    (replacement :
      HeapCellRel rho leftReplacement rightReplacement) :
    ∃ leftResult rightResult,
      setCell left leftLocation leftReplacement = .ok leftResult ∧
      setCell right rightLocation rightReplacement = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases setCell_spec_of_find left leftLocation leftCell leftReplacement
      leftFound with
    ⟨leftResult, leftEffect, leftTarget, leftFrame, _leftLength,
      leftNext, leftGlobals, leftWorld, leftTrace⟩
  rcases setCell_spec_of_find right rightLocation rightCell rightReplacement
      rightFound with
    ⟨rightResult, rightEffect, rightTarget, rightFrame, _rightLength,
      rightNext, rightGlobals, rightWorld, rightTrace⟩
  refine ⟨leftResult, rightResult, leftEffect, rightEffect, ?_⟩
  have leftLocationLt : leftLocation < left.nextLocation := by
    apply Nat.lt_of_not_ge
    intro bounded
    have fresh := related.leftHeapFresh leftLocation bounded
    rw [leftFound] at fresh
    contradiction
  have rightLocationLt : rightLocation < right.nextLocation := by
    apply Nat.lt_of_not_ge
    intro bounded
    have fresh := related.rightHeapFresh rightLocation bounded
    rw [rightFound] at fresh
    contradiction
  exact {
    extra := related.extra
    globals := by
      rw [leftGlobals, rightGlobals]
      exact related.globals
    world_eq := leftWorld.trans (related.world_eq.trans rightWorld.symm)
    trace := by
      rw [leftTrace, rightTrace]
      exact related.trace
    heap := by
      have heaps := heapRel_replaceBothRooted related.heap mapping
        leftFound rightFound leftTarget rightTarget leftFrame rightFrame
        leftOwned rightOwned replacement
      simpa [runtimeRoots, leftGlobals, rightGlobals, leftTrace, rightTrace]
        using heaps
    leftMappingFresh := by
      intro location bounded
      exact related.leftMappingFresh location (leftNext ▸ bounded)
    rightMappingFresh := by
      intro location bounded
      exact related.rightMappingFresh location (rightNext ▸ bounded)
    leftHeapFresh := by
      intro location bounded
      have oldBounded : left.nextLocation ≤ location := leftNext ▸ bounded
      have different : location ≠ leftLocation :=
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le leftLocationLt oldBounded)).symm
      rw [leftFrame location different]
      exact related.leftHeapFresh location oldBounded
    rightHeapFresh := by
      intro location bounded
      have oldBounded : right.nextLocation ≤ location := rightNext ▸ bounded
      have different : location ≠ rightLocation :=
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le rightLocationLt oldBounded)).symm
      rw [rightFrame location different]
      exact related.rightHeapFresh location oldBounded
  }

theorem ShadowRuntimeRel.roots
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra) :
    ListRel (ValueRel rho)
      (runtimeRoots left leftExtra) (runtimeRoots right rightExtra) := by
  unfold runtimeRoots
  exact listRel_append
    (listRel_append related.extra (globalsRoots_related related.globals))
    (traceRoots_related related.trace)

/-- Forgetting live roots is sound when the replacement roots remain
pointwise related and are subsets of the previously published extras. -/
theorem ShadowRuntimeRel.restrictExtra
    (related : ShadowRuntimeRel rho left right leftLarger rightLarger)
    (extra : ListRel (ValueRel rho) leftSmaller rightSmaller)
    (leftSubset : RootSubset leftSmaller leftLarger)
    (rightSubset : RootSubset rightSmaller rightLarger) :
    ShadowRuntimeRel rho left right leftSmaller rightSmaller := by
  exact {
    extra
    globals := related.globals
    world_eq := related.world_eq
    trace := related.trace
    heap := heapRel_monoRoots related.heap
      (runtimeRoots_monoExtra leftSubset)
      (runtimeRoots_monoExtra rightSubset)
    leftMappingFresh := related.leftMappingFresh
    rightMappingFresh := related.rightMappingFresh
    leftHeapFresh := related.leftHeapFresh
    rightHeapFresh := related.rightHeapFresh
  }

/-- Replace the explicit roots using semantic reachability inclusions.  This
is strictly more general than `restrictExtra` and is needed when captured
closure fields become call arguments: they are reachable through the closure
cell even though they were not direct machine roots. -/
theorem ShadowRuntimeRel.reindexExtra
    (related : ShadowRuntimeRel rho left right leftOld rightOld)
    (extra : ListRel (ValueRel rho) leftNew rightNew)
    (leftReachable : ∀ location,
      Reachable left.heap (runtimeRoots left leftNew) location →
        Reachable left.heap (runtimeRoots left leftOld) location)
    (rightReachable : ∀ location,
      Reachable right.heap (runtimeRoots right rightNew) location →
        Reachable right.heap (runtimeRoots right rightOld) location) :
    ShadowRuntimeRel rho left right leftNew rightNew := by
  exact {
    extra
    globals := related.globals
    world_eq := related.world_eq
    trace := related.trace
    heap := ⟨
      fun location reachable => related.heap.1 location
        (leftReachable location reachable),
      fun location reachable => related.heap.2 location
        (rightReachable location reachable)⟩
    leftMappingFresh := related.leftMappingFresh
    rightMappingFresh := related.rightMappingFresh
    leftHeapFresh := related.leftHeapFresh
    rightHeapFresh := related.rightHeapFresh
  }

/-- Adding `.erased` to a root set does not make any heap location
reachable. -/
theorem reachable_without_erased_root
    (reachable : Reachable heap (.erased :: roots) location) :
    Reachable heap roots location := by
  induction reachable with
  | root member =>
      simp only [List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · exact .root member
  | child parent found owned reference ih =>
      exact .child ih found owned reference

/-- The runtime relation may publish `.erased` as an additional direct root:
it is related to itself and carries no heap address. -/
theorem ShadowRuntimeRel.prependErased
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra) :
    ShadowRuntimeRel rho left right
      (.erased :: leftExtra) (.erased :: rightExtra) := by
  apply related.reindexExtra (.cons .erased related.extra)
  · intro location reachable
    apply reachable_without_erased_root
    simpa [runtimeRoots] using reachable
  · intro location reachable
    apply reachable_without_erased_root
    simpa [runtimeRoots] using reachable

theorem closureCallRoots_reachable
    (found : findCell? runtime.heap closureLocation = some cell)
    (objectEq : cell.object = .closure name arity fixed) :
    ∀ location,
      Value.object (.heap location) ∈
        runtimeRoots runtime ((fixed ++ arguments).toList ++ frameRoots) →
      Reachable runtime.heap
        (runtimeRoots runtime
          ((.object (.heap closureLocation) :: arguments.toList) ++
            frameRoots))
        location := by
  intro location member
  simp only [runtimeRoots, Array.toList_append, List.mem_append] at member
  rcases member with
    (((fixedRoot | argumentRoot) | frameRoot) | globalRoot) | traceRoot
  · have closureReachable : Reachable runtime.heap
        (runtimeRoots runtime
          ((.object (.heap closureLocation) :: arguments.toList) ++
            frameRoots))
        closureLocation := by
      apply Reachable.root
      simp [runtimeRoots]
    exact .child closureReachable found
      (by simpa [objectEq, HeapObject.ownedValues] using fixedRoot) rfl
  · exact .root (by simp [runtimeRoots, argumentRoot])
  · exact .root (by simp [runtimeRoots, frameRoot])
  · exact .root (by simp [runtimeRoots, globalRoot])
  · exact .root (by simp [runtimeRoots, traceRoot])

/-- Reindex an invocation from a closure reference plus fresh arguments to
the concatenated fixed/fresh argument array expected by `invokeDecl`.  Fixed
arguments are justified as children of the reachable closure cell. -/
theorem ShadowRuntimeRel.reindexClosureCall
    (related : ShadowRuntimeRel rho left right
      ((.object (.heap leftLocation) :: leftArguments.toList) ++
        leftFrameRoots)
      ((.object (.heap rightLocation) :: rightArguments.toList) ++
        rightFrameRoots))
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (rightFound : findCell? right.heap rightLocation = some rightCell)
    (leftObject : leftCell.object =
      .closure name arity leftFixed)
    (rightObject : rightCell.object =
      .closure name arity rightFixed)
    (fixed : ArrayRel (ValueRel rho) leftFixed rightFixed)
    (arguments : ArrayRel (ValueRel rho) leftArguments rightArguments)
    (frames : ListRel (ValueRel rho) leftFrameRoots rightFrameRoots) :
    ShadowRuntimeRel rho left right
      ((leftFixed ++ leftArguments).toList ++ leftFrameRoots)
      ((rightFixed ++ rightArguments).toList ++ rightFrameRoots) := by
  apply related.reindexExtra
    (listRel_append (arrayRel_append fixed arguments) frames)
  · intro location reachable
    exact reachable_monoRootReachability
      (closureCallRoots_reachable leftFound leftObject) reachable
  · intro location reachable
    exact reachable_monoRootReachability
      (closureCallRoots_reachable rightFound rightObject) reachable

/-- Reading a mapped heap reference that is published as a control root
returns related cells at the mapped locations. -/
theorem ShadowRuntimeRel.readMappedCell
    (related : ShadowRuntimeRel rho left right
      ((.object (.heap leftLocation) :: leftTail) ++ leftFrameRoots)
      ((.object (.heap rightLocation) :: rightTail) ++ rightFrameRoots))
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell) :
    ∃ rightCell,
      findCell? right.heap rightLocation = some rightCell ∧
      HeapCellRel rho leftCell rightCell := by
  have leftReachable : Reachable left.heap
      (runtimeRoots left
        ((.object (.heap leftLocation) :: leftTail) ++ leftFrameRoots))
      leftLocation := by
    apply Reachable.root
    apply extra_subset_runtimeRoots
    exact List.mem_append_left _ List.mem_cons_self
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have locationEq : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have cellEq : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  exact ⟨rightCell, rightFound, cells⟩

/-- Reading a reachable source closure through a mapped reference determines
the corresponding live target closure and reindexes both runtimes to the
concatenated argument arrays consumed by `invokeDecl`. -/
theorem ShadowRuntimeRel.readMappedClosure
    (related : ShadowRuntimeRel rho left right
      ((.object (.heap leftLocation) :: leftArguments.toList) ++
        leftFrameRoots)
      ((.object (.heap rightLocation) :: rightArguments.toList) ++
        rightFrameRoots))
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (leftLive : leftCell.live = true)
    (leftObject : leftCell.object = .closure name arity leftFixed)
    (arguments : ArrayRel (ValueRel rho) leftArguments rightArguments)
    (frames : ListRel (ValueRel rho) leftFrameRoots rightFrameRoots) :
    ∃ rightCell rightFixed,
      findCell? right.heap rightLocation = some rightCell ∧
      rightCell.live = true ∧
      rightCell.object = .closure name arity rightFixed ∧
      ArrayRel (ValueRel rho) leftFixed rightFixed ∧
      ShadowRuntimeRel rho left right
        ((leftFixed ++ leftArguments).toList ++ leftFrameRoots)
        ((rightFixed ++ rightArguments).toList ++ rightFrameRoots) := by
  have leftReachable : Reachable left.heap
      (runtimeRoots left
        ((.object (.heap leftLocation) :: leftArguments.toList) ++
          leftFrameRoots))
      leftLocation := by
    apply Reachable.root
    apply extra_subset_runtimeRoots
    exact List.mem_append_left _ List.mem_cons_self
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have locationEq : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have cellEq : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  have rightLive : rightCell.live = true := by
    rw [← cells.2.2.1]
    exact leftLive
  have objects := cells.2.2.2
  generalize rightObject : rightCell.object = targetObject at objects
  rw [leftObject] at objects
  cases objects with
  | closure fixed =>
      rename_i rightFixed
      have reindexed := related.reindexClosureCall leftFound rightFound
        leftObject rightObject fixed arguments frames
      exact ⟨rightCell, rightFixed, rightFound, rightLive, rightObject, fixed,
        reindexed⟩

/-- A cache hit may publish a global as a new control root.  The value was
already among the canonical runtime roots, so this changes only the explicit
root presentation. -/
theorem ShadowRuntimeRel.prependGlobal
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (value : ValueRel rho leftValue rightValue)
    (leftFound : findGlobal? left.globals name = some leftValue)
    (rightFound : findGlobal? right.globals name = some rightValue) :
    ShadowRuntimeRel rho left right
      (leftValue :: leftExtra) (rightValue :: rightExtra) := by
  have leftMember := findGlobal?_value_mem leftFound
  have rightMember := findGlobal?_value_mem rightFound
  exact {
    extra := .cons value related.extra
    globals := related.globals
    world_eq := related.world_eq
    trace := related.trace
    heap := heapRel_monoRoots related.heap
      (by
        intro root member
        simp only [runtimeRoots, List.mem_append, List.mem_cons] at member ⊢
        rcases member with (headOrExtra | global) | traced
        · rcases headOrExtra with same | extra
          · subst root
            exact Or.inl (Or.inr leftMember)
          · exact Or.inl (Or.inl extra)
        · exact Or.inl (Or.inr global)
        · exact Or.inr traced)
      (by
        intro root member
        simp only [runtimeRoots, List.mem_append, List.mem_cons] at member ⊢
        rcases member with (headOrExtra | global) | traced
        · rcases headOrExtra with same | extra
          · subst root
            exact Or.inl (Or.inr rightMember)
          · exact Or.inl (Or.inl extra)
        · exact Or.inl (Or.inr global)
        · exact Or.inr traced)
    leftMappingFresh := related.leftMappingFresh
    rightMappingFresh := related.rightMappingFresh
    leftHeapFresh := related.leftHeapFresh
    rightHeapFresh := related.rightHeapFresh
  }

/-- Observable frame condition for a possibly multi-cell runtime update.
The operation may rewrite unreachable garbage, but every cell reachable from
the published pre-state roots and every non-heap observable is fixed. -/
structure RuntimeReachableFrame (before after : RuntimeState)
    (roots : List Value) : Prop where
  nextLocation_eq : after.nextLocation = before.nextLocation
  globals_eq : after.globals = before.globals
  world_eq : after.world = before.world
  trace_eq : after.trace = before.trace
  heap : HeapReachableFrame before.heap after.heap roots
  heapFresh : ∀ location, after.nextLocation ≤ location →
    findCell? after.heap location = none

/-- Any source runtime transition satisfying the reachable-frame contract
preserves the complete live-runtime relation. -/
theorem ShadowRuntimeRel.frameLeft
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (frame : RuntimeReachableFrame left after
      (runtimeRoots left leftExtra)) :
    ShadowRuntimeRel rho after right leftExtra rightExtra := by
  exact {
    extra := related.extra
    globals := by
      rw [frame.globals_eq]
      exact related.globals
    world_eq := frame.world_eq.trans related.world_eq
    trace := by
      rw [frame.trace_eq]
      exact related.trace
    heap := by
      have preserved := heapRel_frameLeft_of_reachableFrame related.roots
        related.heap frame.heap
      simpa [runtimeRoots, frame.globals_eq, frame.trace_eq] using preserved
    leftMappingFresh := by
      intro location bounded
      exact related.leftMappingFresh location
        (frame.nextLocation_eq ▸ bounded)
    rightMappingFresh := related.rightMappingFresh
    leftHeapFresh := frame.heapFresh
    rightHeapFresh := related.rightHeapFresh
  }

/-- Replacing one unreachable existing cell produces a reachable runtime
frame.  This packages the common postcondition needed by reset/reuse-style
ownership operations. -/
theorem setCell_reachableFrame_of_unreachable
    (found : findCell? before.heap modified = some current)
    (unreachable : ¬Reachable before.heap roots modified)
    (fresh : ∀ location, before.nextLocation ≤ location →
      findCell? before.heap location = none)
    (replacement : HeapCell) :
    ∃ after,
      setCell before modified replacement = .ok after ∧
      RuntimeReachableFrame before after roots := by
  rcases setCell_spec_of_find before modified current replacement found with
    ⟨after, effect, target, lookupFrame, length, nextLocation,
      globals, world, trace⟩
  have modifiedLt : modified < before.nextLocation := by
    apply Nat.lt_of_not_ge
    intro bounded
    have absent := fresh modified bounded
    rw [found] at absent
    contradiction
  refine ⟨after, effect, ?_⟩
  exact {
    nextLocation_eq := nextLocation
    globals_eq := globals
    world_eq := world
    trace_eq := trace
    heap := by
      intro location reachable
      have different : location ≠ modified := by
        intro same
        subst location
        exact unreachable reachable
      exact lookupFrame location different
    heapFresh := by
      intro location bounded
      have oldBounded : before.nextLocation ≤ location :=
        nextLocation ▸ bounded
      have different : location ≠ modified :=
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le modifiedLt oldBounded)).symm
      rw [lookupFrame location different]
      exact fresh location oldBounded
  }

theorem ShadowRuntimeRel.leftUnreachable_of_forward_unmapped
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (unmapped : rho.forward location = none) :
    ¬Reachable left.heap (runtimeRoots left leftExtra) location := by
  intro reachable
  rcases related.heap.1 location reachable with
    ⟨mapped, leftCell, rightCell, mapping, leftFound, rightFound, cells⟩
  rw [unmapped] at mapping
  contradiction

theorem ShadowRuntimeRel.rightUnreachable_of_reverse_unmapped
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (unmapped : rho.reverse location = none) :
    ¬Reachable right.heap (runtimeRoots right rightExtra) location := by
  intro reachable
  rcases related.heap.2 location reachable with
    ⟨mapped, rightCell, leftCell, mapping, rightFound, leftFound, cells⟩
  rw [unmapped] at mapping
  contradiction

/-- Replacing an unreachable source cell preserves the complete runtime
relation.  The semantic heap update also preserves the fresh counter and all
non-heap runtime components. -/
theorem ShadowRuntimeRel.setCellLeftUnreachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (found : findCell? left.heap location = some current)
    (unreachable : ¬Reachable
      left.heap (runtimeRoots left leftExtra) location)
    (replacement : HeapCell) :
    ∃ result,
      setCell left location replacement = .ok result ∧
      ShadowRuntimeRel rho result right leftExtra rightExtra := by
  rcases setCell_spec_of_find left location current replacement found with
    ⟨result, effect, target, frame, length, nextLocation,
      globals, world, trace⟩
  have locationLt : location < left.nextLocation := by
    apply Nat.lt_of_not_ge
    intro bounded
    have fresh := related.leftHeapFresh location bounded
    rw [found] at fresh
    contradiction
  refine ⟨result, effect, ?_⟩
  exact {
    extra := related.extra
    globals := by
      rw [globals]
      exact related.globals
    world_eq := world.trans related.world_eq
    trace := by
      rw [trace]
      exact related.trace
    heap := by
      have framed : HeapRel rho result.heap right.heap
          (runtimeRoots left leftExtra) (runtimeRoots right rightExtra) :=
        heapRel_frameLeft_of_unreachable related.roots related.heap frame
          unreachable
      simpa [runtimeRoots, globals, trace] using framed
    leftMappingFresh := by
      intro candidate bounded
      exact related.leftMappingFresh candidate (nextLocation ▸ bounded)
    rightMappingFresh := related.rightMappingFresh
    leftHeapFresh := by
      intro candidate bounded
      have oldBounded : left.nextLocation ≤ candidate :=
        nextLocation ▸ bounded
      have different : candidate ≠ location :=
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le locationLt oldBounded)).symm
      rw [frame candidate different]
      exact related.leftHeapFresh candidate oldBounded
    rightHeapFresh := related.rightHeapFresh
  }

/-- A well-formed object-field write to an unreachable source constructor is
an observationally silent source-only heap update. -/
theorem ShadowRuntimeRel.setObjectFieldLeftUnreachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (found : findCell? left.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor object)
    (bounded : index < object.objectFields.size)
    (unreachable : ¬Reachable
      left.heap (runtimeRoots left leftExtra) location)
    (field : Value) :
    ∃ result,
      setObjectField left (.object (.heap location)) index field = .ok result ∧
      ShadowRuntimeRel rho result right leftExtra rightExtra := by
  let replacement : HeapCell :=
    { cell with object := .ctor {
        object with objectFields := object.objectFields.set index field } }
  rcases related.setCellLeftUnreachable found unreachable replacement with
    ⟨result, effect, next⟩
  refine ⟨result, ?_, next⟩
  have constructor : getConstructor left (.object (.heap location)) =
      .ok (location, cell, object) := by
    simp [getConstructor, getLiveCell, found, live, objectEq,
      Bind.bind, Except.bind]
    rfl
  unfold setObjectField modifyConstructor
  rw [constructor]
  simp only [Bind.bind, Except.bind]
  rw [dif_pos bounded]
  simpa [replacement] using effect

/-- The corresponding unboxed-word write changes only an unreachable cell. -/
theorem ShadowRuntimeRel.setUSizeFieldLeftUnreachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (found : findCell? left.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor object)
    (bounded : index < object.usizeFields.size)
    (unreachable : ¬Reachable
      left.heap (runtimeRoots left leftExtra) location)
    (field : UInt64) :
    ∃ result,
      setUSizeField left (.object (.heap location)) index (.usize field) =
        .ok result ∧
      ShadowRuntimeRel rho result right leftExtra rightExtra := by
  let replacement : HeapCell :=
    { cell with object := .ctor {
        object with usizeFields := object.usizeFields.set index field } }
  rcases related.setCellLeftUnreachable found unreachable replacement with
    ⟨result, effect, next⟩
  refine ⟨result, ?_, next⟩
  have constructor : getConstructor left (.object (.heap location)) =
      .ok (location, cell, object) := by
    simp [getConstructor, getLiveCell, found, live, objectEq,
      Bind.bind, Except.bind]
    rfl
  unfold setUSizeField modifyConstructor
  rw [constructor]
  simp only [Bind.bind, Except.bind]
  rw [dif_pos bounded]
  simpa [replacement] using effect

/-- A successful live-cell lookup exposes the exact semantic heap cell and
its liveness bit. -/
theorem getLiveCell_spec
    (effect : getLiveCell runtime location = .ok cell) :
    findCell? runtime.heap location = some cell ∧ cell.live = true := by
  unfold getLiveCell at effect
  generalize foundEq : findCell? runtime.heap location = found at effect
  cases found with
  | none => simp at effect
  | some foundCell =>
      cases liveEq : foundCell.live with
      | false => simp [liveEq] at effect
      | true =>
          simp [liveEq] at effect
          subst cell
          exact ⟨rfl, liveEq⟩

/-- A successful constructor lookup through a heap reference exposes the
exact live semantic cell used by the mutation operations below. -/
theorem getConstructor_heap_spec
    (effect : getConstructor runtime (.object (.heap location)) =
      .ok (resultLocation, cell, object)) :
    resultLocation = location ∧
      findCell? runtime.heap location = some cell ∧
      cell.live = true ∧
      cell.object = .ctor object := by
  unfold getConstructor at effect
  simp only [Bind.bind, Except.bind] at effect
  generalize foundEq : findCell? runtime.heap location = found at effect
  cases found with
  | none => simp [getLiveCell, foundEq] at effect
  | some foundCell =>
      cases liveEq : foundCell.live with
      | false => simp [getLiveCell, foundEq, liveEq] at effect
      | true =>
          cases objectEq : foundCell.object <;>
            simp [getLiveCell, foundEq, liveEq, objectEq] at effect
          case ctor =>
            cases effect
            exact ⟨rfl, rfl, liveEq, objectEq⟩

/-- A retained object-field write updates one mapped constructor pair.  Any
inserted heap reference must already be reachable from the live roots, so the
write may discard an old edge but cannot expose a hidden heap component. -/
theorem ShadowRuntimeRel.setObjectFieldBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (leftLive : leftCell.live = true)
    (leftObjectEq : leftCell.object = .ctor leftObject)
    (bounded : index < leftObject.objectFields.size)
    (leftFieldRoot : ∀ {location},
      leftField = .object (.heap location) →
        Reachable left.heap (runtimeRoots left leftExtra) location)
    (rightFieldRoot : ∀ {location},
      rightField = .object (.heap location) →
        Reachable right.heap (runtimeRoots right rightExtra) location)
    (fields : ValueRel rho leftField rightField) :
    ∃ leftResult rightResult,
      setObjectField left (.object (.heap leftLocation)) index leftField =
        .ok leftResult ∧
      setObjectField right (.object (.heap rightLocation)) index rightField =
        .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have mappedSame : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have leftCellSame : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  have rightLive : rightCell.live = true := by
    rw [← cells.2.2.1]
    exact leftLive
  have objects := cells.2.2.2
  generalize rightObjectEq : rightCell.object = targetObject at objects
  rw [leftObjectEq] at objects
  cases objects with
  | ctor tag objectFields usizes scalars =>
      rename_i rightObject
      have objectSize :
          leftObject.objectFields.size = rightObject.objectFields.size :=
        arrayRel_size_eq objectFields
      have rightBounded : index < rightObject.objectFields.size := by
        omega
      let leftReplacement : HeapCell :=
        { leftCell with object := .ctor {
            leftObject with
            objectFields := leftObject.objectFields.set index leftField } }
      let rightReplacement : HeapCell :=
        { rightCell with object := .ctor {
            rightObject with
            objectFields := rightObject.objectFields.set index rightField } }
      have replacement :
          HeapCellRel rho leftReplacement rightReplacement := by
        refine ⟨cells.1, cells.2.1, cells.2.2.1, ?_⟩
        dsimp only [leftReplacement, rightReplacement]
        exact @HeapObjectRel.ctor rho
          { leftObject with
            objectFields := leftObject.objectFields.set index leftField }
          { rightObject with
            objectFields := rightObject.objectFields.set index rightField }
          tag
          (arrayRel_set index objectFields fields bounded rightBounded)
          usizes scalars
      have leftOwned : ∀ {child},
          Value.object (.heap child) ∈
              leftReplacement.object.ownedValues.toList →
            Value.object (.heap child) ∈
                leftCell.object.ownedValues.toList ∨
              Reachable left.heap (runtimeRoots left leftExtra) child := by
        intro child member
        have changedMemberList :
            Value.object (.heap child) ∈
              (leftObject.objectFields.set index leftField).toList := by
          simpa [leftReplacement, HeapObject.ownedValues] using member
        have changedMember :
            Value.object (.heap child) ∈
              leftObject.objectFields.set index leftField :=
          Array.mem_toList_iff.mp changedMemberList
        rcases Array.mem_or_eq_of_mem_set changedMember with
          oldMember | changed
        · exact Or.inl (by
            simpa [leftObjectEq, HeapObject.ownedValues] using oldMember)
        · exact Or.inr (leftFieldRoot changed.symm)
      have rightOwned : ∀ {child},
          Value.object (.heap child) ∈
              rightReplacement.object.ownedValues.toList →
            Value.object (.heap child) ∈
                rightCell.object.ownedValues.toList ∨
              Reachable right.heap (runtimeRoots right rightExtra) child := by
        intro child member
        have changedMemberList :
            Value.object (.heap child) ∈
              (rightObject.objectFields.set index rightField).toList := by
          simpa [rightReplacement, HeapObject.ownedValues] using member
        have changedMember :
            Value.object (.heap child) ∈
              rightObject.objectFields.set index rightField :=
          Array.mem_toList_iff.mp changedMemberList
        rcases Array.mem_or_eq_of_mem_set changedMember with
          oldMember | changed
        · exact Or.inl (by
            simpa [rightObjectEq, HeapObject.ownedValues] using oldMember)
        · exact Or.inr (rightFieldRoot changed.symm)
      rcases related.setCellBothRooted mapping leftFound rightFound
          leftOwned rightOwned replacement with
        ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
      refine ⟨leftResult, rightResult, ?_, ?_, next⟩
      · have constructor :
            getConstructor left (.object (.heap leftLocation)) =
              .ok (leftLocation, leftCell, leftObject) := by
          simp [getConstructor, getLiveCell, leftFound, leftLive,
            leftObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setObjectField modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos bounded]
        simpa [leftReplacement] using leftEffect
      · have constructor :
            getConstructor right (.object (.heap rightLocation)) =
              .ok (rightLocation, rightCell, rightObject) := by
          simp [getConstructor, getLiveCell, rightFound, rightLive,
            rightObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setObjectField modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos rightBounded]
        simpa [rightReplacement] using rightEffect

/-- Interpreter-facing retained object write: related live operands, rooted
inserted values, and one successful source mutation determine a successful
related target mutation. -/
theorem ShadowRuntimeRel.setObjectFieldBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (fields : ValueRel rho leftField rightField)
    (leftFieldRoot : ∀ {location},
      leftField = .object (.heap location) →
        Reachable left.heap (runtimeRoots left leftExtra) location)
    (rightFieldRoot : ∀ {location},
      rightField = .object (.heap location) →
        Reachable right.heap (runtimeRoots right rightExtra) location)
    (sourceEffect :
      setObjectField left leftObject index leftField = .ok leftResult) :
    ∃ rightResult,
      setObjectField right rightObject index rightField = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases objects with
  | tagged payload =>
      simp [setObjectField, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | usize value =>
      simp [setObjectField, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | scalar value =>
      simp [setObjectField, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | erased =>
      simp [setObjectField, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | reuseNone =>
      simp [setObjectField, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | reuseSome mapping =>
      simp [setObjectField, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | heap mapping =>
      rename_i leftLocation rightLocation
      have originalSourceEffect := sourceEffect
      unfold setObjectField modifyConstructor at sourceEffect
      simp only [Bind.bind, Except.bind] at sourceEffect
      generalize constructorEq :
        getConstructor left (.object (.heap leftLocation)) =
          constructorResult at sourceEffect
      cases constructorResult with
      | error fault =>
          simp at sourceEffect
      | ok result =>
          obtain ⟨resultLocation, leftCell, leftConstructor⟩ := result
          simp only at sourceEffect
          by_cases bounded : index < leftConstructor.objectFields.size
          · rw [dif_pos bounded] at sourceEffect
            simp only at sourceEffect
            rcases getConstructor_heap_spec constructorEq with
              ⟨resultLocationEq, leftFound, leftLive, leftObjectEq⟩
            subst resultLocation
            have reachable :
                Reachable left.heap (runtimeRoots left leftExtra)
                  leftLocation := by
              exact .root (extra_subset_runtimeRoots left leftExtra
                (.object (.heap leftLocation)) objectRoot)
            rcases related.setObjectFieldBoth mapping reachable leftFound
                leftLive leftObjectEq bounded leftFieldRoot rightFieldRoot
                fields with
              ⟨computedLeft, rightResult, leftEffect, rightEffect, next⟩
            rw [originalSourceEffect] at leftEffect
            cases leftEffect
            exact ⟨rightResult, rightEffect, next⟩
          · rw [dif_neg bounded] at sourceEffect
            simp at sourceEffect

/-- A successful absolute-slot write to one reachable mapped constructor is
matched by the same write to the related constructor. The slot is interpreted
against the complete fixed-slot layout on both sides. -/
theorem ShadowRuntimeRel.setUSizeSlotBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (leftLive : leftCell.live = true)
    (leftObjectEq : leftCell.object = .ctor leftObject)
    (lower : leftObject.objectFields.size ≤ slot)
    (bounded :
      slot - leftObject.objectFields.size < leftObject.usizeFields.size)
    (field : UInt64) :
    ∃ leftResult rightResult,
      setUSizeSlot left (.object (.heap leftLocation)) slot (.usize field) =
        .ok leftResult ∧
      setUSizeSlot right (.object (.heap rightLocation)) slot (.usize field) =
        .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have mappedSame : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have leftCellSame : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  have rightLive : rightCell.live = true := by
    rw [← cells.2.2.1]
    exact leftLive
  have objects := cells.2.2.2
  generalize rightObjectEq : rightCell.object = targetObject at objects
  rw [leftObjectEq] at objects
  cases objects with
  | ctor tag objectFields usizes scalars =>
      rename_i rightObject
      have objectSize :
          leftObject.objectFields.size = rightObject.objectFields.size :=
        arrayRel_size_eq objectFields
      have usizeSize :
          leftObject.usizeFields.size = rightObject.usizeFields.size :=
        congrArg Array.size usizes
      have rightLower : rightObject.objectFields.size ≤ slot := by
        omega
      have rightBounded :
          slot - rightObject.objectFields.size <
            rightObject.usizeFields.size := by
        omega
      let leftIndex := slot - leftObject.objectFields.size
      let rightIndex := slot - rightObject.objectFields.size
      let leftReplacement : HeapCell :=
        { leftCell with object := .ctor {
            leftObject with
            usizeFields := leftObject.usizeFields.set leftIndex field } }
      let rightReplacement : HeapCell :=
        { rightCell with object := .ctor {
            rightObject with
            usizeFields := rightObject.usizeFields.set rightIndex field } }
      have replacement :
          HeapCellRel rho leftReplacement rightReplacement := by
        refine ⟨cells.1, cells.2.1, cells.2.2.1, ?_⟩
        dsimp only [leftReplacement, rightReplacement]
        refine @HeapObjectRel.ctor rho
          { leftObject with
            usizeFields := leftObject.usizeFields.set leftIndex field }
          { rightObject with
            usizeFields := rightObject.usizeFields.set rightIndex field }
          tag objectFields ?_ scalars
        simp [leftIndex, rightIndex, objectSize, usizes]
      have leftOwned :
          leftReplacement.object.ownedValues =
            leftCell.object.ownedValues := by
        simp [leftReplacement, leftObjectEq, HeapObject.ownedValues]
      have rightOwned :
          rightReplacement.object.ownedValues =
            rightCell.object.ownedValues := by
        simp [rightReplacement, rightObjectEq, HeapObject.ownedValues]
      rcases related.setCellBoth mapping leftFound rightFound
          leftOwned rightOwned replacement with
        ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
      refine ⟨leftResult, rightResult, ?_, ?_, next⟩
      · have constructor :
            getConstructor left (.object (.heap leftLocation)) =
              .ok (leftLocation, leftCell, leftObject) := by
          simp [getConstructor, getLiveCell, leftFound, leftLive,
            leftObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setUSizeSlot modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        rw [if_pos lower, dif_pos bounded]
        simpa [leftIndex, leftReplacement] using leftEffect
      · have constructor :
            getConstructor right (.object (.heap rightLocation)) =
              .ok (rightLocation, rightCell, rightObject) := by
          simp [getConstructor, getLiveCell, rightFound, rightLive,
            rightObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setUSizeSlot modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        rw [if_pos rightLower, dif_pos rightBounded]
        simpa [rightIndex, rightReplacement] using rightEffect

/-- Interpreter-facing retained absolute-slot write: related live operands and
one successful source update determine a successful related target update. -/
theorem ShadowRuntimeRel.setUSizeSlotBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (fields : ValueRel rho leftField rightField)
    (sourceEffect :
      setUSizeSlot left leftObject slot leftField = .ok leftResult) :
    ∃ rightResult,
      setUSizeSlot right rightObject slot rightField = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases fields with
  | tagged payload => simp [setUSizeSlot] at sourceEffect
  | heap fieldMapping => simp [setUSizeSlot] at sourceEffect
  | scalar field => simp [setUSizeSlot] at sourceEffect
  | erased => simp [setUSizeSlot] at sourceEffect
  | reuseNone => simp [setUSizeSlot] at sourceEffect
  | reuseSome fieldMapping => simp [setUSizeSlot] at sourceEffect
  | usize field =>
      cases objects with
      | tagged payload =>
          simp [setUSizeSlot, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | usize value =>
          simp [setUSizeSlot, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | scalar value =>
          simp [setUSizeSlot, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | erased =>
          simp [setUSizeSlot, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | reuseNone =>
          simp [setUSizeSlot, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | reuseSome mapping =>
          simp [setUSizeSlot, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | heap mapping =>
          rename_i leftLocation rightLocation
          have originalSourceEffect := sourceEffect
          unfold setUSizeSlot modifyConstructor at sourceEffect
          simp only [Bind.bind, Except.bind] at sourceEffect
          generalize constructorEq :
            getConstructor left (.object (.heap leftLocation)) =
              constructorResult at sourceEffect
          cases constructorResult with
          | error fault =>
              simp at sourceEffect
          | ok result =>
              obtain ⟨resultLocation, leftCell, leftConstructor⟩ := result
              simp only at sourceEffect
              by_cases lower :
                  leftConstructor.objectFields.size ≤ slot
              · rw [if_pos lower] at sourceEffect
                by_cases bounded :
                    slot - leftConstructor.objectFields.size <
                      leftConstructor.usizeFields.size
                · rw [dif_pos bounded] at sourceEffect
                  simp only at sourceEffect
                  rcases getConstructor_heap_spec constructorEq with
                    ⟨resultLocationEq, leftFound, leftLive, leftObjectEq⟩
                  subst resultLocation
                  have reachable :
                      Reachable left.heap (runtimeRoots left leftExtra)
                        leftLocation := by
                    exact .root (extra_subset_runtimeRoots left leftExtra
                      (.object (.heap leftLocation)) objectRoot)
                  rcases related.setUSizeSlotBoth mapping reachable leftFound
                      leftLive leftObjectEq lower bounded field with
                    ⟨computedLeft, rightResult, leftEffect, rightEffect,
                      next⟩
                  rw [originalSourceEffect] at leftEffect
                  cases leftEffect
                  exact ⟨rightResult, rightEffect, next⟩
                · rw [dif_neg bounded] at sourceEffect
                  simp at sourceEffect
              · rw [if_neg lower] at sourceEffect
                simp at sourceEffect

/-- An absolute final-LCNF unboxed-word slot changes only an unreachable cell.
Object fields occupy the fixed-slot prefix before the type-local `USize`
array. -/
theorem ShadowRuntimeRel.setUSizeSlotLeftUnreachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (found : findCell? left.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor object)
    (lower : object.objectFields.size ≤ slot)
    (bounded : slot - object.objectFields.size < object.usizeFields.size)
    (unreachable : ¬Reachable
      left.heap (runtimeRoots left leftExtra) location)
    (field : UInt64) :
    ∃ result,
      setUSizeSlot left (.object (.heap location)) slot (.usize field) =
        .ok result ∧
      ShadowRuntimeRel rho result right leftExtra rightExtra := by
  let index := slot - object.objectFields.size
  let replacement : HeapCell :=
    { cell with object := .ctor {
        object with usizeFields := object.usizeFields.set index field } }
  rcases related.setCellLeftUnreachable found unreachable replacement with
    ⟨result, effect, next⟩
  refine ⟨result, ?_, next⟩
  have constructor : getConstructor left (.object (.heap location)) =
      .ok (location, cell, object) := by
    simp [getConstructor, getLiveCell, found, live, objectEq,
      Bind.bind, Except.bind]
    rfl
  unfold setUSizeSlot modifyConstructor
  rw [constructor]
  simp only [Bind.bind, Except.bind]
  rw [if_pos lower, dif_pos bounded]
  simpa [index, replacement] using effect

/-- A retained packed-scalar write updates the same `(width, offset)` entry
inside one mapped constructor pair. Scalar fields contain no ownership edges,
so the existing paired-cell replacement theorem applies directly. -/
theorem ShadowRuntimeRel.setScalarFieldBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (leftLive : leftCell.live = true)
    (leftObjectEq : leftCell.object = .ctor leftObject)
    (width offset : Nat) (field : ScalarValue) :
    ∃ leftResult rightResult,
      setScalarField left (.object (.heap leftLocation)) width offset
          (.scalar field) = .ok leftResult ∧
      setScalarField right (.object (.heap rightLocation)) width offset
          (.scalar field) = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have mappedSame : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have leftCellSame : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  have rightLive : rightCell.live = true := by
    rw [← cells.2.2.1]
    exact leftLive
  have objects := cells.2.2.2
  generalize rightObjectEq : rightCell.object = targetObject at objects
  rw [leftObjectEq] at objects
  cases objects with
  | ctor tag objectFields usizes scalars =>
      rename_i rightObject
      let entry : ScalarField := { width, offset, value := field }
      let leftFields := entry :: leftObject.scalarFields.filter fun old =>
        old.width != width || old.offset != offset
      let rightFields := entry :: rightObject.scalarFields.filter fun old =>
        old.width != width || old.offset != offset
      have fieldsEq : leftFields = rightFields := by
        simp [leftFields, rightFields, scalars]
      let leftReplacement : HeapCell :=
        { leftCell with object := .ctor {
            leftObject with scalarFields := leftFields } }
      let rightReplacement : HeapCell :=
        { rightCell with object := .ctor {
            rightObject with scalarFields := rightFields } }
      have replacement :
          HeapCellRel rho leftReplacement rightReplacement := by
        refine ⟨cells.1, cells.2.1, cells.2.2.1, ?_⟩
        dsimp only [leftReplacement, rightReplacement]
        exact @HeapObjectRel.ctor rho
          { leftObject with scalarFields := leftFields }
          { rightObject with scalarFields := rightFields }
          tag objectFields usizes fieldsEq
      have leftOwned :
          leftReplacement.object.ownedValues =
            leftCell.object.ownedValues := by
        simp [leftReplacement, leftObjectEq, HeapObject.ownedValues]
      have rightOwned :
          rightReplacement.object.ownedValues =
            rightCell.object.ownedValues := by
        simp [rightReplacement, rightObjectEq, HeapObject.ownedValues]
      rcases related.setCellBoth mapping leftFound rightFound
          leftOwned rightOwned replacement with
        ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
      refine ⟨leftResult, rightResult, ?_, ?_, next⟩
      · have constructor :
            getConstructor left (.object (.heap leftLocation)) =
              .ok (leftLocation, leftCell, leftObject) := by
          simp [getConstructor, getLiveCell, leftFound, leftLive,
            leftObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setScalarField modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        simpa [entry, leftFields, leftReplacement] using leftEffect
      · have constructor :
            getConstructor right (.object (.heap rightLocation)) =
              .ok (rightLocation, rightCell, rightObject) := by
          simp [getConstructor, getLiveCell, rightFound, rightLive,
            rightObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setScalarField modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        simpa [entry, rightFields, rightReplacement] using rightEffect

/-- Interpreter-facing retained scalar write: related operands and one
successful source mutation determine the identical packed-scalar update on
the related target constructor. -/
theorem ShadowRuntimeRel.setScalarFieldBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (fields : ValueRel rho leftField rightField)
    (sourceEffect :
      setScalarField left leftObject width offset leftField = .ok leftResult) :
    ∃ rightResult,
      setScalarField right rightObject width offset rightField =
          .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases fields with
  | tagged payload => simp [setScalarField] at sourceEffect
  | heap fieldMapping => simp [setScalarField] at sourceEffect
  | usize field => simp [setScalarField] at sourceEffect
  | erased => simp [setScalarField] at sourceEffect
  | reuseNone => simp [setScalarField] at sourceEffect
  | reuseSome fieldMapping => simp [setScalarField] at sourceEffect
  | scalar field =>
      cases objects with
      | tagged payload =>
          simp [setScalarField, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | usize value =>
          simp [setScalarField, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | scalar value =>
          simp [setScalarField, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | erased =>
          simp [setScalarField, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | reuseNone =>
          simp [setScalarField, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | reuseSome mapping =>
          simp [setScalarField, modifyConstructor, getConstructor,
            Bind.bind, Except.bind] at sourceEffect
      | heap mapping =>
          rename_i leftLocation rightLocation
          have originalSourceEffect := sourceEffect
          unfold setScalarField modifyConstructor at sourceEffect
          simp only [Bind.bind, Except.bind] at sourceEffect
          generalize constructorEq :
            getConstructor left (.object (.heap leftLocation)) =
              constructorResult at sourceEffect
          cases constructorResult with
          | error fault =>
              simp at sourceEffect
          | ok result =>
              obtain ⟨resultLocation, leftCell, leftConstructor⟩ := result
              simp only at sourceEffect
              rcases getConstructor_heap_spec constructorEq with
                ⟨resultLocationEq, leftFound, leftLive, leftObjectEq⟩
              subst resultLocation
              have reachable :
                  Reachable left.heap (runtimeRoots left leftExtra)
                    leftLocation := by
                exact .root (extra_subset_runtimeRoots left leftExtra
                  (.object (.heap leftLocation)) objectRoot)
              rcases related.setScalarFieldBoth mapping reachable leftFound
                  leftLive leftObjectEq width offset field with
                ⟨computedLeft, rightResult, leftEffect, rightEffect, next⟩
              rw [originalSourceEffect] at leftEffect
              cases leftEffect
              exact ⟨rightResult, rightEffect, next⟩

/-- Updating the constructor tag of one mapped live pair preserves the
reachable runtime relation. Tags carry no ownership edges. -/
theorem ShadowRuntimeRel.setTagBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (leftLive : leftCell.live = true)
    (leftObjectEq : leftCell.object = .ctor leftObject)
    (tag : Nat) :
    ∃ leftResult rightResult,
      setTag left (.object (.heap leftLocation)) tag = .ok leftResult ∧
      setTag right (.object (.heap rightLocation)) tag = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have mappedSame : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have leftCellSame : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  have rightLive : rightCell.live = true := by
    rw [← cells.2.2.1]
    exact leftLive
  have objects := cells.2.2.2
  generalize rightObjectEq : rightCell.object = targetObject at objects
  rw [leftObjectEq] at objects
  cases objects with
  | ctor oldTag objectFields usizes scalars =>
      rename_i rightObject
      let leftReplacement : HeapCell :=
        { leftCell with object := .ctor { leftObject with tag } }
      let rightReplacement : HeapCell :=
        { rightCell with object := .ctor { rightObject with tag } }
      have replacement :
          HeapCellRel rho leftReplacement rightReplacement := by
        refine ⟨cells.1, cells.2.1, cells.2.2.1, ?_⟩
        dsimp only [leftReplacement, rightReplacement]
        exact @HeapObjectRel.ctor rho
          { leftObject with tag }
          { rightObject with tag }
          rfl objectFields usizes scalars
      have leftOwned :
          leftReplacement.object.ownedValues =
            leftCell.object.ownedValues := by
        simp [leftReplacement, leftObjectEq, HeapObject.ownedValues]
      have rightOwned :
          rightReplacement.object.ownedValues =
            rightCell.object.ownedValues := by
        simp [rightReplacement, rightObjectEq, HeapObject.ownedValues]
      rcases related.setCellBoth mapping leftFound rightFound
          leftOwned rightOwned replacement with
        ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
      refine ⟨leftResult, rightResult, ?_, ?_, next⟩
      · have constructor :
            getConstructor left (.object (.heap leftLocation)) =
              .ok (leftLocation, leftCell, leftObject) := by
          simp [getConstructor, getLiveCell, leftFound, leftLive,
            leftObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setTag modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        simpa [leftReplacement] using leftEffect
      · have constructor :
            getConstructor right (.object (.heap rightLocation)) =
              .ok (rightLocation, rightCell, rightObject) := by
          simp [getConstructor, getLiveCell, rightFound, rightLive,
            rightObjectEq, Bind.bind, Except.bind]
          rfl
        unfold setTag modifyConstructor
        rw [constructor]
        simp only [Bind.bind, Except.bind]
        simpa [rightReplacement] using rightEffect

/-- Interpreter-facing retained tag write. -/
theorem ShadowRuntimeRel.setTagBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceEffect : setTag left leftObject tag = .ok leftResult) :
    ∃ rightResult,
      setTag right rightObject tag = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases objects with
  | tagged payload =>
      simp [setTag, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | usize value =>
      simp [setTag, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | scalar value =>
      simp [setTag, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | erased =>
      simp [setTag, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | reuseNone =>
      simp [setTag, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | reuseSome mapping =>
      simp [setTag, modifyConstructor, getConstructor,
        Bind.bind, Except.bind] at sourceEffect
  | heap mapping =>
      rename_i leftLocation rightLocation
      have originalSourceEffect := sourceEffect
      unfold setTag modifyConstructor at sourceEffect
      simp only [Bind.bind, Except.bind] at sourceEffect
      generalize constructorEq :
        getConstructor left (.object (.heap leftLocation)) =
          constructorResult at sourceEffect
      cases constructorResult with
      | error fault =>
          simp at sourceEffect
      | ok result =>
          obtain ⟨resultLocation, leftCell, leftConstructor⟩ := result
          simp only at sourceEffect
          rcases getConstructor_heap_spec constructorEq with
            ⟨resultLocationEq, leftFound, leftLive, leftObjectEq⟩
          subst resultLocation
          have reachable :
              Reachable left.heap (runtimeRoots left leftExtra)
                leftLocation := by
            exact .root (extra_subset_runtimeRoots left leftExtra
              (.object (.heap leftLocation)) objectRoot)
          rcases related.setTagBoth mapping reachable leftFound leftLive
              leftObjectEq tag with
            ⟨computedLeft, rightResult, leftEffect, rightEffect, next⟩
          rw [originalSourceEffect] at leftEffect
          cases leftEffect
          exact ⟨rightResult, rightEffect, next⟩

/-- Incrementing one reachable mapped heap reference updates equal reference
counts on both sides. Persistent cells are synchronized no-ops. -/
theorem ShadowRuntimeRel.incLocationBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (leftLive : leftCell.live = true)
    (amount : Nat) :
    ∃ leftResult rightResult,
      incLocation left leftLocation amount = .ok leftResult ∧
      incLocation right rightLocation amount = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  rcases related.heap.1 leftLocation leftReachable with
    ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft, rightFound,
      cells⟩
  have mappedSame : mapped = rightLocation := by
    rw [mapping] at mappedEq
    exact (Option.some.inj mappedEq).symm
  subst mapped
  have leftCellSame : foundLeftCell = leftCell := by
    rw [leftFound] at foundLeft
    exact (Option.some.inj foundLeft).symm
  subst foundLeftCell
  have rightLive : rightCell.live = true := by
    rw [← cells.2.2.1]
    exact leftLive
  have leftGet : getLiveCell left leftLocation = .ok leftCell := by
    simp [getLiveCell, leftFound, leftLive]
  have rightGet : getLiveCell right rightLocation = .ok rightCell := by
    simp [getLiveCell, rightFound, rightLive]
  cases persistentEq : leftCell.persistent with
  | true =>
      have rightPersistent : rightCell.persistent = true := by
        rw [← cells.2.1]
        exact persistentEq
      refine ⟨left, right, ?_, ?_, related⟩
      · unfold incLocation
        rw [leftGet]
        simp only [Bind.bind, Except.bind]
        rw [if_pos (by simp [persistentEq])]
        rfl
      · unfold incLocation
        rw [rightGet]
        simp only [Bind.bind, Except.bind]
        rw [if_pos (by simp [rightPersistent])]
        rfl
  | false =>
      have rightPersistent : rightCell.persistent = false := by
        rw [← cells.2.1]
        exact persistentEq
      let leftReplacement : HeapCell :=
        { leftCell with rc := leftCell.rc + amount }
      let rightReplacement : HeapCell :=
        { rightCell with rc := rightCell.rc + amount }
      have replacement :
          HeapCellRel rho leftReplacement rightReplacement := by
        refine ⟨?_, cells.2.1, cells.2.2.1, cells.2.2.2⟩
        simp [leftReplacement, rightReplacement, cells.1]
      have leftOwned :
          leftReplacement.object.ownedValues =
            leftCell.object.ownedValues := by
        simp [leftReplacement]
      have rightOwned :
          rightReplacement.object.ownedValues =
            rightCell.object.ownedValues := by
        simp [rightReplacement]
      rcases related.setCellBoth mapping leftFound rightFound
          leftOwned rightOwned replacement with
        ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
      refine ⟨leftResult, rightResult, ?_, ?_, next⟩
      · unfold incLocation
        rw [leftGet]
        simp only [Bind.bind, Except.bind]
        rw [if_neg (by simp [persistentEq])]
        simpa [leftReplacement] using leftEffect
      · unfold incLocation
        rw [rightGet]
        simp only [Bind.bind, Except.bind]
        rw [if_neg (by simp [rightPersistent])]
        simpa [rightReplacement] using rightEffect

/-- Interpreter-facing retained increment. A successful source effect fixes
the same successful target effect for related live operands. -/
theorem ShadowRuntimeRel.incValueBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceEffect :
      incValue left leftObject amount check = .ok leftResult) :
    ∃ rightResult,
      incValue right rightObject amount check = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases objects with
  | tagged payload =>
      cases check with
      | false => simp [incValue] at sourceEffect
      | true =>
          simp [incValue] at sourceEffect
          subst leftResult
          exact ⟨right, by simp [incValue], related⟩
  | usize value => simp [incValue] at sourceEffect
  | scalar value => simp [incValue] at sourceEffect
  | erased => simp [incValue] at sourceEffect
  | reuseNone => simp [incValue] at sourceEffect
  | reuseSome mapping => simp [incValue] at sourceEffect
  | heap mapping =>
      rename_i leftLocation rightLocation
      have originalSourceEffect := sourceEffect
      have sourceLocationEffect :
          incLocation left leftLocation amount = .ok leftResult := by
        simpa [incValue] using originalSourceEffect
      unfold incValue incLocation at sourceEffect
      simp only [Bind.bind, Except.bind] at sourceEffect
      generalize liveEq :
        getLiveCell left leftLocation = liveResult at sourceEffect
      cases liveResult with
      | error fault =>
          simp at sourceEffect
      | ok leftCell =>
          rcases getLiveCell_spec liveEq with ⟨leftFound, leftLive⟩
          have reachable :
              Reachable left.heap (runtimeRoots left leftExtra)
                leftLocation := by
            exact .root (extra_subset_runtimeRoots left leftExtra
              (.object (.heap leftLocation)) objectRoot)
          rcases related.incLocationBoth mapping reachable leftFound leftLive
              amount with
            ⟨computedLeft, rightResult, leftEffect, rightEffect, next⟩
          rw [sourceLocationEffect] at leftEffect
          cases leftEffect
          exact ⟨rightResult, by simpa [incValue] using rightEffect, next⟩

/-- Publish a related pair of cells' owned values as temporary direct roots.
This is the ownership-release frame: after the parent is marked dead, every
child remains available to the recursive left-to-right decrement fold even
when an earlier sibling release changes the heap. -/
theorem ShadowRuntimeRel.publishOwnedValues
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (rightReachable :
      Reachable right.heap (runtimeRoots right rightExtra) rightLocation)
    (leftFound : findCell? left.heap leftLocation = some leftCell)
    (rightFound : findCell? right.heap rightLocation = some rightCell)
    (cells : HeapCellRel rho leftCell rightCell) :
    ShadowRuntimeRel rho left right
      (leftCell.object.ownedValues.toList ++ leftExtra)
      (rightCell.object.ownedValues.toList ++ rightExtra) := by
  apply related.reindexExtra
    (listRel_append (heapCellRel_ownedValues cells) related.extra)
  · intro location reachable
    apply reachable_monoRootReachability (larger :=
      runtimeRoots left leftExtra) ?_ reachable
    intro child member
    simp only [runtimeRoots, List.mem_append] at member
    rcases member with ((owned | extra) | global) | trace
    · exact .child leftReachable leftFound owned rfl
    · exact .root (by simp [runtimeRoots, extra])
    · exact .root (by simp [runtimeRoots, global])
    · exact .root (by simp [runtimeRoots, trace])
  · intro location reachable
    apply reachable_monoRootReachability (larger :=
      runtimeRoots right rightExtra) ?_ reachable
    intro child member
    simp only [runtimeRoots, List.mem_append] at member
    rcases member with ((owned | extra) | global) | trace
    · exact .child rightReachable rightFound owned rfl
    · exact .root (by simp [runtimeRoots, extra])
    · exact .root (by simp [runtimeRoots, global])
    · exact .root (by simp [runtimeRoots, trace])

/-- Successful semantic recursive release is monotone in fuel. Enlarging the
depth budget cannot change the selected branch or final runtime. -/
theorem decLocationFuel_ok_mono
    {fuel more : Nat} {runtime result : RuntimeState} {location : Location}
    (fuelLe : fuel ≤ more)
    (operation : decLocationFuel fuel runtime location = .ok result) :
    decLocationFuel more runtime location = .ok result := by
  induction fuel generalizing more runtime result location with
  | zero =>
      simp [decLocationFuel] at operation
  | succ fuel recurse =>
      cases more with
      | zero => omega
      | succ more =>
          have smaller : fuel ≤ more := by omega
          generalize cellEq : getLiveCell runtime location = cellResult
          cases cellResult with
          | error fault =>
              simp [decLocationFuel, cellEq, Bind.bind, Except.bind] at operation
          | ok cell =>
              by_cases persistent : cell.persistent = true
              · simpa [decLocationFuel, cellEq, Bind.bind, Except.bind,
                  persistent] using operation
              · by_cases zero : cell.rc = 0
                · simp [decLocationFuel, cellEq, Bind.bind, Except.bind,
                    persistent, zero] at operation
                · by_cases above : 1 < cell.rc
                  · simpa [decLocationFuel, cellEq, Bind.bind, Except.bind,
                      persistent, zero, above] using operation
                  · cases releasedEq :
                      setCell runtime location { cell with rc := 0, live := false } with
                    | error fault =>
                        simp only [decLocationFuel, cellEq, Bind.bind,
                          Except.bind] at operation
                        rw [if_neg persistent, if_neg zero, if_neg above]
                          at operation
                        rw [releasedEq] at operation
                        contradiction
                    | ok released =>
                        simp only [decLocationFuel, cellEq, Bind.bind,
                          Except.bind] at operation ⊢
                        rw [if_neg persistent, if_neg zero, if_neg above]
                          at operation ⊢
                        rw [releasedEq] at operation ⊢
                        have foldMono : ∀ (values : List Value)
                            (before after : RuntimeState),
                            values.foldlM (init := before) (fun next value =>
                              match value with
                              | .object (.heap child) =>
                                  decLocationFuel fuel next child
                              | _ => .ok next) = .ok after →
                            values.foldlM (init := before) (fun next value =>
                              match value with
                              | .object (.heap child) =>
                                  decLocationFuel more next child
                              | _ => .ok next) = .ok after := by
                          intro values
                          induction values with
                          | nil =>
                              intro before after folded
                              simpa using folded
                          | cons value values tailIH =>
                              intro before after folded
                              simp only [List.foldlM_cons, Bind.bind,
                                Except.bind] at folded ⊢
                              cases value with
                              | object reference =>
                                  cases reference with
                                  | tagged payload =>
                                      exact tailIH before after folded
                                  | heap child =>
                                      dsimp only at folded ⊢
                                      cases childEq :
                                          decLocationFuel fuel before child with
                                      | error fault =>
                                          rw [childEq] at folded
                                          contradiction
                                      | ok middle =>
                                          rw [childEq] at folded
                                          rw [recurse smaller childEq]
                                          exact tailIH middle after folded
                              | usize | scalar | erased | reuseToken =>
                                  exact tailIH before after folded
                        dsimp only at operation ⊢
                        rw [← Array.foldlM_toList] at operation ⊢
                        exact foldMono cell.object.ownedValues.toList
                          released result operation

/-- One common positive fuel budget drives corresponding recursive releases
through the same ownership graph. The source's successful execution fixes the
branch and result; the target follows under the reachable-heap relation. -/
theorem ShadowRuntimeRel.decLocationFuelBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (sourceEffect :
      decLocationFuel fuel left leftLocation = .ok leftResult) :
    ∃ rightResult,
      decLocationFuel fuel right rightLocation = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  induction fuel generalizing left right leftExtra rightExtra leftLocation
      rightLocation leftResult with
  | zero =>
      simp [decLocationFuel] at sourceEffect
  | succ fuel recurse =>
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mapped, leftCell, rightCell, mappedEq, leftFound, rightFound, cells⟩
      have mappedSame : mapped = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mapped
      rcases reachable_forward related.roots related.heap leftReachable with
        ⟨mappedReachable, reachableMapping, rightReachable⟩
      have reachableSame : mappedReachable = rightLocation := by
        rw [mapping] at reachableMapping
        exact (Option.some.inj reachableMapping).symm
      subst mappedReachable
      cases leftLive : leftCell.live with
      | false =>
          simp [decLocationFuel, getLiveCell, leftFound, leftLive,
            Bind.bind, Except.bind] at sourceEffect
      | true =>
          have rightLive : rightCell.live = true := by
            rw [← cells.2.2.1]
            exact leftLive
          have leftGet : getLiveCell left leftLocation = .ok leftCell := by
            simp [getLiveCell, leftFound, leftLive]
          have rightGet : getLiveCell right rightLocation = .ok rightCell := by
            simp [getLiveCell, rightFound, rightLive]
          cases leftPersistent : leftCell.persistent with
          | true =>
              have rightPersistent : rightCell.persistent = true := by
                rw [← cells.2.1]
                exact leftPersistent
              have leftNoop :
                  decLocationFuel (fuel + 1) left leftLocation = .ok left := by
                simp only [decLocationFuel, leftGet, Bind.bind, Except.bind]
                rw [if_pos (by simp [leftPersistent])]
                rfl
              have rightNoop :
                  decLocationFuel (fuel + 1) right rightLocation = .ok right := by
                simp only [decLocationFuel, rightGet, Bind.bind, Except.bind]
                rw [if_pos (by simp [rightPersistent])]
                rfl
              rw [leftNoop] at sourceEffect
              have resultEq := Except.ok.inj sourceEffect
              subst leftResult
              exact ⟨right, rightNoop, related⟩
          | false =>
              have rightPersistent : rightCell.persistent = false := by
                rw [← cells.2.1]
                exact leftPersistent
              by_cases leftZero : leftCell.rc = 0
              · simp only [decLocationFuel, leftGet, Bind.bind,
                  Except.bind] at sourceEffect
                rw [if_neg (by simp [leftPersistent])] at sourceEffect
                rw [if_pos leftZero] at sourceEffect
                simp at sourceEffect
              · have rightNonzero : rightCell.rc ≠ 0 := by
                  rw [← cells.1]
                  exact leftZero
                by_cases leftAbove : 1 < leftCell.rc
                · have rightAbove : 1 < rightCell.rc := by
                    rw [← cells.1]
                    exact leftAbove
                  let leftReplacement : HeapCell :=
                    { leftCell with rc := leftCell.rc - 1 }
                  let rightReplacement : HeapCell :=
                    { rightCell with rc := rightCell.rc - 1 }
                  have replacement :
                      HeapCellRel rho leftReplacement rightReplacement := by
                    refine ⟨?_, cells.2.1, cells.2.2.1, cells.2.2.2⟩
                    simp [leftReplacement, rightReplacement, cells.1]
                  have leftOwned :
                      leftReplacement.object.ownedValues =
                        leftCell.object.ownedValues := by
                    simp [leftReplacement]
                  have rightOwned :
                      rightReplacement.object.ownedValues =
                        rightCell.object.ownedValues := by
                    simp [rightReplacement]
                  rcases related.setCellBoth mapping leftFound rightFound
                      leftOwned rightOwned replacement with
                    ⟨computedLeft, rightResult, leftEffect, rightEffect, next⟩
                  have leftBranch :
                      decLocationFuel (fuel + 1) left leftLocation =
                        setCell left leftLocation leftReplacement := by
                    simp only [decLocationFuel, leftGet, Bind.bind, Except.bind]
                    rw [if_neg (by simp [leftPersistent])]
                    rw [if_neg leftZero, if_pos leftAbove]
                  have rightBranch :
                      decLocationFuel (fuel + 1) right rightLocation =
                        setCell right rightLocation rightReplacement := by
                    simp only [decLocationFuel, rightGet, Bind.bind, Except.bind]
                    rw [if_neg (by simp [rightPersistent])]
                    rw [if_neg rightNonzero, if_pos rightAbove]
                  rw [leftBranch, leftEffect] at sourceEffect
                  have resultEq := Except.ok.inj sourceEffect
                  subst leftResult
                  exact ⟨rightResult, rightBranch.trans rightEffect, next⟩
                · have leftOne : leftCell.rc = 1 := by omega
                  have rightNotAbove : ¬1 < rightCell.rc := by
                    rw [← cells.1]
                    exact leftAbove
                  let leftReplacement : HeapCell :=
                    { leftCell with rc := 0, live := false }
                  let rightReplacement : HeapCell :=
                    { rightCell with rc := 0, live := false }
                  have replacement :
                      HeapCellRel rho leftReplacement rightReplacement := by
                    refine ⟨by simp [leftReplacement, rightReplacement],
                      cells.2.1, by simp [leftReplacement, rightReplacement],
                      cells.2.2.2⟩
                  have leftOwned :
                      leftReplacement.object.ownedValues =
                        leftCell.object.ownedValues := by
                    simp [leftReplacement]
                  have rightOwned :
                      rightReplacement.object.ownedValues =
                        rightCell.object.ownedValues := by
                    simp [rightReplacement]
                  have published := related.publishOwnedValues leftReachable
                    rightReachable leftFound rightFound cells
                  rcases published.setCellBoth mapping leftFound rightFound
                      leftOwned rightOwned replacement with
                    ⟨parentLeft, parentRight, parentLeftEffect,
                      parentRightEffect, parentRelated⟩
                  let releaseChild (runtime : RuntimeState) (value : Value) :
                      Except RuntimeFault RuntimeState :=
                    match value with
                    | .object (.heap child) =>
                        decLocationFuel fuel runtime child
                    | _ => .ok runtime
                  have sourceFoldArray :
                      Array.foldlM releaseChild parentLeft
                          leftCell.object.ownedValues = .ok leftResult := by
                    simp only [decLocationFuel, leftGet, Bind.bind,
                      Except.bind] at sourceEffect
                    rw [if_neg (by simp [leftPersistent])] at sourceEffect
                    rw [if_neg leftZero, if_neg leftAbove] at sourceEffect
                    rw [parentLeftEffect] at sourceEffect
                    change Array.foldlM releaseChild parentLeft
                      leftCell.object.ownedValues = .ok leftResult at sourceEffect
                    exact sourceEffect
                  have sourceFoldList :
                      leftCell.object.ownedValues.toList.foldlM
                          (init := parentLeft) releaseChild = .ok leftResult := by
                    simpa only [Array.foldlM_toList] using sourceFoldArray
                  have foldBoth : ∀
                      {leftValues rightValues : List Value}
                      {beforeLeft beforeRight afterLeft : RuntimeState},
                      ListRel (ValueRel rho) leftValues rightValues →
                      RootSubset leftValues leftCell.object.ownedValues.toList →
                      RootSubset rightValues rightCell.object.ownedValues.toList →
                      ShadowRuntimeRel rho beforeLeft beforeRight
                        (leftCell.object.ownedValues.toList ++ leftExtra)
                        (rightCell.object.ownedValues.toList ++ rightExtra) →
                      leftValues.foldlM (init := beforeLeft) releaseChild =
                        .ok afterLeft →
                      ∃ afterRight,
                        rightValues.foldlM (init := beforeRight) releaseChild =
                            .ok afterRight ∧
                        ShadowRuntimeRel rho afterLeft afterRight
                          (leftCell.object.ownedValues.toList ++ leftExtra)
                          (rightCell.object.ownedValues.toList ++ rightExtra) := by
                    intro leftValues rightValues beforeLeft beforeRight afterLeft
                      values leftSubset rightSubset states operation
                    induction values generalizing beforeLeft beforeRight afterLeft with
                    | nil =>
                        simp only [List.foldlM_nil] at operation ⊢
                        have stateEq := Except.ok.inj operation
                        subst afterLeft
                        exact ⟨beforeRight, rfl, states⟩
                    | @cons leftHead rightHead leftTail rightTail heads tails tailIH =>
                        have leftTailSubset :
                            RootSubset leftTail
                              leftCell.object.ownedValues.toList := by
                          intro value member
                          exact leftSubset value
                            (List.mem_cons_of_mem leftHead member)
                        have rightTailSubset :
                            RootSubset rightTail
                              rightCell.object.ownedValues.toList := by
                          intro value member
                          exact rightSubset value
                            (List.mem_cons_of_mem rightHead member)
                        simp only [List.foldlM_cons, Bind.bind, Except.bind]
                          at operation ⊢
                        cases heads with
                        | heap childMapping =>
                            rename_i leftChild rightChild
                            simp only [releaseChild] at operation ⊢
                            cases childEffect :
                                decLocationFuel fuel beforeLeft leftChild with
                            | error fault =>
                                rw [childEffect] at operation
                                contradiction
                            | ok nextLeft =>
                                rw [childEffect] at operation
                                have childMember :
                                    Value.object (.heap leftChild) ∈
                                      leftCell.object.ownedValues.toList :=
                                  leftSubset _ List.mem_cons_self
                                have childReachable :
                                    Reachable beforeLeft.heap
                                      (runtimeRoots beforeLeft
                                        (leftCell.object.ownedValues.toList ++
                                          leftExtra)) leftChild := by
                                  exact .root (extra_subset_runtimeRoots beforeLeft
                                    (leftCell.object.ownedValues.toList ++ leftExtra)
                                    _ (List.mem_append_left _ childMember))
                                rcases recurse states childMapping childReachable
                                    childEffect with
                                  ⟨nextRight, rightChildEffect, nextStates⟩
                                rw [rightChildEffect]
                                exact tailIH leftTailSubset rightTailSubset
                                  nextStates operation
                        | tagged | usize | scalar | erased | reuseNone | reuseSome =>
                            exact tailIH leftTailSubset rightTailSubset
                              states operation
                  rcases foldBoth (heapCellRel_ownedValues cells)
                      (RootSubset.refl _) (RootSubset.refl _) parentRelated
                      sourceFoldList with
                    ⟨rightResult, targetFoldList, finalPublished⟩
                  have targetFoldArray :
                      Array.foldlM releaseChild parentRight
                          rightCell.object.ownedValues = .ok rightResult := by
                    simpa only [Array.foldlM_toList] using targetFoldList
                  have targetEffect :
                      decLocationFuel (fuel + 1) right rightLocation =
                        .ok rightResult := by
                    simp only [decLocationFuel, rightGet, Bind.bind, Except.bind]
                    rw [if_neg (by simp [rightPersistent])]
                    rw [if_neg rightNonzero, if_neg rightNotAbove]
                    rw [parentRightEffect]
                    exact targetFoldArray
                  have finalRelated := finalPublished.restrictExtra related.extra
                    (by
                      intro value member
                      exact List.mem_append_right _ member)
                    (by
                      intro value member
                      exact List.mem_append_right _ member)
                  exact ⟨rightResult, targetEffect, finalRelated⟩

/-- Interpreter-facing retained delete. Erased failed-reset tokens are
synchronized no-ops; a related live heap operand marks the mapped cells dead
without recursively changing their owned values. -/
theorem ShadowRuntimeRel.deleteValueBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceEffect : deleteValue left leftObject = .ok leftResult) :
    ∃ rightResult,
      deleteValue right rightObject = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases objects with
  | tagged payload => simp [deleteValue] at sourceEffect
  | usize value => simp [deleteValue] at sourceEffect
  | scalar value => simp [deleteValue] at sourceEffect
  | reuseNone => simp [deleteValue] at sourceEffect
  | reuseSome mapping => simp [deleteValue] at sourceEffect
  | erased =>
      simp [deleteValue] at sourceEffect
      subst leftResult
      exact ⟨right, by simp [deleteValue], related⟩
  | heap mapping =>
      rename_i leftLocation rightLocation
      unfold deleteValue at sourceEffect
      simp only [Bind.bind, Except.bind] at sourceEffect
      generalize liveEq :
        getLiveCell left leftLocation = liveResult at sourceEffect
      cases liveResult with
      | error fault =>
          simp at sourceEffect
      | ok leftCell =>
          rcases getLiveCell_spec liveEq with ⟨leftFound, leftLive⟩
          have reachable :
              Reachable left.heap (runtimeRoots left leftExtra)
                leftLocation := by
            exact .root (extra_subset_runtimeRoots left leftExtra
              (.object (.heap leftLocation)) objectRoot)
          rcases related.heap.1 leftLocation reachable with
            ⟨mapped, foundLeftCell, rightCell, mappedEq, foundLeft,
              rightFound, cells⟩
          have mappedSame : mapped = rightLocation := by
            rw [mapping] at mappedEq
            exact (Option.some.inj mappedEq).symm
          subst mapped
          have leftCellSame : foundLeftCell = leftCell := by
            rw [leftFound] at foundLeft
            exact (Option.some.inj foundLeft).symm
          subst foundLeftCell
          have rightLive : rightCell.live = true := by
            rw [← cells.2.2.1]
            exact leftLive
          let leftReplacement : HeapCell :=
            { leftCell with rc := 0, live := false }
          let rightReplacement : HeapCell :=
            { rightCell with rc := 0, live := false }
          have replacement :
              HeapCellRel rho leftReplacement rightReplacement := by
            refine ⟨by simp [leftReplacement, rightReplacement],
              cells.2.1, by simp [leftReplacement, rightReplacement],
              cells.2.2.2⟩
          have leftOwned :
              leftReplacement.object.ownedValues =
                leftCell.object.ownedValues := by
            simp [leftReplacement]
          have rightOwned :
              rightReplacement.object.ownedValues =
                rightCell.object.ownedValues := by
            simp [rightReplacement]
          rcases related.setCellBoth mapping leftFound rightFound
              leftOwned rightOwned replacement with
            ⟨computedLeft, rightResult, leftSet, rightSet, next⟩
          change setCell left leftLocation leftReplacement =
            .ok leftResult at sourceEffect
          rw [sourceEffect] at leftSet
          have resultEq := Except.ok.inj leftSet
          subst computedLeft
          have targetEffect :
              deleteValue right (.object (.heap rightLocation)) =
                .ok rightResult := by
            unfold deleteValue
            simp only [Bind.bind, Except.bind]
            have rightGet :
                getLiveCell right rightLocation = .ok rightCell := by
              simp [getLiveCell, rightFound, rightLive]
            rw [rightGet]
            exact rightSet
          exact ⟨rightResult, targetEffect, next⟩

/-- Scalar writes replace the `(width, offset)` entry only inside the
unreachable source cell. -/
theorem ShadowRuntimeRel.setScalarFieldLeftUnreachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (found : findCell? left.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor object)
    (unreachable : ¬Reachable
      left.heap (runtimeRoots left leftExtra) location)
    (width offset : Nat) (field : ScalarValue) :
    ∃ result,
      setScalarField left (.object (.heap location)) width offset
          (.scalar field) = .ok result ∧
      ShadowRuntimeRel rho result right leftExtra rightExtra := by
  let entry : ScalarField := { width, offset, value := field }
  let fields := entry :: object.scalarFields.filter fun old =>
    old.width != width || old.offset != offset
  let replacement : HeapCell :=
    { cell with object := .ctor { object with scalarFields := fields } }
  rcases related.setCellLeftUnreachable found unreachable replacement with
    ⟨result, effect, next⟩
  refine ⟨result, ?_, next⟩
  have constructor : getConstructor left (.object (.heap location)) =
      .ok (location, cell, object) := by
    simp [getConstructor, getLiveCell, found, live, objectEq,
      Bind.bind, Except.bind]
    rfl
  unfold setScalarField modifyConstructor
  rw [constructor]
  simp only [Bind.bind, Except.bind]
  simpa [entry, fields, replacement] using effect

theorem shadowRuntimeRel_monoRenaming
    (extension : RenamingExtends smaller larger)
    (related : ShadowRuntimeRel smaller left right leftExtra rightExtra)
    (leftMappingFresh : ∀ location, left.nextLocation ≤ location →
      larger.forward location = none)
    (rightMappingFresh : ∀ location, right.nextLocation ≤ location →
      larger.reverse location = none) :
    ShadowRuntimeRel larger left right leftExtra rightExtra := {
  extra := listRel_mono (valueRel_mono extension) related.extra
  globals := listRel_mono (namedValueRel_mono extension) related.globals
  world_eq := related.world_eq
  trace := arrayRel_mono (eventRel_mono extension) related.trace
  heap := heapRel_monoRenaming extension related.heap
  leftMappingFresh
  rightMappingFresh
  leftHeapFresh := related.leftHeapFresh
  rightHeapFresh := related.rightHeapFresh
}

theorem mappingFresh_succ
    (mapping : Location → Option Location)
    (fresh : ∀ location, start ≤ location → mapping location = none) :
    ∀ location, start + 1 ≤ location → mapping location = none := by
  intro location bounded
  exact fresh location (Nat.le_trans (Nat.le_succ start) bounded)

theorem heapFresh_succ
    (fresh : ∀ location, start ≤ location →
      findCell? heap location = none) :
    ∀ location, start + 1 ≤ location →
      findCell? ((start, cell) :: heap) location = none := by
  intro location bounded
  have less : start < location :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self start) bounded
  have different : start ≠ location := Nat.ne_of_lt less
  simpa [findCell?, different] using
    fresh location (Nat.le_trans (Nat.le_succ start) bounded)

theorem renamingExtend_leftMappingFresh
    (fresh : ∀ location, left ≤ location → rho.forward location = none)
    (rightFresh : rho.reverse right = none) :
    ∀ location, left + 1 ≤ location →
      (AddressRenaming.extend rho left right (fresh left (Nat.le_refl left))
        rightFresh).forward location = none := by
  intro location bounded
  have less : left < location :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self left) bounded
  have different : location ≠ left := (Nat.ne_of_lt less).symm
  simp [AddressRenaming.extend, different,
    fresh location (Nat.le_trans (Nat.le_succ left) bounded)]

theorem renamingExtend_rightMappingFresh
    (leftFresh : rho.forward left = none)
    (fresh : ∀ location, right ≤ location → rho.reverse location = none) :
    ∀ location, right + 1 ≤ location →
      (AddressRenaming.extend rho left right leftFresh
        (fresh right (Nat.le_refl right))).reverse location = none := by
  intro location bounded
  have less : right < location :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self right) bounded
  have different : location ≠ right := (Nat.ne_of_lt less).symm
  simp [AddressRenaming.extend, different,
    fresh location (Nat.le_trans (Nat.le_succ right) bounded)]

/-- An allocation whose result is absent from all live roots is unreachable
garbage.  It may advance only the source heap and fresh counter while the
existing runtime relation and address renaming remain valid. -/
theorem ShadowRuntimeRel.allocLeftGarbage
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (object : HeapObject) (persistent : Bool) :
    ShadowRuntimeRel rho (alloc left object persistent).1 right
      leftExtra rightExtra := by
  simp only [alloc]
  exact {
    extra := related.extra
    globals := related.globals
    world_eq := related.world_eq
    trace := related.trace
    heap := by
      simpa [runtimeRoots] using
        heapRel_consLeft_of_forward_unmapped related.heap
          (related.leftMappingFresh left.nextLocation (Nat.le_refl _))
    leftMappingFresh := mappingFresh_succ rho.forward
      related.leftMappingFresh
    rightMappingFresh := related.rightMappingFresh
    leftHeapFresh := heapFresh_succ related.leftHeapFresh
    rightHeapFresh := related.rightHeapFresh
  }

/-- Dead literals are either immediate values or one source-only allocation;
in both cases their evaluation preserves reachable runtime semantics. -/
theorem ShadowRuntimeRel.literalLeftGarbage
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (literalValue : LCNF.LitValue) :
    ShadowRuntimeRel rho (literal left literalValue).1 right
      leftExtra rightExtra := by
  cases literalValue with
  | nat value =>
      by_cases small : value ≤ maxTaggedPayload
      · simpa [literal, small] using related
      · simpa [literal, small] using
          related.allocLeftGarbage (.natural value) false
  | str value =>
      simpa [literal] using related.allocLeftGarbage (.string value) false
  | uint8 value | uint16 value | uint32 value | uint64 value | usize value =>
      simpa [literal] using related

theorem ShadowRuntimeRel.evalLetValueLiteralLeftGarbage
    (related : ShadowRuntimeRel rho state.runtime rightRuntime
      leftExtra rightExtra) :
    ∃ nextRuntime value,
      evalLetValue state {
        fvarId
        binderName
        type
        value := .lit literalValue
      } = .ok (nextRuntime, .value value) ∧
      ShadowRuntimeRel rho nextRuntime rightRuntime leftExtra rightExtra := by
  refine ⟨(literal state.runtime literalValue).1,
    (literal state.runtime literalValue).2, ?_,
    related.literalLeftGarbage literalValue⟩
  rfl

/-- A well-formed dead partial application allocates one unreachable closure
after reading its fixed arguments and target arity. -/
theorem ShadowRuntimeRel.evalLetValuePapLeftGarbage
    (related : ShadowRuntimeRel rho state.runtime rightRuntime
      leftExtra rightExtra)
    (argumentsResult : evalArgs state.env arguments = .ok values)
    (targetFound : state.program.findDecl? name = some target)
    (underapplied : values.size < target.params.size) :
    ∃ nextRuntime value,
      evalLetValue state {
        fvarId
        binderName
        type
        value := .pap name arguments
      } = .ok (nextRuntime, .value value) ∧
      ShadowRuntimeRel rho nextRuntime rightRuntime leftExtra rightExtra := by
  let object : HeapObject := .closure name target.params.size values
  let nextRuntime := (alloc state.runtime object).1
  let value : Value := .object (alloc state.runtime object).2
  refine ⟨nextRuntime, value, ?_, ?_⟩
  · simp only [evalLetValue, argumentsResult, Bind.bind, Except.bind]
    rw [targetFound]
    simp only
    rw [if_neg (Nat.not_le_of_lt underapplied)]
    rfl
  · exact related.allocLeftGarbage object false

/-- Boxing a scalar is immediate when the payload fits the tagged range and
otherwise contributes one unreachable boxed allocation. -/
theorem ShadowRuntimeRel.boxScalarLeftGarbage
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (type : Expr) (scalar : ScalarValue) :
    ∃ nextRuntime value,
      box left type (.scalar scalar) = .ok (nextRuntime, value) ∧
      ShadowRuntimeRel rho nextRuntime right leftExtra rightExtra := by
  let payload := scalar.toUInt64
  by_cases small : payload.toNat ≤ maxTaggedPayload
  · refine ⟨left, .object (.tagged payload), ?_, related⟩
    unfold box
    simp only [Bind.bind, Except.bind]
    rw [if_pos (by simpa [payload] using small)]
    rfl
  · let object : HeapObject := .boxed type (.scalar scalar)
    refine ⟨(alloc left object).1, .object (alloc left object).2, ?_,
      related.allocLeftGarbage object false⟩
    unfold box
    simp only [Bind.bind, Except.bind]
    rw [if_neg (by simpa [payload] using small)]
    rfl

/-- The unboxed-word case has the same immediate/allocation split. -/
theorem ShadowRuntimeRel.boxUSizeLeftGarbage
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (type : Expr) (word : UInt64) :
    ∃ nextRuntime value,
      box left type (.usize word) = .ok (nextRuntime, value) ∧
      ShadowRuntimeRel rho nextRuntime right leftExtra rightExtra := by
  by_cases small : word.toNat ≤ maxTaggedPayload
  · refine ⟨left, .object (.tagged word), ?_, related⟩
    unfold box
    simp only [Bind.bind, Except.bind]
    rw [if_pos small]
    rfl
  · let object : HeapObject := .boxed type (.usize word)
    refine ⟨(alloc left object).1, .object (alloc left object).2, ?_,
      related.allocLeftGarbage object false⟩
    unfold box
    simp only [Bind.bind, Except.bind]
    rw [if_neg small]
    rfl

/-- Related retained allocations may choose different fresh locations.  The
address renaming is extended with that pair, the returned references become
new live roots, and all old runtime components are transported monotonically. -/
theorem ShadowRuntimeRel.allocBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objects : HeapObjectRel rho leftObject rightObject)
    (leftOwned : RootSubset leftObject.ownedValues.toList
      (runtimeRoots left leftExtra))
    (rightOwned : RootSubset rightObject.ownedValues.toList
      (runtimeRoots right rightExtra))
    (persistent : Bool) :
    ∃ larger,
      RenamingExtends rho larger ∧
        ValueRel larger (.object (alloc left leftObject persistent).2)
          (.object (alloc right rightObject persistent).2) ∧
        ShadowRuntimeRel larger
          (alloc left leftObject persistent).1
          (alloc right rightObject persistent).1
          (.object (alloc left leftObject persistent).2 :: leftExtra)
          (.object (alloc right rightObject persistent).2 :: rightExtra) := by
  let leftUnmapped := related.leftMappingFresh left.nextLocation (Nat.le_refl _)
  let rightUnmapped :=
    related.rightMappingFresh right.nextLocation (Nat.le_refl _)
  let larger := AddressRenaming.extend rho left.nextLocation right.nextLocation
    leftUnmapped rightUnmapped
  have extension : RenamingExtends rho larger :=
    renamingExtend_extends leftUnmapped rightUnmapped
  have mapping : larger.forward left.nextLocation = some right.nextLocation :=
    renamingExtend_forward_new leftUnmapped rightUnmapped
  refine ⟨larger, extension, ?_, ?_⟩
  · exact .heap mapping
  · simp only [alloc]
    have cells : HeapCellRel rho
        { object := leftObject
          persistent
          rc := if persistent then 0 else 1 }
        { object := rightObject
          persistent
          rc := if persistent then 0 else 1 } :=
      ⟨rfl, rfl, rfl, objects⟩
    exact {
      extra := .cons (.heap mapping)
        (listRel_mono (valueRel_mono extension) related.extra)
      globals := listRel_mono (namedValueRel_mono extension) related.globals
      world_eq := related.world_eq
      trace := arrayRel_mono (eventRel_mono extension) related.trace
      heap := by
        simpa [runtimeRoots] using
          heapRel_consBoth related.heap leftUnmapped rightUnmapped cells
            leftOwned rightOwned
      leftMappingFresh := renamingExtend_leftMappingFresh
        related.leftMappingFresh rightUnmapped
      rightMappingFresh := renamingExtend_rightMappingFresh leftUnmapped
        related.rightMappingFresh
      leftHeapFresh := heapFresh_succ related.leftHeapFresh
      rightHeapFresh := heapFresh_succ related.rightHeapFresh
    }

/-- A well-formed dead constructor evaluation either produces an immediate
tag without changing the runtime, or allocates source-only unreachable
garbage covered by `allocLeftGarbage`. -/
theorem ShadowRuntimeRel.allocCtorLeftGarbage
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (info : LCNF.CtorInfo) (arguments : Array Value)
    (arity : arguments.size = info.size) :
    ∃ nextRuntime value,
      allocCtor left info arguments = .ok (nextRuntime, value) ∧
      ShadowRuntimeRel rho nextRuntime right leftExtra rightExtra := by
  by_cases empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0
  · refine ⟨left, .object (.tagged (UInt64.ofNat info.cidx)), ?_, related⟩
    simp [allocCtor, arity, empty.1.1, empty.1.2, empty.2]
    rfl
  · let object : ConstructorObject := {
      tag := info.cidx
      objectFields := arguments
      usizeFields := Array.replicate info.usize 0
      scalarFields := []
    }
    refine ⟨(alloc left (.ctor object)).1,
      .object (alloc left (.ctor object)).2, ?_,
      related.allocLeftGarbage (.ctor object) false⟩
    simp [allocCtor, arity, empty, object]
    rfl

/-- A failed reuse token allocates a fresh constructor.  If the produced
value is dead, that allocation is source-only unreachable garbage. -/
theorem ShadowRuntimeRel.reuseNoneLeftGarbage
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (info : LCNF.CtorInfo) (arguments : Array Value)
    (arity : arguments.size = info.size) (updateHeader : Bool) :
    ∃ nextRuntime value,
      reuse left (.reuseToken none) info updateHeader arguments =
          .ok (nextRuntime, value) ∧
      ShadowRuntimeRel rho nextRuntime right leftExtra rightExtra := by
  rcases related.allocCtorLeftGarbage info arguments arity with
    ⟨nextRuntime, value, allocated, next⟩
  exact ⟨nextRuntime, value, by simpa [reuse] using allocated, next⟩

/-- Reusing an existing compiler-owned cell changes only that cell.  When the
cell is outside the published reachable subgraph, the target may stutter. -/
theorem ShadowRuntimeRel.reuseSomeLeftUnreachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (found : findCell? left.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor oldObject)
    (unreachable : ¬Reachable
      left.heap (runtimeRoots left leftExtra) location)
    (info : LCNF.CtorInfo) (arguments : Array Value)
    (arity : arguments.size = info.size) (updateHeader : Bool) :
    ∃ nextRuntime,
      reuse left (.reuseToken (some location)) info updateHeader arguments =
          .ok (nextRuntime, .object (.heap location)) ∧
      ShadowRuntimeRel rho nextRuntime right leftExtra rightExtra := by
  let tag := if updateHeader then info.cidx else oldObject.tag
  let object : ConstructorObject := {
    tag
    objectFields := arguments
    usizeFields := Array.replicate info.usize 0
    scalarFields := [] }
  let replacement : HeapCell :=
    { cell with object := .ctor object }
  rcases related.setCellLeftUnreachable found unreachable replacement with
    ⟨nextRuntime, effect, next⟩
  refine ⟨nextRuntime, ?_, next⟩
  unfold reuse
  simp only [Bind.bind, Except.bind]
  rw [if_neg (by simp [arity])]
  have constructor : getLiveCell left location = .ok cell := by
    simp [getLiveCell, found, live]
  rw [constructor]
  simp only [Bind.bind, Except.bind]
  rw [objectEq]
  change (do
    let runtime ← setCell left location replacement
    pure (runtime, Value.object (ObjectRef.heap location))) = _
  rw [effect]
  rfl

/-- Interpreter-facing form of the constructor result: successful argument
evaluation plus compiler arity well-formedness turns a dead constructor let
into one source step that preserves the reachable runtime relation. -/
theorem ShadowRuntimeRel.evalLetValueCtorLeftGarbage
    (related : ShadowRuntimeRel rho state.runtime rightRuntime
      leftExtra rightExtra)
    (argumentsResult : evalArgs state.env arguments = .ok values)
    (arity : values.size = info.size) :
    ∃ nextRuntime value,
      evalLetValue state {
        fvarId
        binderName
        type
        value := .ctor info arguments
      } = .ok (nextRuntime, .value value) ∧
      ShadowRuntimeRel rho nextRuntime rightRuntime leftExtra rightExtra := by
  rcases related.allocCtorLeftGarbage info values arity with
    ⟨nextRuntime, value, allocated, nextRelated⟩
  refine ⟨nextRuntime, value, ?_, nextRelated⟩
  simp only [evalLetValue, argumentsResult, Bind.bind, Except.bind]
  rw [allocated]
  rfl

theorem ShadowRuntimeRel.evalLetValueReuseNoneLeftGarbage
    (related : ShadowRuntimeRel rho state.runtime rightRuntime
      leftExtra rightExtra)
    (tokenResult : lookupValue state.env token = .ok (.reuseToken none))
    (argumentsResult : evalArgs state.env arguments = .ok values)
    (arity : values.size = info.size) :
    ∃ nextRuntime value,
      evalLetValue state {
        fvarId
        binderName
        type
        value := .reuse token info updateHeader arguments
      } = .ok (nextRuntime, .value value) ∧
      ShadowRuntimeRel rho nextRuntime rightRuntime leftExtra rightExtra := by
  rcases related.reuseNoneLeftGarbage info values arity updateHeader with
    ⟨nextRuntime, value, reused, next⟩
  refine ⟨nextRuntime, value, ?_, next⟩
  simp only [evalLetValue, tokenResult, Bind.bind, Except.bind,
    argumentsResult]
  rw [reused]
  rfl

theorem ShadowRuntimeRel.evalLetValueReuseSomeLeftUnreachable
    (related : ShadowRuntimeRel rho state.runtime rightRuntime
      leftExtra rightExtra)
    (tokenResult : lookupValue state.env token =
      .ok (.reuseToken (some location)))
    (argumentsResult : evalArgs state.env arguments = .ok values)
    (found : findCell? state.runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .ctor oldObject)
    (unreachable : ¬Reachable state.runtime.heap
      (runtimeRoots state.runtime leftExtra) location)
    (arity : values.size = info.size) :
    ∃ nextRuntime,
      evalLetValue state {
        fvarId
        binderName
        type
        value := .reuse token info updateHeader arguments
      } = .ok (nextRuntime, .value (.object (.heap location))) ∧
      ShadowRuntimeRel rho nextRuntime rightRuntime leftExtra rightExtra := by
  rcases related.reuseSomeLeftUnreachable found live objectEq unreachable
      info values arity updateHeader with
    ⟨nextRuntime, reused, next⟩
  refine ⟨nextRuntime, ?_, next⟩
  simp only [evalLetValue, tokenResult, Bind.bind, Except.bind,
    argumentsResult]
  rw [reused]
  rfl

theorem traceRoots_subset_runtimeRoots
    (runtime : RuntimeState) (extra : List Value) :
    RootSubset (traceRoots runtime.trace) (runtimeRoots runtime extra) := by
  intro value member
  simp [runtimeRoots, member]

/-- If the terminal outcome roots occur among the live extra roots, the full
observation roots occur among the runtime relation's canonical roots. -/
theorem observationRoots_subset_runtimeRoots
    (state : MachineState) (outcome : Outcome) (extra : List Value)
    (outcomeSubset : RootSubset (outcomeRoots outcome) extra) :
    RootSubset
      (Observation.roots (observe state outcome))
      (runtimeRoots state.runtime extra) := by
  intro value member
  cases outcome with
  | returned result =>
      simp only [Observation.roots, observe, List.mem_append,
        List.mem_singleton] at member
      cases member with
      | inl returned =>
          have live : value ∈ extra :=
            outcomeSubset value (by simp [outcomeRoots, returned])
          simp [runtimeRoots, live]
      | inr traced =>
          exact traceRoots_subset_runtimeRoots state.runtime extra value traced
  | fault fault =>
      simp only [Observation.roots, observe, List.nil_append] at member
      exact traceRoots_subset_runtimeRoots state.runtime extra value member

/-- The runtime relation discharges the shared reachable-observation contract
at a terminal boundary. -/
theorem ShadowRuntimeRel.observationRel
    (related : ShadowRuntimeRel rho left.runtime right.runtime
      leftExtra rightExtra)
    (outcomes : OutcomeRel rho leftOutcome rightOutcome)
    (leftOutcomeSubset : RootSubset (outcomeRoots leftOutcome) leftExtra)
    (rightOutcomeSubset : RootSubset (outcomeRoots rightOutcome) rightExtra) :
    ObservationRel
      (observe left leftOutcome)
      (observe right rightOutcome) := by
  refine ⟨rho, outcomes, related.world_eq, related.trace, ?_⟩
  exact heapRel_monoRoots related.heap
    (observationRoots_subset_runtimeRoots left leftOutcome leftExtra
      leftOutcomeSubset)
    (observationRoots_subset_runtimeRoots right rightOutcome rightExtra
      rightOutcomeSubset)

/-- Initial runtimes are related by the empty address renaming. -/
theorem emptyRuntime_shadowRelated :
    ShadowRuntimeRel emptyAddressRenaming ({} : RuntimeState)
      ({} : RuntimeState) [] [] := by
  refine {
    extra := .nil
    globals := .nil
    world_eq := rfl
    trace := .nil
    heap := ?_
    leftMappingFresh := by simp [emptyAddressRenaming]
    rightMappingFresh := by simp [emptyAddressRenaming]
    leftHeapFresh := by simp [findCell?]
    rightHeapFresh := by simp [findCell?]
  }
  constructor
  · intro location reachable
    exact (not_reachable_from_empty reachable).elim
  · intro location reachable
    exact (not_reachable_from_empty reachable).elim

theorem valueRel_empty_noHeapLeft
    (related : ValueRel emptyAddressRenaming left right) :
    left ≠ .object (.heap location) := by
  intro same
  subst left
  cases related with
  | heap mapped => simp [emptyAddressRenaming] at mapped

theorem valueRel_empty_noHeapRight
    (related : ValueRel emptyAddressRenaming left right) :
    right ≠ .object (.heap location) := by
  intro same
  subst right
  cases related with
  | heap mapped => simp [emptyAddressRenaming] at mapped

theorem listRel_empty_noHeapLeft
    (related : ListRel (ValueRel emptyAddressRenaming) left right) :
    .object (.heap location) ∉ left := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      simp only [List.mem_cons, not_or]
      exact ⟨(valueRel_empty_noHeapLeft head).symm, ih⟩

theorem listRel_empty_noHeapRight
    (related : ListRel (ValueRel emptyAddressRenaming) left right) :
    .object (.heap location) ∉ right := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      simp only [List.mem_cons, not_or]
      exact ⟨(valueRel_empty_noHeapRight head).symm, ih⟩

theorem not_reachable_from_emptyHeap
    (noHeapRoot : ∀ candidate,
      Value.object (.heap candidate) ∉ roots)
    (reachable : Reachable [] roots location) : False := by
  cases reachable with
  | root member => exact noHeapRoot _ member
  | child parentReachable cellFound member reference =>
      simp [findCell?] at cellFound

/-- Empty runtimes support arbitrary pointwise-related entry roots.  Under
the empty renaming such roots cannot contain heap locations, so the empty
heaps have no reachable cells to match. -/
theorem emptyRuntime_shadowRelated_of_roots
    (roots : ListRel (ValueRel emptyAddressRenaming)
      leftRoots rightRoots) :
    ShadowRuntimeRel emptyAddressRenaming ({} : RuntimeState)
      ({} : RuntimeState) leftRoots rightRoots := by
  refine {
    extra := roots
    globals := .nil
    world_eq := rfl
    trace := .nil
    heap := ?_
    leftMappingFresh := by simp [emptyAddressRenaming]
    rightMappingFresh := by simp [emptyAddressRenaming]
    leftHeapFresh := by simp [findCell?]
    rightHeapFresh := by simp [findCell?]
  }
  constructor
  · intro location reachable
    have reduced : Reachable [] leftRoots location := by
      simpa [runtimeRoots, traceRoots] using reachable
    exact (not_reachable_from_emptyHeap
      (fun candidate => listRel_empty_noHeapLeft roots) reduced).elim
  · intro location reachable
    have reduced : Reachable [] rightRoots location := by
      simpa [runtimeRoots, traceRoots] using reachable
    exact (not_reachable_from_emptyHeap
      (fun candidate => listRel_empty_noHeapRight roots) reduced).elim

end Fir.LeanIR.Passes.ElimDead
