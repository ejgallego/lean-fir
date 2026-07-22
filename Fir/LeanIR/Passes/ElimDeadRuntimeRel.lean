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

/-- Environments agree relationally on precisely the variables retained by
the backwards liveness graph. -/
def EnvRelOn (rho : AddressRenaming) (used : UsedLocals)
    (left right : Env) : Prop :=
  ∀ fvarId, used.contains fvarId = true →
    OptionalRel (ValueRel rho) (lookup left fvarId) (lookup right fvarId)

/-- Canonical runtime roots contributed by the live portion of an
environment.  `filterMap` drops malformed/missing live lookups symmetrically. -/
def envRootsOn (used : UsedLocals) (env : Env) : List Value :=
  used.toList.filterMap (lookup env)

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

theorem ShadowRuntimeRel.roots
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra) :
    ListRel (ValueRel rho)
      (runtimeRoots left leftExtra) (runtimeRoots right rightExtra) := by
  unfold runtimeRoots
  exact listRel_append
    (listRel_append related.extra (globalsRoots_related related.globals))
    (traceRoots_related related.trace)

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
  refine ⟨larger, ?_, ?_⟩
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
