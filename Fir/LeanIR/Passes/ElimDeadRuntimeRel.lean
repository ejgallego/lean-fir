import Fir.LeanIR.Passes.ElimDead

namespace Fir.LeanIR.Passes.ElimDead

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure

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

theorem not_reachable_from_empty
    (reachable : Reachable heap [] location) : False := by
  induction reachable with
  | root member => simp at member
  | child parentReachable cellFound member reference ih => exact ih

def traceRoots (trace : Array ExternalEvent) : List Value :=
  trace.toList.flatMap fun event => event.result :: event.args.toList

def outcomeRoots : Outcome → List Value
  | .returned value => [value]
  | .fault _ => []

/-- `extra` contains control-, environment-, and frame-specific roots.  The
runtime contributes globals and the already observable external trace. -/
def runtimeRoots (runtime : RuntimeState) (extra : List Value) : List Value :=
  extra ++ runtime.globals.map Prod.snd ++ traceRoots runtime.trace

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

end Fir.LeanIR.Passes.ElimDead
