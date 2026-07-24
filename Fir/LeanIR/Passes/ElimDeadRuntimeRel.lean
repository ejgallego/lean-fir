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

/-- Pointwise relation for computations that may fail with differently
represented but semantically related errors. -/
inductive ExceptRel (errorRel : ε₁ → ε₂ → Prop)
    (valueRel : α₁ → α₂ → Prop) :
    Except ε₁ α₁ → Except ε₂ α₂ → Prop where
  | error (related : errorRel left right) :
      ExceptRel errorRel valueRel (.error left) (.error right)
  | ok (related : valueRel left right) :
      ExceptRel errorRel valueRel (.ok left) (.ok right)

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

/-- Number of live cells whose metadata still needs persistence promotion.
This is the semantic termination measure for `markPersistentLocationFuel`:
an effective visit marks its parent before recursively visiting children. -/
def unpersistedLiveCount : Heap → Nat
  | [] => 0
  | (_, cell) :: rest =>
      (if cell.live && !cell.persistent then 1 else 0) +
        unpersistedLiveCount rest

theorem unpersistedLiveCount_le_length (heap : Heap) :
    unpersistedLiveCount heap ≤ heap.length := by
  induction heap with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      obtain ⟨location, cell⟩ := entry
      simp only [unpersistedLiveCount, List.length_cons]
      split <;> omega

/-- Promoting one ordinary live cell removes exactly one unit from the
persistence termination measure. -/
theorem unpersistedLiveCount_replace_persistent
    (found : findCell? heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (replaced : replaceCell heap location
      { cell with rc := 0, persistent := true } = some after) :
    unpersistedLiveCount after + 1 = unpersistedLiveCount heap := by
  induction heap generalizing after with
  | nil => simp [findCell?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, current⟩ := entry
      by_cases here : candidate = location
      · subst candidate
        simp [findCell?] at found
        subst current
        simp [replaceCell] at replaced
        subst after
        simp [unpersistedLiveCount, live, ordinary]
        omega
      · have tailFound : findCell? rest location = some cell := by
          simpa [findCell?, here] using found
        cases tailReplaced : replaceCell rest location
            { cell with rc := 0, persistent := true } with
        | none => simp [replaceCell, here, tailReplaced] at replaced
        | some tailAfter =>
            have afterEq : after = (candidate, current) :: tailAfter := by
              simpa [replaceCell, here, tailReplaced] using replaced.symm
            subst after
            have tailCount := ih tailFound tailReplaced
            simp only [unpersistedLiveCount]
            omega

/-- Recursive persistence never creates a new unpersisted live cell. -/
theorem unpersistedLiveCount_markPersistentLocationFuel_le
    (fuel : Nat) (heap : Heap) (location : Location) :
    unpersistedLiveCount
        (markPersistentLocationFuel fuel heap location) ≤
      unpersistedLiveCount heap := by
  induction fuel generalizing heap location with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [markPersistentLocationFuel]
      cases found : findCell? heap location with
      | none => simp
      | some cell =>
          by_cases skip : !cell.live || cell.persistent
          · simp [skip]
          · have live : cell.live = true := by
              cases liveEq : cell.live <;> simp_all
            have ordinary : cell.persistent = false := by
              cases persistentEq : cell.persistent <;> simp_all
            simp only [skip, Bool.false_eq_true, if_false]
            obtain ⟨after, post⟩ :=
              replaceCell_spec_of_find heap location cell
                { cell with rc := 0, persistent := true } found
            rw [post.replaced]
            have parentDrop :=
              unpersistedLiveCount_replace_persistent found live ordinary
                post.replaced
            have foldLe (values : Array Value) (start : Heap) :
                unpersistedLiveCount
                    (values.foldl (init := start) fun next value =>
                      match value with
                      | .object (.heap child) =>
                          markPersistentLocationFuel fuel next child
                      | _ => next) ≤
                  unpersistedLiveCount start := by
              rw [← Array.foldl_toList]
              generalize values.toList = items
              induction items generalizing start with
              | nil => exact Nat.le_refl _
              | cons value items itemsIH =>
                  simp only [List.foldl]
                  apply Nat.le_trans (itemsIH _)
                  cases value with
                  | object reference =>
                      cases reference with
                      | tagged payload => exact Nat.le_refl _
                      | heap child => exact ih start child
                  | usize | scalar | erased | reuseToken =>
                      exact Nat.le_refl _
            exact Nat.le_trans
              (foldLe cell.object.ownedValues after) (by omega)

/-- A heap update preserves the ownership graph when every lookup keeps the
same optional heap object; reference-count and persistence metadata may
change. -/
def HeapOwnershipFrame (before after : Heap) : Prop :=
  ∀ location,
    (findCell? before location).map HeapCell.object =
      (findCell? after location).map HeapCell.object

namespace HeapOwnershipFrame

theorem refl (heap : Heap) : HeapOwnershipFrame heap heap := by
  intro location
  rfl

theorem trans
    (first : HeapOwnershipFrame before middle)
    (second : HeapOwnershipFrame middle after) :
    HeapOwnershipFrame before after := by
  intro location
  exact (first location).trans (second location)

theorem symm
    (frame : HeapOwnershipFrame before after) :
    HeapOwnershipFrame after before := by
  intro location
  exact (frame location).symm

theorem reachable
    (frame : HeapOwnershipFrame before after)
    (reachable : Reachable before roots location) :
    Reachable after roots location := by
  induction reachable with
  | root member => exact .root member
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      have objectRead := frame parent
      rw [cellFound] at objectRead
      cases afterFound : findCell? after parent with
      | none => simp [afterFound] at objectRead
      | some afterCell =>
          simp only [afterFound, Option.map_some, Option.some.injEq] at objectRead
          exact .child ih afterFound
            (by simpa [← objectRead] using member) reference

theorem find_none
    (frame : HeapOwnershipFrame before after)
    (found : findCell? before location = none) :
    findCell? after location = none := by
  have objectRead := frame location
  rw [found] at objectRead
  cases afterFound : findCell? after location with
  | none => rfl
  | some cell =>
      simp [afterFound] at objectRead

end HeapOwnershipFrame

/-- Replacing one cell while retaining its heap object preserves the complete
ownership graph. -/
theorem heapOwnershipFrame_replace
    (beforeFound : findCell? before modified = some beforeCell)
    (afterFound : findCell? after modified = some afterCell)
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (objectEq : afterCell.object = beforeCell.object) :
    HeapOwnershipFrame before after := by
  intro location
  by_cases same : location = modified
  · subst location
    simp [beforeFound, afterFound, objectEq]
  · rw [frame location same]

/-- Every fuel-bounded persistence traversal changes metadata only; its
ownership graph is exactly the input graph. -/
theorem heapOwnershipFrame_markPersistentLocationFuel
    (fuel : Nat) (heap : Heap) (location : Location) :
    HeapOwnershipFrame heap
      (markPersistentLocationFuel fuel heap location) := by
  induction fuel generalizing heap location with
  | zero => exact .refl heap
  | succ fuel ih =>
      rw [markPersistentLocationFuel]
      cases found : findCell? heap location with
      | none => exact .refl heap
      | some cell =>
          by_cases skip : !cell.live || cell.persistent
          · simp [skip]
            exact .refl heap
          · simp only [skip, Bool.false_eq_true, if_false]
            obtain ⟨after, post⟩ :=
              replaceCell_spec_of_find heap location cell
                { cell with rc := 0, persistent := true } found
            rw [post.replaced]
            have parentFrame : HeapOwnershipFrame heap after :=
              heapOwnershipFrame_replace found post.target post.frame rfl
            have foldFrame (values : Array Value) (start : Heap) :
                HeapOwnershipFrame start
                  (values.foldl (init := start) fun next value =>
                    match value with
                    | .object (.heap child) =>
                        markPersistentLocationFuel fuel next child
                    | _ => next) := by
              rw [← Array.foldl_toList]
              generalize values.toList = items
              induction items generalizing start with
              | nil => exact .refl start
              | cons value items itemsIH =>
                  simp only [List.foldl]
                  have headFrame : HeapOwnershipFrame start
                      (match value with
                      | .object (.heap child) =>
                          markPersistentLocationFuel fuel start child
                      | _ => start) := by
                    cases value with
                    | object reference =>
                        cases reference with
                        | tagged payload => exact .refl start
                        | heap child => exact ih start child
                    | usize | scalar | erased | reuseToken =>
                        exact .refl start
                  exact headFrame.trans (itemsIH _)
            exact parentFrame.trans
              (foldFrame cell.object.ownedValues after)

/-- Related reachable locations remain related after recursive persistence at
one common sufficient fuel.  The two traversals follow related ownership
arrays; the live-nonpersistent count guarantees that every effective child
visit has enough remaining fuel. -/
theorem heapRel_markPersistentLocationFuelBoth
    (related : HeapRel rho left right leftRoots rightRoots)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable : Reachable left leftRoots leftLocation)
    (rightReachable : Reachable right rightRoots rightLocation)
    (leftBound : unpersistedLiveCount left ≤ fuel)
    (rightBound : unpersistedLiveCount right ≤ fuel) :
    HeapRel rho
      (markPersistentLocationFuel fuel left leftLocation)
      (markPersistentLocationFuel fuel right rightLocation)
      leftRoots rightRoots := by
  induction fuel generalizing left right leftLocation rightLocation with
  | zero =>
      simpa [markPersistentLocationFuel] using related
  | succ fuel ih =>
      rcases related.1 leftLocation leftReachable with
        ⟨mapped, leftCell, rightCell, mappedEq, leftFound, rightFound,
          cells⟩
      have mappedSame : mapped = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mapped
      rcases cells with ⟨rcEq, persistentEq, liveEq, objects⟩
      cases leftLive : leftCell.live with
      | false =>
          have rightLive : rightCell.live = false := by
            rw [← liveEq]
            exact leftLive
          simpa [markPersistentLocationFuel, leftFound, rightFound,
            leftLive, rightLive] using related
      | true =>
          have rightLive : rightCell.live = true := by
            rw [← liveEq]
            exact leftLive
          cases leftPersistent : leftCell.persistent with
          | true =>
              have rightPersistent : rightCell.persistent = true := by
                rw [← persistentEq]
                exact leftPersistent
              simpa [markPersistentLocationFuel, leftFound, rightFound,
                leftLive, rightLive, leftPersistent, rightPersistent] using
                related
          | false =>
              have rightPersistent : rightCell.persistent = false := by
                rw [← persistentEq]
                exact leftPersistent
              let leftReplacement : HeapCell :=
                { leftCell with rc := 0, persistent := true }
              let rightReplacement : HeapCell :=
                { rightCell with rc := 0, persistent := true }
              obtain ⟨leftAfter, leftPost⟩ :=
                replaceCell_spec_of_find left leftLocation leftCell
                  leftReplacement leftFound
              obtain ⟨rightAfter, rightPost⟩ :=
                replaceCell_spec_of_find right rightLocation rightCell
                  rightReplacement rightFound
              have replacements :
                  HeapCellRel rho leftReplacement rightReplacement := by
                exact ⟨rfl, rfl, liveEq, objects⟩
              have leftParentFrame : HeapOwnershipFrame left leftAfter :=
                heapOwnershipFrame_replace leftFound leftPost.target
                  leftPost.frame rfl
              have rightParentFrame : HeapOwnershipFrame right rightAfter :=
                heapOwnershipFrame_replace rightFound rightPost.target
                  rightPost.frame rfl
              have parentRelated : HeapRel rho leftAfter rightAfter
                  leftRoots rightRoots := by
                constructor
                · intro location afterReachable
                  have beforeReachable :=
                    leftParentFrame.symm.reachable afterReachable
                  rcases related.1 location beforeReachable with
                    ⟨target, sourceCell, targetCell, targetMapping,
                      sourceFound, targetFound, oldCells⟩
                  by_cases same : location = leftLocation
                  · subst location
                    have targetSame : target = rightLocation := by
                      rw [mapping] at targetMapping
                      exact (Option.some.inj targetMapping).symm
                    subst target
                    exact ⟨rightLocation, leftReplacement, rightReplacement,
                      mapping, leftPost.target, rightPost.target, replacements⟩
                  · have targetDifferent : target ≠ rightLocation := by
                      intro targetSame
                      subst target
                      have oldInverse := rho.leftInverse targetMapping
                      have newInverse := rho.leftInverse mapping
                      rw [newInverse] at oldInverse
                      exact same (Option.some.inj oldInverse).symm
                    exact ⟨target, sourceCell, targetCell, targetMapping,
                      by simpa [leftPost.frame location same] using sourceFound,
                      by simpa [rightPost.frame target targetDifferent] using
                        targetFound,
                      oldCells⟩
                · intro location afterReachable
                  have beforeReachable :=
                    rightParentFrame.symm.reachable afterReachable
                  rcases related.2 location beforeReachable with
                    ⟨source, targetCell, sourceCell, sourceMapping,
                      targetFound, sourceFound, oldCells⟩
                  have reverseMapping := rho.leftInverse mapping
                  by_cases same : location = rightLocation
                  · subst location
                    have sourceSame : source = leftLocation := by
                      rw [reverseMapping] at sourceMapping
                      exact (Option.some.inj sourceMapping).symm
                    subst source
                    exact ⟨leftLocation, rightReplacement, leftReplacement,
                      reverseMapping, rightPost.target, leftPost.target,
                      replacements⟩
                  · have sourceDifferent : source ≠ leftLocation := by
                      intro sourceSame
                      subst source
                      have oldForward := rho.rightInverse sourceMapping
                      rw [mapping] at oldForward
                      exact same (Option.some.inj oldForward).symm
                    exact ⟨source, targetCell, sourceCell, sourceMapping,
                      by simpa [rightPost.frame location same] using targetFound,
                      by simpa [leftPost.frame source sourceDifferent] using
                        sourceFound,
                      oldCells⟩
              have leftParentReachable :
                  Reachable leftAfter leftRoots leftLocation :=
                leftParentFrame.reachable leftReachable
              have rightParentReachable :
                  Reachable rightAfter rightRoots rightLocation :=
                rightParentFrame.reachable rightReachable
              have leftAfterBound :
                  unpersistedLiveCount leftAfter ≤ fuel := by
                have dropped :=
                  unpersistedLiveCount_replace_persistent leftFound leftLive
                    leftPersistent leftPost.replaced
                omega
              have rightAfterBound :
                  unpersistedLiveCount rightAfter ≤ fuel := by
                have dropped :=
                  unpersistedLiveCount_replace_persistent rightFound rightLive
                    rightPersistent rightPost.replaced
                omega
              have foldRelated :
                  ∀ {leftItems rightItems},
                    ListRel (ValueRel rho) leftItems rightItems →
                    (∀ value, value ∈ leftItems →
                      value ∈ leftCell.object.ownedValues.toList) →
                    (∀ value, value ∈ rightItems →
                      value ∈ rightCell.object.ownedValues.toList) →
                    ∀ {leftCurrent rightCurrent},
                      HeapRel rho leftCurrent rightCurrent
                          leftRoots rightRoots →
                      HeapOwnershipFrame leftAfter leftCurrent →
                      HeapOwnershipFrame rightAfter rightCurrent →
                      unpersistedLiveCount leftCurrent ≤ fuel →
                      unpersistedLiveCount rightCurrent ≤ fuel →
                      HeapRel rho
                        (leftItems.foldl (init := leftCurrent)
                          fun next value =>
                            match value with
                            | .object (.heap child) =>
                                markPersistentLocationFuel fuel next child
                            | _ => next)
                        (rightItems.foldl (init := rightCurrent)
                          fun next value =>
                            match value with
                            | .object (.heap child) =>
                                markPersistentLocationFuel fuel next child
                            | _ => next)
                        leftRoots rightRoots := by
                intro leftItems rightItems values leftMember rightMember
                  leftCurrent rightCurrent currentRelated leftFrame rightFrame
                  leftCurrentBound rightCurrentBound
                induction values generalizing leftCurrent rightCurrent with
                | nil => exact currentRelated
                | cons head tail tailIH =>
                    rename_i leftHead rightHead leftTail rightTail
                    have leftHeadMember :
                        leftHead ∈ leftCell.object.ownedValues.toList :=
                      leftMember leftHead List.mem_cons_self
                    have rightHeadMember :
                        rightHead ∈ rightCell.object.ownedValues.toList :=
                      rightMember rightHead List.mem_cons_self
                    have leftTailMember :
                        ∀ value, value ∈ leftTail →
                          value ∈ leftCell.object.ownedValues.toList := by
                      intro value member
                      exact leftMember value (List.mem_cons_of_mem _ member)
                    have rightTailMember :
                        ∀ value, value ∈ rightTail →
                          value ∈ rightCell.object.ownedValues.toList := by
                      intro value member
                      exact rightMember value (List.mem_cons_of_mem _ member)
                    cases head with
                    | @heap leftChildLocation rightChildLocation headMapping =>
                        have leftBaseChild :
                            Reachable leftAfter leftRoots leftChildLocation :=
                          .child leftParentReachable leftPost.target
                            leftHeadMember rfl
                        have rightBaseChild :
                            Reachable rightAfter rightRoots rightChildLocation :=
                          .child rightParentReachable rightPost.target
                            rightHeadMember rfl
                        have leftChild := leftFrame.reachable leftBaseChild
                        have rightChild := rightFrame.reachable rightBaseChild
                        have childRelated :=
                          ih currentRelated headMapping leftChild rightChild
                            leftCurrentBound rightCurrentBound
                        have leftChildFrame :=
                          heapOwnershipFrame_markPersistentLocationFuel fuel
                            leftCurrent leftChildLocation
                        have rightChildFrame :=
                          heapOwnershipFrame_markPersistentLocationFuel fuel
                            rightCurrent rightChildLocation
                        have leftChildBound :
                            unpersistedLiveCount
                                (markPersistentLocationFuel fuel leftCurrent
                                  leftChildLocation) ≤
                              fuel :=
                          Nat.le_trans
                            (unpersistedLiveCount_markPersistentLocationFuel_le
                              fuel leftCurrent leftChildLocation)
                            leftCurrentBound
                        have rightChildBound :
                            unpersistedLiveCount
                                (markPersistentLocationFuel fuel rightCurrent
                                  rightChildLocation) ≤
                              fuel :=
                          Nat.le_trans
                            (unpersistedLiveCount_markPersistentLocationFuel_le
                              fuel rightCurrent rightChildLocation)
                            rightCurrentBound
                        simpa only [List.foldl] using
                          tailIH leftTailMember rightTailMember childRelated
                            (leftFrame.trans leftChildFrame)
                            (rightFrame.trans rightChildFrame)
                            leftChildBound rightChildBound
                    | tagged payload | usize payload | scalar payload
                    | erased | reuseNone | reuseSome headMapping =>
                        simpa only [List.foldl] using
                          tailIH leftTailMember rightTailMember currentRelated
                            leftFrame rightFrame leftCurrentBound
                            rightCurrentBound
              simp only [markPersistentLocationFuel, leftFound, rightFound,
                leftLive, rightLive, leftPersistent, rightPersistent,
                Bool.not_true, Bool.false_or, Bool.false_eq_true, if_false]
              have leftReplaced : replaceCell left leftLocation
                  { object := leftCell.object, rc := 0, persistent := true } =
                    some leftAfter := by
                simpa [leftReplacement, leftLive] using leftPost.replaced
              have rightReplaced : replaceCell right rightLocation
                  { object := rightCell.object, rc := 0, persistent := true } =
                    some rightAfter := by
                simpa [rightReplacement, rightLive] using rightPost.replaced
              rw [leftReplaced, rightReplaced]
              simp only
              rw [← Array.foldl_toList, ← Array.foldl_toList]
              have ownedValuesOf :
                  ∀ {leftObject rightObject},
                    HeapObjectRel rho leftObject rightObject →
                    ListRel (ValueRel rho)
                      leftObject.ownedValues.toList
                      rightObject.ownedValues.toList := by
                intro leftObject rightObject objectRelated
                cases objectRelated with
                | ctor tag fields usizes scalars => exact fields
                | closure fixed => exact fixed
                | boxed value => exact .cons value .nil
                | string value | natural value | integer value
                | byteArray value | «opaque» value => exact .nil
              have ownedValues := ownedValuesOf objects
              exact foldRelated ownedValues
                (fun _ member => member) (fun _ member => member)
                parentRelated (.refl leftAfter) (.refl rightAfter)
                leftAfterBound rightAfterBound

/-- If no live cell still needs promotion, persistence is an all-fuel no-op. -/
theorem markPersistentLocationFuel_eq_of_count_zero
    (empty : unpersistedLiveCount heap = 0)
    (fuel : Nat) (location : Location) :
    markPersistentLocationFuel fuel heap location = heap := by
  induction fuel generalizing heap location with
  | zero => rfl
  | succ fuel ih =>
      rw [markPersistentLocationFuel]
      cases found : findCell? heap location with
      | none => rfl
      | some cell =>
          by_cases skip : !cell.live || cell.persistent
          · simp [skip]
          · have live : cell.live = true := by
              cases liveEq : cell.live <;> simp_all
            have ordinary : cell.persistent = false := by
              cases persistentEq : cell.persistent <;> simp_all
            obtain ⟨after, post⟩ :=
              replaceCell_spec_of_find heap location cell
                { cell with rc := 0, persistent := true } found
            have dropped :=
              unpersistedLiveCount_replace_persistent found live ordinary
                post.replaced
            omega

/-- Once the fuel covers every live nonpersistent cell, increasing it cannot
change the persistence result. -/
theorem markPersistentLocationFuel_eq_of_sufficient
    (bound : unpersistedLiveCount heap ≤ fuel)
    (fuelLe : fuel ≤ more) :
    markPersistentLocationFuel fuel heap location =
      markPersistentLocationFuel more heap location := by
  induction fuel generalizing more heap location with
  | zero =>
      have empty : unpersistedLiveCount heap = 0 := by omega
      rw [markPersistentLocationFuel_eq_of_count_zero empty more location]
      rfl
  | succ fuel ih =>
      cases more with
      | zero => omega
      | succ more =>
          have fuelLe' : fuel ≤ more := by omega
          rw [markPersistentLocationFuel, markPersistentLocationFuel]
          cases found : findCell? heap location with
          | none => rfl
          | some cell =>
              by_cases skip : !cell.live || cell.persistent
              · simp [skip]
              · have live : cell.live = true := by
                  cases liveEq : cell.live <;> simp_all
                have ordinary : cell.persistent = false := by
                  cases persistentEq : cell.persistent <;> simp_all
                simp only [skip, Bool.false_eq_true, if_false]
                obtain ⟨after, post⟩ :=
                  replaceCell_spec_of_find heap location cell
                    { cell with rc := 0, persistent := true } found
                rw [post.replaced]
                have afterBound :
                    unpersistedLiveCount after ≤ fuel := by
                  have dropped :=
                    unpersistedLiveCount_replace_persistent found live ordinary
                      post.replaced
                  omega
                have foldEq (items : List Value) (start : Heap)
                    (startBound : unpersistedLiveCount start ≤ fuel) :
                    items.foldl (init := start) (fun next value =>
                      match value with
                      | .object (.heap child) =>
                          markPersistentLocationFuel fuel next child
                      | _ => next) =
                    items.foldl (init := start) (fun next value =>
                      match value with
                      | .object (.heap child) =>
                          markPersistentLocationFuel more next child
                      | _ => next) := by
                  induction items generalizing start with
                  | nil => rfl
                  | cons value items itemsIH =>
                      simp only [List.foldl]
                      cases value with
                      | object reference =>
                          cases reference with
                          | tagged payload => exact itemsIH start startBound
                          | heap child =>
                              change
                                List.foldl (fun next value =>
                                  match value with
                                  | .object (.heap child) =>
                                      markPersistentLocationFuel fuel next child
                                  | _ => next)
                                    (markPersistentLocationFuel fuel start child)
                                    items =
                                List.foldl (fun next value =>
                                  match value with
                                  | .object (.heap child) =>
                                      markPersistentLocationFuel more next child
                                  | _ => next)
                                    (markPersistentLocationFuel more start child)
                                    items
                              have headEq := ih startBound fuelLe'
                                (location := child)
                              rw [headEq]
                              exact itemsIH _ (Nat.le_trans
                                (unpersistedLiveCount_markPersistentLocationFuel_le
                                  more start child)
                                startBound)
                      | usize | scalar | erased | reuseToken =>
                          exact itemsIH start startBound
                change
                  cell.object.ownedValues.foldl (init := after)
                      (fun next value =>
                        match value with
                        | .object (.heap child) =>
                            markPersistentLocationFuel fuel next child
                        | _ => next) =
                    cell.object.ownedValues.foldl (init := after)
                      (fun next value =>
                        match value with
                        | .object (.heap child) =>
                            markPersistentLocationFuel more next child
                        | _ => next)
                simpa only [Array.foldl_toList] using
                  foldEq cell.object.ownedValues.toList after afterBound

/-- The public heap-length fuel choices may differ because unreachable
garbage differs.  Raising both to a common sufficient bound and using
fuel stability recovers the paired reachable-heap relation. -/
theorem heapRel_markPersistentBoth
    (related : HeapRel rho left right leftRoots rightRoots)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable : Reachable left leftRoots leftLocation)
    (rightReachable : Reachable right rightRoots rightLocation) :
    HeapRel rho
      (markPersistentLocationFuel (left.length + 1) left leftLocation)
      (markPersistentLocationFuel (right.length + 1) right rightLocation)
      leftRoots rightRoots := by
  let commonFuel := max left.length right.length + 1
  have leftCount : unpersistedLiveCount left ≤ left.length + 1 :=
    Nat.le_trans (unpersistedLiveCount_le_length left) (Nat.le_succ _)
  have rightCount : unpersistedLiveCount right ≤ right.length + 1 :=
    Nat.le_trans (unpersistedLiveCount_le_length right) (Nat.le_succ _)
  have leftFuelLe : left.length + 1 ≤ commonFuel := by
    dsimp [commonFuel]
    omega
  have rightFuelLe : right.length + 1 ≤ commonFuel := by
    dsimp [commonFuel]
    omega
  have leftEq := markPersistentLocationFuel_eq_of_sufficient
    (location := leftLocation) leftCount leftFuelLe
  have rightEq := markPersistentLocationFuel_eq_of_sufficient
    (location := rightLocation) rightCount rightFuelLe
  rw [leftEq, rightEq]
  exact heapRel_markPersistentLocationFuelBoth related mapping
    leftReachable rightReachable
    (Nat.le_trans leftCount leftFuelLe)
    (Nat.le_trans rightCount rightFuelLe)

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

/-- Replacing a common index prefix by related values preserves a pointwise
list relation. The offset form supports the shifted indices in `mapIdx`'s
recursive tail. -/
theorem listRel_mapIdx_replacePrefixFrom
    (related : ListRel relation left right)
    (replacement : relation leftReplacement rightReplacement)
    (offset count : Nat) :
    ListRel relation
      (left.mapIdx fun index value =>
        if offset + index < count then leftReplacement else value)
      (right.mapIdx fun index value =>
        if offset + index < count then rightReplacement else value) := by
  induction related generalizing offset with
  | nil => exact .nil
  | cons head tail recurse =>
      have headRelated : relation
          (if offset < count then leftReplacement else ‹_›)
          (if offset < count then rightReplacement else ‹_›) := by
        by_cases replaced : offset < count
        · simpa [replaced] using replacement
        · simpa [replaced] using head
      have tailRelated := recurse (offset + 1)
      simpa only [List.mapIdx_cons, Nat.add_zero, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using
        ListRel.cons headRelated tailRelated

/-- Array form of `listRel_mapIdx_replacePrefixFrom` at offset zero. -/
theorem arrayRel_mapIdx_replacePrefix
    (related : ArrayRel relation left right)
    (replacement : relation leftReplacement rightReplacement)
    (count : Nat) :
    ArrayRel relation
      (left.mapIdx fun index value =>
        if index < count then leftReplacement else value)
      (right.mapIdx fun index value =>
        if index < count then rightReplacement else value) := by
  unfold ArrayRel at related ⊢
  simp only [Array.toList_mapIdx]
  simpa using
    listRel_mapIdx_replacePrefixFrom related replacement 0 count

/-- Values selected by an array extract remain members of the source array. -/
theorem array_mem_of_mem_extract
    (values : Array α)
    (member : value ∈ (values.extract start stop).toList) :
    value ∈ values.toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop] at member
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

/-- Clearing an array prefix to the tagged-zero sentinel cannot introduce a
new heap reference. -/
theorem heap_mem_of_mem_clearPrefix
    (values : Array Value)
    (member : Value.object (.heap child) ∈
      (values.mapIdx fun index value =>
        if index < count then .object (.tagged 0) else value).toList) :
    Value.object (.heap child) ∈ values.toList := by
  simp only [Array.toList_mapIdx, List.mem_mapIdx] at member
  rcases member with ⟨index, bounded, selected⟩
  by_cases cleared : index < count
  · simp [cleared] at selected
  · rw [List.mem_iff_getElem]
    refine ⟨index, bounded, ?_⟩
    simpa [cleared] using selected

theorem arrayRel_append
    (first : ArrayRel relation leftFirst rightFirst)
    (second : ArrayRel relation leftSecond rightSecond) :
    ArrayRel relation (leftFirst ++ leftSecond) (rightFirst ++ rightSecond) := by
  unfold ArrayRel at first second ⊢
  simpa using listRel_append first second

/-- A successful indexed read from the left list of a `ListRel` has a
successful related read at the same index on the right. -/
theorem listRel_getElem?_some
    {left : List α} {right : List β} {leftValue : α}
    (related : ListRel relation left right)
    (index : Nat)
    (found : left[index]? = some leftValue) :
    ∃ rightValue,
      right[index]? = some rightValue ∧ relation leftValue rightValue := by
  induction related generalizing index leftValue with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at found
          subst leftValue
          exact ⟨_, by simp, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          rcases ih index found with ⟨rightValue, rightFound, values⟩
          exact ⟨rightValue, by simpa using rightFound, values⟩

/-- Array form of `listRel_getElem?_some`. -/
theorem arrayRel_getElem?_some
    {left : Array α} {right : Array β} {leftValue : α}
    (related : ArrayRel relation left right)
    (index : Nat)
    (found : left[index]? = some leftValue) :
    ∃ rightValue,
      right[index]? = some rightValue ∧ relation leftValue rightValue := by
  unfold ArrayRel at related
  have listFound : left.toList[index]? = some leftValue := by
    simpa using found
  rcases listRel_getElem?_some related index listFound with
    ⟨rightValue, rightFound, values⟩
  exact ⟨rightValue, by simpa using rightFound, values⟩

/-- A successful optional list read returns a member of that list. -/
theorem list_mem_of_getElem?_eq_some
    {values : List α} (index : Nat)
    (found : values[index]? = some value) :
    value ∈ values := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at found
          subst value
          exact List.mem_cons_self
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          exact List.mem_cons_of_mem head (ih index found)

/-- Array form of `list_mem_of_getElem?_eq_some`. -/
theorem array_mem_of_getElem?_eq_some
    {values : Array α} (index : Nat)
    (found : values[index]? = some value) :
    value ∈ values.toList := by
  apply list_mem_of_getElem?_eq_some index
  simpa using found

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

/-- Inserting related values under the same cache key preserves related
global tables; the filtered tails make the replacement semantics explicit. -/
theorem insertGlobal_related
    (globals : ListRel (NamedValueRel rho) left right)
    (value : ValueRel rho leftValue rightValue) :
    ListRel (NamedValueRel rho)
      (insertGlobal left name leftValue)
      (insertGlobal right name rightValue) := by
  unfold insertGlobal
  apply ListRel.cons ⟨rfl, value⟩
  induction globals with
  | nil => exact .nil
  | cons head tail ih =>
      rename_i leftHead rightHead leftTail rightTail
      obtain ⟨leftName, leftHeadValue⟩ := leftHead
      obtain ⟨rightName, rightHeadValue⟩ := rightHead
      rcases head with ⟨nameEq, headValue⟩
      simp only at nameEq headValue
      subst leftName
      have headRelated : NamedValueRel rho
          (rightName, leftHeadValue) (rightName, rightHeadValue) :=
        ⟨rfl, headValue⟩
      by_cases keep : rightName != name
      · simpa [keep] using ListRel.cons headRelated ih
      · simpa [keep] using ih

/-- Every value retained by cache insertion is either the newly inserted
value or came from the old global table. -/
theorem insertGlobal_values_subset
    (member : candidate ∈ (insertGlobal globals name value).map Prod.snd) :
    candidate = value ∨ candidate ∈ globals.map Prod.snd := by
  simp only [insertGlobal, List.map_cons, List.mem_cons] at member
  rcases member with same | old
  · exact Or.inl same
  · rcases List.mem_map.mp old with ⟨entry, filtered, entryEq⟩
    exact Or.inr (List.mem_map.mpr
      ⟨entry, (List.mem_filter.mp filtered).1, entryEq⟩)

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
      | fault rightFault =>
          change RuntimeFaultRel smaller leftFault rightFault at related
          change RuntimeFaultRel larger leftFault rightFault
          cases related with
          | same => exact .same _
          | deadObject mapped =>
              exact .deadObject (extension.forward mapped)
          | referenceCountUnderflow mapped =>
              exact .referenceCountUnderflow (extension.forward mapped)

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

/-- Promoting related values already published as extra roots preserves the
complete runtime relation, even when unreachable heap padding gives the two
public persistence calls different fuel budgets. -/
theorem ShadowRuntimeRel.markPersistentBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (value : ValueRel rho leftValue rightValue)
    (leftPublished : leftValue ∈ leftExtra)
    (rightPublished : rightValue ∈ rightExtra) :
    ShadowRuntimeRel rho
      (left.markPersistent leftValue)
      (right.markPersistent rightValue)
      leftExtra rightExtra := by
  cases value with
  | heap mapping =>
      rename_i leftLocation rightLocation
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        apply Reachable.root
        simp [runtimeRoots, leftPublished]
      have rightReachable : Reachable right.heap
          (runtimeRoots right rightExtra) rightLocation := by
        apply Reachable.root
        simp [runtimeRoots, rightPublished]
      have heaps := heapRel_markPersistentBoth related.heap mapping
        leftReachable rightReachable
      exact {
        extra := related.extra
        globals := by
          simpa using related.globals
        world_eq := by
          simpa using related.world_eq
        trace := by
          simpa using related.trace
        heap := by
          simpa [RuntimeState.markPersistent, runtimeRoots] using heaps
        leftMappingFresh := by
          intro location bounded
          exact related.leftMappingFresh location (by simpa using bounded)
        rightMappingFresh := by
          intro location bounded
          exact related.rightMappingFresh location (by simpa using bounded)
        leftHeapFresh := by
          intro location bounded
          have oldNone := related.leftHeapFresh location
            (by simpa using bounded)
          have frame :=
            heapOwnershipFrame_markPersistentLocationFuel
              (left.heap.length + 1) left.heap leftLocation
          simpa [RuntimeState.markPersistent] using frame.find_none oldNone
        rightHeapFresh := by
          intro location bounded
          have oldNone := related.rightHeapFresh location
            (by simpa using bounded)
          have frame :=
            heapOwnershipFrame_markPersistentLocationFuel
              (right.heap.length + 1) right.heap rightLocation
          simpa [RuntimeState.markPersistent] using frame.find_none oldNone
      }
  | tagged payload | usize payload | scalar payload | erased
  | reuseNone | reuseSome mapping =>
      simpa [RuntimeState.markPersistent] using related

/-- Paired cache insertion preserves the reachable runtime relation when the
cached values are already published roots.  Persistence handles the heap;
insertion only replaces one related global entry, and its new root duplicates
the already-published value. -/
theorem ShadowRuntimeRel.setGlobalBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (value : ValueRel rho leftValue rightValue)
    (leftPublished : leftValue ∈ leftExtra)
    (rightPublished : rightValue ∈ rightExtra) :
    ShadowRuntimeRel rho
      (left.setGlobal name leftValue)
      (right.setGlobal name rightValue)
      leftExtra rightExtra := by
  have persisted := related.markPersistentBoth value
    leftPublished rightPublished
  have leftSubset : RootSubset
      (runtimeRoots (left.setGlobal name leftValue) leftExtra)
      (runtimeRoots (left.markPersistent leftValue) leftExtra) := by
    intro candidate member
    simp only [runtimeRoots, RuntimeState.setGlobal,
      RuntimeState.markPersistent_globals, RuntimeState.markPersistent_trace,
      List.mem_append] at member ⊢
    rcases member with (extra | global) | traced
    · exact Or.inl (Or.inl extra)
    · rcases insertGlobal_values_subset global with same | old
      · subst candidate
        exact Or.inl (Or.inl leftPublished)
      · exact Or.inl (Or.inr old)
    · exact Or.inr traced
  have rightSubset : RootSubset
      (runtimeRoots (right.setGlobal name rightValue) rightExtra)
      (runtimeRoots (right.markPersistent rightValue) rightExtra) := by
    intro candidate member
    simp only [runtimeRoots, RuntimeState.setGlobal,
      RuntimeState.markPersistent_globals, RuntimeState.markPersistent_trace,
      List.mem_append] at member ⊢
    rcases member with (extra | global) | traced
    · exact Or.inl (Or.inl extra)
    · rcases insertGlobal_values_subset global with same | old
      · subst candidate
        exact Or.inl (Or.inl rightPublished)
      · exact Or.inl (Or.inr old)
    · exact Or.inr traced
  exact {
    extra := persisted.extra
    globals := by
      simpa [RuntimeState.setGlobal] using
        insertGlobal_related related.globals value
    world_eq := by
      simpa [RuntimeState.setGlobal] using persisted.world_eq
    trace := by
      simpa [RuntimeState.setGlobal] using persisted.trace
    heap := by
      simpa [RuntimeState.setGlobal] using
        heapRel_monoRoots persisted.heap leftSubset rightSubset
    leftMappingFresh := by
      simpa [RuntimeState.setGlobal] using persisted.leftMappingFresh
    rightMappingFresh := by
      simpa [RuntimeState.setGlobal] using persisted.rightMappingFresh
    leftHeapFresh := by
      simpa [RuntimeState.setGlobal] using persisted.leftHeapFresh
    rightHeapFresh := by
      simpa [RuntimeState.setGlobal] using persisted.rightHeapFresh
  }

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

/-- A heap frame away from one modified location either preserves a reachable
candidate or discovers that the modified location was already reached along
the old path. -/
theorem reachable_heapFrame_or_modified
    (frame : ∀ other, other ≠ modified →
      findCell? after other = findCell? before other)
    (reachable : Reachable before roots candidate) :
    Reachable after roots candidate ∨ Reachable after roots modified := by
  induction reachable with
  | root member => exact Or.inl (.root member)
  | child parentReachable cellFound member reference ih =>
      rename_i parent child cell value
      rcases ih with parentPreserved | modifiedReached
      · by_cases same : parent = modified
        · exact Or.inr (same ▸ parentPreserved)
        · exact Or.inl (.child parentPreserved
            (by rw [frame parent same]; exact cellFound) member reference)
      · exact Or.inr modifiedReached

/-- Replacing a cell preserves reachability of the replaced location itself.
If an old path cycles through that location, the first visit already supplies
the required post-update reachability. -/
theorem reachable_setCell_location
    (found : findCell? before.heap location = some current)
    (effect : setCell before location replacement = .ok after)
    (reachable :
      Reachable before.heap (runtimeRoots before extra) location) :
    Reachable after.heap (runtimeRoots after extra) location := by
  rcases setCell_spec_of_find before location current replacement found with
    ⟨result, resultEffect, _target, frame, _length, _nextLocation,
      globals, _world, trace⟩
  rw [effect] at resultEffect
  cases resultEffect
  rcases reachable_heapFrame_or_modified frame reachable with
    preserved | reached
  · simpa [runtimeRoots, globals, trace] using preserved
  · simpa [runtimeRoots, globals, trace] using reached

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

/-- An already-published related value may be repeated as a direct control
root without changing the reachable heap relation. -/
theorem ShadowRuntimeRel.prependRelatedRoot
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftValue ∈ leftExtra)
    (rightMember : rightValue ∈ rightExtra)
    (values : ValueRel rho leftValue rightValue) :
    ShadowRuntimeRel rho left right
      (leftValue :: leftExtra) (rightValue :: rightExtra) := by
  apply related.restrictExtra (.cons values related.extra)
  · intro value member
    simp only [List.mem_cons] at member ⊢
    rcases member with same | old
    · subst value
      exact leftMember
    · exact old
  · intro value member
    simp only [List.mem_cons] at member ⊢
    rcases member with same | old
    · subst value
      exact rightMember
    · exact old

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

/-- A direct root which is not a heap reference cannot introduce a reachable
heap location.  This packages the common immediate-value argument used by
tagged naturals, scalars, unboxed words, and erased values. -/
theorem reachable_without_nonHeap_root
    (nonHeap : ∀ candidate, root ≠ .object (.heap candidate))
    (reachable : Reachable heap (root :: roots) location) :
    Reachable heap roots location := by
  induction reachable with
  | root member =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · exact (nonHeap _ same.symm).elim
      · exact .root member
  | child parent found owned reference ih =>
      exact .child ih found owned reference

/-- Promoting an already semantically reachable value to a direct root does
not enlarge the reachable heap.  Non-heap values satisfy `rooted` vacuously;
heap children use the existing parent-to-child reachability derivation. -/
theorem reachable_without_reachable_root
    (rooted : ∀ candidate,
      root = .object (.heap candidate) → Reachable heap roots candidate)
    (reachable : Reachable heap (root :: roots) location) :
    Reachable heap roots location := by
  induction reachable with
  | root member =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · exact rooted _ same.symm
      · exact .root member
  | child parent found owned reference ih =>
      exact .child ih found owned reference

/-- A related pair already reachable through the published roots may be
promoted to direct continuation roots on both sides. -/
theorem ShadowRuntimeRel.prependReachable
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (values : ValueRel rho leftRoot rightRoot)
    (leftRooted : ∀ location,
      leftRoot = .object (.heap location) →
        Reachable left.heap (runtimeRoots left leftExtra) location)
    (rightRooted : ∀ location,
      rightRoot = .object (.heap location) →
        Reachable right.heap (runtimeRoots right rightExtra) location) :
    ShadowRuntimeRel rho left right
      (leftRoot :: leftExtra) (rightRoot :: rightExtra) := by
  apply related.reindexExtra (.cons values related.extra)
  · intro location reachable
    apply reachable_without_reachable_root leftRooted
    simpa [runtimeRoots] using reachable
  · intro location reachable
    apply reachable_without_reachable_root rightRooted
    simpa [runtimeRoots] using reachable

/-- A pair of related immediate values may be published as direct roots
without changing either reachable heap. -/
theorem ShadowRuntimeRel.prependNonHeap
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (values : ValueRel rho leftRoot rightRoot)
    (leftNonHeap : ∀ location, leftRoot ≠ .object (.heap location))
    (rightNonHeap : ∀ location, rightRoot ≠ .object (.heap location)) :
    ShadowRuntimeRel rho left right
      (leftRoot :: leftExtra) (rightRoot :: rightExtra) := by
  apply related.reindexExtra (.cons values related.extra)
  · intro location reachable
    apply reachable_without_nonHeap_root leftNonHeap
    simpa [runtimeRoots] using reachable
  · intro location reachable
    apply reachable_without_nonHeap_root rightNonHeap
    simpa [runtimeRoots] using reachable

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

/-- Publishing the results of a covered argument evaluation preserves the
runtime relation.  Every evaluated argument is either the synthetic erased
value or an already-published live environment root. -/
theorem ShadowRuntimeRel.publishEvalArgs
    (related : ShadowRuntimeRel rho left right
      (envRootsOn used leftEnv ++ leftTail)
      (envRootsOn used rightEnv ++ rightTail))
    (covered : ArgsCovered used arguments)
    (leftEvaluated : evalArgs leftEnv arguments = .ok leftValues)
    (rightEvaluated : evalArgs rightEnv arguments = .ok rightValues)
    (values : ArrayRel (ValueRel rho) leftValues rightValues) :
    ShadowRuntimeRel rho left right
      (leftValues.toList ++ (envRootsOn used leftEnv ++ leftTail))
      (rightValues.toList ++ (envRootsOn used rightEnv ++ rightTail)) := by
  have leftSubsetValues :=
    evalArgs_values_subset covered leftEvaluated
  have rightSubsetValues :=
    evalArgs_values_subset covered rightEvaluated
  have leftSubset : RootSubset
      (leftValues.toList ++ (envRootsOn used leftEnv ++ leftTail))
      (.erased :: (envRootsOn used leftEnv ++ leftTail)) := by
    intro value member
    rcases List.mem_append.mp member with evaluated | old
    · have rooted := leftSubsetValues value evaluated
      simp only [List.mem_cons] at rooted ⊢
      rcases rooted with erased | environment
      · exact Or.inl erased
      · exact Or.inr (List.mem_append_left _ environment)
    · exact List.mem_cons_of_mem _ old
  have rightSubset : RootSubset
      (rightValues.toList ++ (envRootsOn used rightEnv ++ rightTail))
      (.erased :: (envRootsOn used rightEnv ++ rightTail)) := by
    intro value member
    rcases List.mem_append.mp member with evaluated | old
    · have rooted := rightSubsetValues value evaluated
      simp only [List.mem_cons] at rooted ⊢
      rcases rooted with erased | environment
      · exact Or.inl erased
      · exact Or.inr (List.mem_append_left _ environment)
    · exact List.mem_cons_of_mem _ old
  exact related.prependErased.restrictExtra
    (listRel_append values related.extra) leftSubset rightSubset

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

/-- Constructor-tag reads of related published values either return the same
tag or fail with related runtime faults.  In particular, a dead heap reference
reports the concrete source and target locations related by `rho`. -/
theorem ShadowRuntimeRel.getTagBoth_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftValue ∈ leftExtra)
    (values : ValueRel rho leftValue rightValue) :
    ExceptRel (RuntimeFaultRel rho) Eq
      (getTag left leftValue) (getTag right rightValue) := by
  cases values with
  | tagged payload => exact .ok rfl
  | usize value => exact .ok rfl
  | scalar value => exact .ok rfl
  | erased => exact .error (.same _)
  | reuseNone => exact .error (.same _)
  | reuseSome mapped => exact .error (.same _)
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have objects := cells.2.2.2
      generalize leftObjectEq : leftCell.object = leftObject at objects
      generalize rightObjectEq : rightCell.object = rightObject at objects
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            simpa [rightLiveEq] using liveEq
          simp [getTag, getLiveCell, leftFound, rightFound, leftLiveEq,
            rightLiveEq, Bind.bind, Except.bind]
          exact .error (RuntimeFaultRel.deadObject mapping)
      | true =>
          have leftLiveEq : leftCell.live = true := by
            simpa [rightLiveEq] using liveEq
          cases objects <;>
            simp_all [getTag, getLiveCell, leftFound, rightFound,
              Bind.bind, Except.bind] <;>
            first
            | exact .ok rfl
            | exact .error (.same _)

/-- A successful constructor-tag read of a related published value succeeds
with the same tag on the target. -/
theorem ShadowRuntimeRel.getTagBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftValue ∈ leftExtra)
    (values : ValueRel rho leftValue rightValue)
    (sourceRead : getTag left leftValue = .ok tag) :
    getTag right rightValue = .ok tag := by
  cases values with
  | tagged payload => simpa [getTag] using sourceRead
  | usize value => simpa [getTag] using sourceRead
  | scalar value => simpa [getTag] using sourceRead
  | erased => simp [getTag] at sourceRead
  | reuseNone => simp [getTag] at sourceRead
  | reuseSome mapped => simp [getTag] at sourceRead
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have objects := cells.2.2.2
      generalize leftObjectEq : leftCell.object = leftObject at objects
      generalize rightObjectEq : rightCell.object = rightObject at objects
      cases rightLiveEq : rightCell.live with
      | false =>
          simp_all [getTag, getLiveCell, leftFound, rightFound,
            Bind.bind, Except.bind]
      | true =>
          cases objects <;>
            simp_all [getTag, getLiveCell, leftFound, rightFound,
              Bind.bind, Except.bind]

/-- A successful sharedness query on a related published object succeeds on
the target with a related scalar result.  Heap references use equality of
the related cells' liveness, persistence, and reference count; tagged objects
return the common immediate `true` result. -/
theorem ShadowRuntimeRel.isSharedBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftValue ∈ leftExtra)
    (values : ValueRel rho leftValue rightValue)
    (sourceRead : isShared left leftValue = .ok leftResult) :
    ∃ rightResult,
      isShared right rightValue = .ok rightResult ∧
      ValueRel rho leftResult rightResult ∧
      ShadowRuntimeRel rho left right
        (leftResult :: leftExtra) (rightResult :: rightExtra) := by
  cases values with
  | tagged payload =>
      have resultEq :
          leftResult = .scalar (.uint8 1) := by
        have normalized := sourceRead
        simp [isShared] at normalized
        exact normalized.symm
      subst leftResult
      refine ⟨.scalar (.uint8 1), by simp [isShared], .scalar _, ?_⟩
      exact related.prependNonHeap (.scalar _)
        (by intro location; simp) (by intro location; simp)
  | usize value => simp [isShared] at sourceRead
  | scalar value => simp [isShared] at sourceRead
  | erased => simp [isShared] at sourceRead
  | reuseNone => simp [isShared] at sourceRead
  | reuseSome mapped => simp [isShared] at sourceRead
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      cases leftLiveEq : leftCell.live with
      | false =>
          simp [isShared, getLiveCell, leftFound, leftLiveEq,
            Functor.map, Except.map] at sourceRead
      | true =>
          have rightLiveEq : rightCell.live = true := by
            rw [← cells.2.2.1]
            exact leftLiveEq
          have persistentEq : leftCell.persistent = rightCell.persistent :=
            cells.2.1
          have rcEq : leftCell.rc = rightCell.rc := cells.1
          have resultEq : leftResult =
              .scalar (.uint8
                (if leftCell.persistent || leftCell.rc != 1 then 1 else 0)) := by
            have normalized := sourceRead
            simp [isShared, getLiveCell, leftFound, leftLiveEq,
              Functor.map, Except.map] at normalized
            simpa using normalized.symm
          subst leftResult
          let result : Value := .scalar (.uint8
            (if rightCell.persistent || rightCell.rc != 1 then 1 else 0))
          have sameResult : result = .scalar (.uint8
              (if leftCell.persistent || leftCell.rc != 1 then 1 else 0)) := by
            simp [result, ← persistentEq, ← rcEq]
          subst result
          refine ⟨_, ?_, .scalar _, ?_⟩
          · simp [isShared, getLiveCell, rightFound, rightLiveEq,
              ← persistentEq, ← rcEq, Functor.map, Except.map]
          · exact related.prependNonHeap (.scalar _)
              (by intro location; simp) (by intro location; simp)

/-- A successful object-field projection from a related published
constructor succeeds at the same index on the target.  The selected fields
are related and, as children of already reachable constructor roots, may be
promoted to direct continuation roots. -/
theorem ShadowRuntimeRel.getObjectFieldBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceRead : getObjectField left leftObject index = .ok leftField) :
    ∃ rightField,
      getObjectField right rightObject index = .ok rightField ∧
      ValueRel rho leftField rightField ∧
      ShadowRuntimeRel rho left right
        (leftField :: leftExtra) (rightField :: rightExtra) := by
  cases objects with
  | tagged payload =>
      simp [getObjectField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | usize value =>
      simp [getObjectField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | scalar value =>
      simp [getObjectField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | erased =>
      simp [getObjectField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | reuseNone =>
      simp [getObjectField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | reuseSome mapped =>
      simp [getObjectField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      have rightReachable : Reachable right.heap
          (runtimeRoots right rightExtra) rightLocation := by
        rcases reachable_forward related.roots related.heap
            leftReachable with
          ⟨mappedLocation, mappedEq, reachable⟩
        have locationEq : mappedLocation = rightLocation := by
          rw [mapping] at mappedEq
          exact (Option.some.inj mappedEq).symm
        simpa [locationEq] using reachable
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have heapObjects := cells.2.2.2
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            rw [liveEq]
            exact rightLiveEq
          simp [getObjectField, getConstructor, getLiveCell, leftFound,
            leftLiveEq, Bind.bind, Except.bind] at sourceRead
      | true =>
          have leftLiveEq : leftCell.live = true := by
            rw [liveEq]
            exact rightLiveEq
          generalize leftObjectEq :
            leftCell.object = leftHeapObject at heapObjects
          generalize rightObjectEq :
            rightCell.object = rightHeapObject at heapObjects
          cases heapObjects with
          | @ctor leftConstructor rightConstructor tag fields usizes scalars =>
              generalize leftFieldEq :
                leftConstructor.objectFields[index]? = leftFieldResult
                  at sourceRead
              cases leftFieldResult with
              | none =>
                  simp [getObjectField, getConstructor, getLiveCell,
                    leftFound, leftLiveEq, leftObjectEq, leftFieldEq,
                    Bind.bind, Except.bind, Pure.pure, Except.pure]
                    at sourceRead
              | some sourceValue =>
                  have valueEq : leftField = sourceValue := by
                    have normalized := sourceRead
                    simp [getObjectField, getConstructor, getLiveCell,
                      leftFound, leftLiveEq, leftObjectEq, leftFieldEq,
                      Bind.bind, Except.bind, Pure.pure, Except.pure]
                      at normalized
                    exact normalized.symm
                  subst leftField
                  rcases arrayRel_getElem?_some fields index leftFieldEq with
                    ⟨targetValue, rightFieldEq, values⟩
                  have targetRead :
                      getObjectField right
                        (.object (.heap rightLocation)) index =
                          .ok targetValue := by
                    simp [getObjectField, getConstructor, getLiveCell,
                      rightFound, rightLiveEq, rightObjectEq, rightFieldEq,
                      Bind.bind, Except.bind, Pure.pure, Except.pure]
                  have leftRooted : ∀ location,
                      sourceValue = .object (.heap location) →
                        Reachable left.heap
                          (runtimeRoots left leftExtra) location := by
                    intro location reference
                    exact .child leftReachable leftFound
                      (by simpa [leftObjectEq, HeapObject.ownedValues] using
                        array_mem_of_getElem?_eq_some index leftFieldEq)
                      reference
                  have rightRooted : ∀ location,
                      targetValue = .object (.heap location) →
                        Reachable right.heap
                          (runtimeRoots right rightExtra) location := by
                    intro location reference
                    exact .child rightReachable rightFound
                      (by simpa [rightObjectEq, HeapObject.ownedValues] using
                        array_mem_of_getElem?_eq_some index rightFieldEq)
                      reference
                  exact ⟨targetValue, targetRead, values,
                    related.prependReachable values leftRooted rightRooted⟩
          | closure fixed =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | boxed value =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | string value =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | natural value =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | integer value =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | byteArray value =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | «opaque» value =>
              simp [getObjectField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead

/-- Every successful absolute fixed-slot `USize` read returns an unboxed
word value. -/
theorem getUSizeSlot_ok_eq_usize
    (read : getUSizeSlot runtime object slot = .ok result) :
    ∃ word, result = .usize word := by
  unfold getUSizeSlot at read
  generalize constructorEq :
    getConstructor runtime object = constructorResult at read
  cases constructorResult with
  | error fault =>
      simp [constructorEq, Bind.bind, Except.bind] at read
  | ok constructor =>
      obtain ⟨location, cell, value⟩ := constructor
      simp only [constructorEq, Bind.bind, Except.bind] at read
      by_cases bounded : value.objectFields.size ≤ slot
      · rw [if_pos bounded] at read
        generalize fieldEq :
          value.usizeFields[slot - value.objectFields.size]? = fieldResult
            at read
        cases fieldResult with
        | none =>
            simp [fieldEq] at read
        | some word =>
            simp [fieldEq, Pure.pure, Except.pure] at read
            cases read
            exact ⟨word, rfl⟩
      · rw [if_neg bounded] at read
        simp at read

/-- An absolute fixed-slot `USize` projection from a related published
constructor succeeds with the same immediate word on the target. -/
theorem ShadowRuntimeRel.getUSizeSlotBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceRead : getUSizeSlot left leftObject slot = .ok leftField) :
    ∃ rightField,
      getUSizeSlot right rightObject slot = .ok rightField ∧
      ValueRel rho leftField rightField ∧
      ShadowRuntimeRel rho left right
        (leftField :: leftExtra) (rightField :: rightExtra) := by
  cases objects with
  | tagged payload =>
      simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | usize value =>
      simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | scalar value =>
      simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | erased =>
      simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | reuseNone =>
      simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | reuseSome mapped =>
      simp [getUSizeSlot, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have heapObjects := cells.2.2.2
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            rw [liveEq]
            exact rightLiveEq
          simp [getUSizeSlot, getConstructor, getLiveCell, leftFound,
            leftLiveEq, Bind.bind, Except.bind] at sourceRead
      | true =>
          have leftLiveEq : leftCell.live = true := by
            rw [liveEq]
            exact rightLiveEq
          generalize leftObjectEq :
            leftCell.object = leftHeapObject at heapObjects
          generalize rightObjectEq :
            rightCell.object = rightHeapObject at heapObjects
          cases heapObjects with
          | @ctor leftConstructor rightConstructor tag fields usizes scalars =>
              have objectSizeEq :
                  leftConstructor.objectFields.size =
                    rightConstructor.objectFields.size :=
                arrayRel_size_eq fields
              have targetRead :
                  getUSizeSlot right
                    (.object (.heap rightLocation)) slot =
                      .ok leftField := by
                simpa [getUSizeSlot, getConstructor, getLiveCell,
                  leftFound, rightFound, leftLiveEq, rightLiveEq,
                  leftObjectEq, rightObjectEq, objectSizeEq, usizes,
                  Bind.bind, Except.bind, Pure.pure, Except.pure]
                  using sourceRead
              rcases getUSizeSlot_ok_eq_usize sourceRead with
                ⟨word, resultEq⟩
              subst leftField
              exact ⟨.usize word, targetRead, .usize word,
                related.prependNonHeap (.usize word)
                  (by intro location; simp) (by intro location; simp)⟩
          | closure fixed =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | boxed value =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | string value =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | natural value =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | integer value =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | byteArray value =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | «opaque» value =>
              simp [getUSizeSlot, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead

/-- Every successful packed-scalar read returns an unboxed scalar value. -/
theorem getScalarField_ok_eq_scalar
    (read : getScalarField runtime object width offset = .ok result) :
    ∃ scalar, result = .scalar scalar := by
  unfold getScalarField at read
  generalize constructorEq :
    getConstructor runtime object = constructorResult at read
  cases constructorResult with
  | error fault =>
      simp [constructorEq, Bind.bind, Except.bind] at read
  | ok constructor =>
      obtain ⟨location, cell, value⟩ := constructor
      simp only [constructorEq, Bind.bind, Except.bind] at read
      generalize fieldEq :
        value.scalarFields.find? (fun field =>
          field.width == width && field.offset == offset) = fieldResult
          at read
      cases fieldResult with
      | none =>
          simp [fieldEq] at read
      | some field =>
          simp [fieldEq, Pure.pure, Except.pure] at read
          cases read
          exact ⟨field.value, rfl⟩

/-- A packed-scalar projection from a related published constructor succeeds
with the same immediate scalar on the target. -/
theorem ShadowRuntimeRel.getScalarFieldBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceRead :
      getScalarField left leftObject width offset = .ok leftField) :
    ∃ rightField,
      getScalarField right rightObject width offset = .ok rightField ∧
      ValueRel rho leftField rightField ∧
      ShadowRuntimeRel rho left right
        (leftField :: leftExtra) (rightField :: rightExtra) := by
  cases objects with
  | tagged payload =>
      simp [getScalarField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | usize value =>
      simp [getScalarField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | scalar value =>
      simp [getScalarField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | erased =>
      simp [getScalarField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | reuseNone =>
      simp [getScalarField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | reuseSome mapped =>
      simp [getScalarField, getConstructor, Bind.bind, Except.bind]
        at sourceRead
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have heapObjects := cells.2.2.2
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            rw [liveEq]
            exact rightLiveEq
          simp [getScalarField, getConstructor, getLiveCell, leftFound,
            leftLiveEq, Bind.bind, Except.bind] at sourceRead
      | true =>
          have leftLiveEq : leftCell.live = true := by
            rw [liveEq]
            exact rightLiveEq
          generalize leftObjectEq :
            leftCell.object = leftHeapObject at heapObjects
          generalize rightObjectEq :
            rightCell.object = rightHeapObject at heapObjects
          cases heapObjects with
          | @ctor leftConstructor rightConstructor tag fields usizes scalars =>
              have targetRead :
                  getScalarField right
                    (.object (.heap rightLocation)) width offset =
                      .ok leftField := by
                simpa [getScalarField, getConstructor, getLiveCell,
                  leftFound, rightFound, leftLiveEq, rightLiveEq,
                  leftObjectEq, rightObjectEq, scalars,
                  Bind.bind, Except.bind, Pure.pure, Except.pure]
                  using sourceRead
              rcases getScalarField_ok_eq_scalar sourceRead with
                ⟨scalar, resultEq⟩
              subst leftField
              exact ⟨.scalar scalar, targetRead, .scalar scalar,
                related.prependNonHeap (.scalar scalar)
                  (by intro location; simp) (by intro location; simp)⟩
          | closure fixed =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | boxed value =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | string value =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | natural value =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | integer value =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | byteArray value =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | «opaque» value =>
              simp [getScalarField, getConstructor, getLiveCell,
                leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead

/-- Successful tagged-object unboxing always produces an immediate scalar or
`USize` word. -/
theorem scalarFromType_ok_eq_immediate
    (read : scalarFromType type payload = .ok result) :
    (∃ scalar, result = .scalar scalar) ∨
      ∃ word, result = .usize word := by
  by_cases uint8 : type == LCNF.ImpureType.uint8
  · left
    have normalized := read
    simp [scalarFromType, uint8] at normalized
    exact ⟨.uint8 payload.toUInt8, normalized.symm⟩
  · by_cases uint16 : type == LCNF.ImpureType.uint16
    · left
      have normalized := read
      simp [scalarFromType, uint8, uint16] at normalized
      exact ⟨.uint16 payload.toUInt16, normalized.symm⟩
    · by_cases uint32 : type == LCNF.ImpureType.uint32
      · left
        have normalized := read
        simp [scalarFromType, uint8, uint16, uint32] at normalized
        exact ⟨.uint32 payload.toUInt32, normalized.symm⟩
      · by_cases uint64 : type == LCNF.ImpureType.uint64
        · left
          have normalized := read
          simp [scalarFromType, uint8, uint16, uint32, uint64] at normalized
          exact ⟨.uint64 payload, normalized.symm⟩
        · by_cases usize : type == LCNF.ImpureType.usize
          · right
            have normalized := read
            simp [scalarFromType, uint8, uint16, uint32, uint64, usize]
              at normalized
            exact ⟨payload, normalized.symm⟩
          · simp [scalarFromType, uint8, uint16, uint32, uint64, usize]
              at read

/-- Unboxing a related published object succeeds on the target with a related
payload. Heap-box payloads are promoted from child reachability to direct
continuation roots. -/
theorem ShadowRuntimeRel.unboxBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceRead : unbox left type leftObject = .ok leftResult) :
    ∃ rightResult,
      unbox right type rightObject = .ok rightResult ∧
      ValueRel rho leftResult rightResult ∧
      ShadowRuntimeRel rho left right
        (leftResult :: leftExtra) (rightResult :: rightExtra) := by
  cases objects with
  | tagged payload =>
      have scalarRead : scalarFromType type payload = .ok leftResult := by
        simpa [unbox] using sourceRead
      have targetRead :
          unbox right type (.object (.tagged payload)) = .ok leftResult := by
        simpa [unbox] using scalarRead
      rcases scalarFromType_ok_eq_immediate scalarRead with
        ⟨scalar, resultEq⟩ | ⟨word, resultEq⟩
      · subst leftResult
        exact ⟨.scalar scalar, targetRead, .scalar scalar,
          related.prependNonHeap (.scalar scalar)
            (by intro location; simp) (by intro location; simp)⟩
      · subst leftResult
        exact ⟨.usize word, targetRead, .usize word,
          related.prependNonHeap (.usize word)
            (by intro location; simp) (by intro location; simp)⟩
  | usize value => simp [unbox] at sourceRead
  | scalar value => simp [unbox] at sourceRead
  | erased => simp [unbox] at sourceRead
  | reuseNone => simp [unbox] at sourceRead
  | reuseSome mapped => simp [unbox] at sourceRead
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ leftMember)
      have rightReachable : Reachable right.heap
          (runtimeRoots right rightExtra) rightLocation := by
        rcases reachable_forward related.roots related.heap
            leftReachable with
          ⟨mappedLocation, mappedEq, reachable⟩
        have locationEq : mappedLocation = rightLocation := by
          rw [mapping] at mappedEq
          exact (Option.some.inj mappedEq).symm
        simpa [locationEq] using reachable
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have heapObjects := cells.2.2.2
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            rw [liveEq]
            exact rightLiveEq
          simp [unbox, getLiveCell, leftFound, leftLiveEq,
            Bind.bind, Except.bind] at sourceRead
      | true =>
          have leftLiveEq : leftCell.live = true := by
            rw [liveEq]
            exact rightLiveEq
          generalize leftObjectEq :
            leftCell.object = leftHeapObject at heapObjects
          generalize rightObjectEq :
            rightCell.object = rightHeapObject at heapObjects
          cases heapObjects with
          | ctor tag fields usizes scalars =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | closure fixed =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | @boxed boxedType leftValue rightValue values =>
              have resultEq : leftResult = leftValue := by
                have normalized := sourceRead
                simp [unbox, getLiveCell, leftFound, leftLiveEq,
                  leftObjectEq, Bind.bind, Except.bind,
                  Pure.pure, Except.pure] at normalized
                exact normalized.symm
              subst leftResult
              have targetRead :
                  unbox right type (.object (.heap rightLocation)) =
                    .ok rightValue := by
                simp [unbox, getLiveCell, rightFound, rightLiveEq,
                  rightObjectEq, Bind.bind, Except.bind,
                  Pure.pure, Except.pure]
              have leftRooted : ∀ location,
                  leftValue = .object (.heap location) →
                    Reachable left.heap
                      (runtimeRoots left leftExtra) location := by
                intro location reference
                exact .child leftReachable leftFound
                  (by simp [leftObjectEq, HeapObject.ownedValues])
                  reference
              have rightRooted : ∀ location,
                  rightValue = .object (.heap location) →
                    Reachable right.heap
                      (runtimeRoots right rightExtra) location := by
                intro location reference
                exact .child rightReachable rightFound
                  (by simp [rightObjectEq, HeapObject.ownedValues])
                  reference
              exact ⟨rightValue, targetRead, values,
                related.prependReachable values leftRooted rightRooted⟩
          | string value =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | natural value =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | integer value =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | byteArray value =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead
          | «opaque» value =>
              simp [unbox, getLiveCell, leftFound, leftLiveEq, leftObjectEq,
                Bind.bind, Except.bind] at sourceRead

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

/-- Constructor-tag writes to related published values either preserve the
reachable runtime relation or fail with related faults. -/
theorem ShadowRuntimeRel.setTagBoth_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject) :
    ExceptRel (RuntimeFaultRel rho)
      (fun leftResult rightResult =>
        ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra)
      (setTag left leftObject tag) (setTag right rightObject tag) := by
  cases objects with
  | tagged payload => exact .error (.same _)
  | usize value => exact .error (.same _)
  | scalar value => exact .error (.same _)
  | erased => exact .error (.same _)
  | reuseNone => exact .error (.same _)
  | reuseSome mapping => exact .error (.same _)
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ objectRoot)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      have objectRelation := cells.2.2.2
      generalize leftObjectEq : leftCell.object = leftHeapObject
        at objectRelation
      generalize rightObjectEq : rightCell.object = rightHeapObject
        at objectRelation
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            simpa [rightLiveEq] using liveEq
          simp [setTag, modifyConstructor, getConstructor, getLiveCell,
            leftFound, rightFound, leftLiveEq, rightLiveEq,
            Bind.bind, Except.bind]
          exact .error (.deadObject mapping)
      | true =>
          have leftLiveEq : leftCell.live = true := by
            simpa [rightLiveEq] using liveEq
          cases objectRelation with
          | ctor objectTag objectFields usizes scalars =>
              rename_i leftConstructor rightConstructor
              rcases related.setTagBoth mapping leftReachable leftFound
                  leftLiveEq leftObjectEq tag with
                ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
              rw [leftEffect, rightEffect]
              exact .ok next
          | closure fixed =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)
          | boxed value =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)
          | string value =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)
          | natural value =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)
          | integer value =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)
          | byteArray value =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)
          | «opaque» typeName =>
              simp [setTag, modifyConstructor, getConstructor, getLiveCell,
                leftFound, rightFound, leftLiveEq, rightLiveEq,
                leftObjectEq, rightObjectEq, Bind.bind, Except.bind]
              exact .error (.same _)

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

/-- Reference-count increments on related published values either preserve
the runtime relation or fail with related faults. -/
theorem ShadowRuntimeRel.incValueBoth_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject) :
    ExceptRel (RuntimeFaultRel rho)
      (fun leftResult rightResult =>
        ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra)
      (incValue left leftObject amount check)
      (incValue right rightObject amount check) := by
  cases objects with
  | tagged payload =>
      cases check with
      | false => exact .error (.same _)
      | true => exact .ok related
  | usize value => exact .error (.same _)
  | scalar value => exact .error (.same _)
  | erased => exact .error (.same _)
  | reuseNone => exact .error (.same _)
  | reuseSome mapping => exact .error (.same _)
  | @heap leftLocation rightLocation mapping =>
      have leftReachable : Reachable left.heap
          (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ objectRoot)
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have liveEq := cells.2.2.1
      cases rightLiveEq : rightCell.live with
      | false =>
          have leftLiveEq : leftCell.live = false := by
            simpa [rightLiveEq] using liveEq
          simp [incValue, incLocation, getLiveCell, leftFound, rightFound,
            leftLiveEq, rightLiveEq, Bind.bind, Except.bind]
          exact .error (.deadObject mapping)
      | true =>
          have leftLiveEq : leftCell.live = true := by
            simpa [rightLiveEq] using liveEq
          rcases related.incLocationBoth mapping leftReachable leftFound
              leftLiveEq amount with
            ⟨leftResult, rightResult, leftEffect, rightEffect, next⟩
          rw [show incValue left (.object (.heap leftLocation)) amount check =
              incLocation left leftLocation amount by rfl,
            show incValue right (.object (.heap rightLocation)) amount check =
              incLocation right rightLocation amount by rfl,
            leftEffect, rightEffect]
          exact .ok next

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

/-- Number of currently live semantic heap entries. Recursive release strictly
decreases this measure before descending into owned children. -/
def liveCellCount : Heap → Nat
  | [] => 0
  | (_, cell) :: rest =>
      (if cell.live then 1 else 0) + liveCellCount rest

theorem liveCellCount_le_length (heap : Heap) :
    liveCellCount heap ≤ heap.length := by
  induction heap with
  | nil => exact Nat.zero_le 0
  | cons entry rest ih =>
      obtain ⟨location, cell⟩ := entry
      simp only [liveCellCount, List.length_cons]
      cases cell.live <;> simp <;> omega

/-- Replacing the first matching heap entry exchanges exactly the liveness
contribution of the old and new cells. -/
theorem replaceCell_liveCellCount
    (found : findCell? before location = some current)
    (replaced : replaceCell before location replacement = some after) :
    liveCellCount after + (if current.live then 1 else 0) =
      liveCellCount before + (if replacement.live then 1 else 0) := by
  induction before generalizing after with
  | nil => simp [findCell?] at found
  | cons entry rest recurse =>
      obtain ⟨candidate, cell⟩ := entry
      by_cases here : candidate = location
      · subst candidate
        simp [findCell?] at found
        subst current
        simp [replaceCell] at replaced
        subst after
        simp only [liveCellCount]
        omega
      · have tailFound : findCell? rest location = some current := by
          simpa [findCell?, here] using found
        generalize tailEq :
          replaceCell rest location replacement = tailResult at replaced
        cases tailResult with
        | none => simp [replaceCell, here, tailEq] at replaced
        | some tailAfter =>
            simp [replaceCell, here, tailEq] at replaced
            subst after
            have tailCount := recurse tailFound tailEq
            simp only [liveCellCount]
            omega

/-- Runtime-level form of `replaceCell_liveCellCount`. -/
theorem setCell_liveCellCount
    (found : findCell? runtime.heap location = some current)
    (effect : setCell runtime location replacement = .ok result) :
    liveCellCount result.heap + (if current.live then 1 else 0) =
      liveCellCount runtime.heap + (if replacement.live then 1 else 0) := by
  unfold setCell at effect
  generalize replacedEq :
    replaceCell runtime.heap location replacement = replaced at effect
  cases replaced with
  | none => simp at effect
  | some heap =>
      simp only at effect
      cases effect
      exact replaceCell_liveCellCount found replacedEq

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

/-- Successful recursive release never increases the number of live heap
entries. -/
theorem decLocationFuel_liveCellCount_le
    (operation : decLocationFuel fuel runtime location = .ok result) :
    liveCellCount result.heap ≤ liveCellCount runtime.heap := by
  induction fuel generalizing runtime result location with
  | zero =>
      simp [decLocationFuel] at operation
  | succ fuel recurse =>
      generalize cellEq : getLiveCell runtime location = cellResult
      cases cellResult with
      | error fault =>
          simp [decLocationFuel, cellEq, Bind.bind, Except.bind] at operation
      | ok cell =>
          rcases getLiveCell_spec cellEq with ⟨found, live⟩
          by_cases persistent : cell.persistent = true
          · have noop :
                decLocationFuel (fuel + 1) runtime location = .ok runtime := by
              simp only [decLocationFuel, cellEq, Bind.bind, Except.bind]
              rw [if_pos persistent]
              rfl
            rw [noop] at operation
            have resultEq := Except.ok.inj operation
            subst result
            exact Nat.le_refl _
          · by_cases zero : cell.rc = 0
            · simp [decLocationFuel, cellEq, Bind.bind, Except.bind,
                persistent, zero] at operation
            · by_cases above : 1 < cell.rc
              · have count := setCell_liveCellCount found
                  (by simpa [decLocationFuel, cellEq, Bind.bind, Except.bind,
                    persistent, zero, above] using operation)
                simp [live] at count
                omega
              · simp only [decLocationFuel, cellEq, Bind.bind,
                  Except.bind] at operation
                rw [if_neg persistent, if_neg zero, if_neg above] at operation
                generalize parentEq :
                  setCell runtime location { cell with rc := 0, live := false } =
                    parentResult at operation
                cases parentResult with
                | error fault =>
                    simp [parentEq] at operation
                | ok parent =>
                    dsimp only at operation
                    have parentCount := setCell_liveCellCount found parentEq
                    simp [live] at parentCount
                    have foldLe : ∀ (values : List Value)
                        (before after : RuntimeState),
                        values.foldlM (init := before) (fun next value =>
                          match value with
                          | .object (.heap child) =>
                              decLocationFuel fuel next child
                          | _ => .ok next) = .ok after →
                        liveCellCount after.heap ≤
                          liveCellCount before.heap := by
                      intro values
                      induction values with
                      | nil =>
                          intro before after folded
                          have same := Except.ok.inj folded
                          subst after
                          exact Nat.le_refl _
                      | cons value values tailIH =>
                          intro before after folded
                          simp only [List.foldlM_cons, Bind.bind,
                            Except.bind] at folded
                          cases value with
                          | object reference =>
                              cases reference with
                              | tagged payload =>
                                  exact tailIH before after folded
                              | heap child =>
                                  dsimp only at folded
                                  cases childEq :
                                      decLocationFuel fuel before child with
                                  | error fault =>
                                      rw [childEq] at folded
                                      contradiction
                                  | ok middle =>
                                      rw [childEq] at folded
                                      exact Nat.le_trans (tailIH middle after folded)
                                        (recurse childEq)
                          | usize | scalar | erased | reuseToken =>
                              exact tailIH before after folded
                    rw [← Array.foldlM_toList] at operation
                    have finalLe := foldLe cell.object.ownedValues.toList
                      parent result operation
                    omega

/-- Any successful recursive release can be replayed with every budget that
strictly dominates the current number of live heap cells. This is the
fuel-adequacy theorem needed to forget unreachable allocations. -/
theorem decLocationFuel_ok_of_liveCellCount_lt
    (enough : liveCellCount runtime.heap < fuel)
    (operation : decLocationFuel more runtime location = .ok result) :
    decLocationFuel fuel runtime location = .ok result := by
  generalize countEq : liveCellCount runtime.heap = count at enough
  induction count using Nat.strongRecOn generalizing
      fuel more runtime result location with
  | ind count smaller =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases more with
          | zero =>
              simp [decLocationFuel] at operation
          | succ more =>
              generalize cellEq :
                getLiveCell runtime location = cellResult at operation ⊢
              cases cellResult with
              | error fault =>
                  simp [decLocationFuel, cellEq, Bind.bind, Except.bind]
                    at operation
              | ok cell =>
                  rcases getLiveCell_spec cellEq with ⟨found, live⟩
                  by_cases persistent : cell.persistent = true
                  · have sourceNoop :
                        decLocationFuel (more + 1) runtime location =
                          .ok runtime := by
                      simp only [decLocationFuel, cellEq, Bind.bind,
                        Except.bind]
                      rw [if_pos persistent]
                      rfl
                    rw [sourceNoop] at operation
                    have resultEq := Except.ok.inj operation
                    subst result
                    simp only [decLocationFuel, cellEq, Bind.bind,
                      Except.bind]
                    rw [if_pos persistent]
                    rfl
                  · by_cases zero : cell.rc = 0
                    · simp [decLocationFuel, cellEq, Bind.bind, Except.bind,
                        persistent, zero] at operation
                    · by_cases above : 1 < cell.rc
                      · simpa [decLocationFuel, cellEq, Bind.bind, Except.bind,
                          persistent, zero, above] using operation
                      · simp only [decLocationFuel, cellEq, Bind.bind,
                          Except.bind] at operation ⊢
                        rw [if_neg persistent, if_neg zero, if_neg above]
                          at operation ⊢
                        generalize parentEq :
                          setCell runtime location
                              { cell with rc := 0, live := false } =
                            parentResult at operation ⊢
                        cases parentResult with
                        | error fault =>
                            simp at operation
                        | ok parent =>
                            dsimp only at operation ⊢
                            have parentCount :=
                              setCell_liveCellCount found parentEq
                            simp [live] at parentCount
                            have parentLtCount :
                                liveCellCount parent.heap < count := by
                              rw [← countEq]
                              omega
                            have parentLtFuel :
                                liveCellCount parent.heap < fuel := by
                              omega
                            have foldCap : ∀ (values : List Value)
                                (before after : RuntimeState),
                                liveCellCount before.heap < count →
                                liveCellCount before.heap < fuel →
                                values.foldlM (init := before)
                                    (fun next value =>
                                  match value with
                                  | .object (.heap child) =>
                                      decLocationFuel more next child
                                  | _ => .ok next) = .ok after →
                                values.foldlM (init := before)
                                    (fun next value =>
                                  match value with
                                  | .object (.heap child) =>
                                      decLocationFuel fuel next child
                                  | _ => .ok next) = .ok after := by
                              intro values
                              induction values with
                              | nil =>
                                  intro before after _ _ folded
                                  simpa using folded
                              | cons value values tailIH =>
                                  intro before after beforeLtCount beforeLtFuel folded
                                  simp only [List.foldlM_cons, Bind.bind,
                                    Except.bind] at folded ⊢
                                  cases value with
                                  | object reference =>
                                      cases reference with
                                      | tagged payload =>
                                          exact tailIH before after beforeLtCount
                                            beforeLtFuel folded
                                      | heap child =>
                                          dsimp only at folded ⊢
                                          cases childEq :
                                              decLocationFuel more before child with
                                          | error fault =>
                                              rw [childEq] at folded
                                              contradiction
                                          | ok middle =>
                                              rw [childEq] at folded
                                              have childCapped :=
                                                smaller
                                                  (liveCellCount before.heap)
                                                  beforeLtCount
                                                  (runtime := before)
                                                  (result := middle)
                                                  (location := child)
                                                  (fuel := fuel)
                                                  (more := more)
                                                  childEq rfl beforeLtFuel
                                              rw [childCapped]
                                              have middleLe :=
                                                decLocationFuel_liveCellCount_le
                                                  childEq
                                              exact tailIH middle after
                                                (Nat.lt_of_le_of_lt middleLe
                                                  beforeLtCount)
                                                (Nat.lt_of_le_of_lt middleLe
                                                  beforeLtFuel)
                                                folded
                                  | usize | scalar | erased | reuseToken =>
                                      exact tailIH before after beforeLtCount
                                        beforeLtFuel folded
                            rw [← Array.foldlM_toList] at operation ⊢
                            exact foldCap cell.object.ownedValues.toList
                              parent result parentLtCount parentLtFuel operation

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

/-- Public recursive release is independent of the two heaps' unreachable
allocation counts: simulate at the source budget, then replay the successful
target run at its own adequate public budget. -/
theorem ShadowRuntimeRel.decLocationBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (mapping : rho.forward leftLocation = some rightLocation)
    (leftReachable :
      Reachable left.heap (runtimeRoots left leftExtra) leftLocation)
    (sourceEffect : decLocation left leftLocation = .ok leftResult) :
    ∃ rightResult,
      decLocation right rightLocation = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  unfold decLocation at sourceEffect
  rcases related.decLocationFuelBoth mapping leftReachable sourceEffect with
    ⟨rightResult, sameFuel, next⟩
  have adequate :
      liveCellCount right.heap < right.heap.length + 1 := by
    have bounded := liveCellCount_le_length right.heap
    omega
  have publicEffect := decLocationFuel_ok_of_liveCellCount_lt
    adequate sameFuel
  exact ⟨rightResult, by simpa [decLocation] using publicEffect, next⟩

/-- One public decrement on a related operand preserves the runtime relation.
Checked tagged references and persistent heap cells are synchronized no-ops. -/
theorem ShadowRuntimeRel.decValueOnceBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceEffect : decValueOnce left leftObject check = .ok leftResult) :
    ∃ rightResult,
      decValueOnce right rightObject check = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  cases objects with
  | tagged payload =>
      cases check with
      | false => simp [decValueOnce] at sourceEffect
      | true =>
          simp [decValueOnce] at sourceEffect
          subst leftResult
          exact ⟨right, by simp [decValueOnce], related⟩
  | usize value => simp [decValueOnce] at sourceEffect
  | scalar value => simp [decValueOnce] at sourceEffect
  | erased => simp [decValueOnce] at sourceEffect
  | reuseNone => simp [decValueOnce] at sourceEffect
  | reuseSome mapping => simp [decValueOnce] at sourceEffect
  | heap mapping =>
      rename_i leftLocation rightLocation
      have reachable :
          Reachable left.heap (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra
          (.object (.heap leftLocation)) objectRoot)
      rcases related.decLocationBoth mapping reachable
          (by simpa [decValueOnce] using sourceEffect) with
        ⟨rightResult, targetEffect, next⟩
      exact ⟨rightResult, by simpa [decValueOnce] using targetEffect, next⟩

/-- Repeating a related public decrement preserves the relation after every
successful source iteration. -/
theorem ShadowRuntimeRel.decValueBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceEffect :
      decValue left leftObject amount check = .ok leftResult) :
    ∃ rightResult,
      decValue right rightObject amount check = .ok rightResult ∧
      ShadowRuntimeRel rho leftResult rightResult leftExtra rightExtra := by
  induction amount generalizing left right leftResult with
  | zero =>
      have sourceNoop : decValue left leftObject 0 check = .ok left := by
        rfl
      rw [sourceNoop] at sourceEffect
      have resultEq := Except.ok.inj sourceEffect
      subst leftResult
      exact ⟨right, by rfl, related⟩
  | succ amount recurse =>
      simp only [decValue, List.replicate_succ, List.foldlM_cons,
        Bind.bind, Except.bind] at sourceEffect ⊢
      cases firstEffect :
          decValueOnce left leftObject check with
      | error fault =>
          rw [firstEffect] at sourceEffect
          contradiction
      | ok middleLeft =>
          rw [firstEffect] at sourceEffect
          rcases related.decValueOnceBoth_of_related objectRoot objects
              firstEffect with
            ⟨middleRight, targetFirst, middleRelated⟩
          rw [targetFirst]
          exact recurse middleRelated sourceEffect

/-- Retained reset follows the same ownership branch on related published
objects. Shared objects perform the paired public decrement; unique
constructors clear related prefixes and release the removed fields
left-to-right before returning mapped reuse tokens. -/
theorem ShadowRuntimeRel.resetBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (objectRoot : leftObject ∈ leftExtra)
    (objects : ValueRel rho leftObject rightObject)
    (sourceEffect :
      reset left count leftObject = .ok (leftResult, leftToken)) :
    ∃ rightResult rightToken,
      reset right count rightObject = .ok (rightResult, rightToken) ∧
      ValueRel rho leftToken rightToken ∧
      ShadowRuntimeRel rho leftResult rightResult
        (leftToken :: leftExtra) (rightToken :: rightExtra) := by
  cases objects with
  | tagged payload =>
      have pairEq := Except.ok.inj sourceEffect
      have runtimeEq := congrArg Prod.fst pairEq
      have tokenEq := congrArg Prod.snd pairEq
      simp [reset] at runtimeEq tokenEq
      subst leftResult
      subst leftToken
      exact ⟨right, .reuseToken none, by simp [reset], .reuseNone,
        related.prependNonHeap .reuseNone
          (by intro location; simp) (by intro location; simp)⟩
  | usize value => simp [reset] at sourceEffect
  | scalar value => simp [reset] at sourceEffect
  | erased => simp [reset] at sourceEffect
  | reuseNone => simp [reset] at sourceEffect
  | reuseSome mapping => simp [reset] at sourceEffect
  | @heap leftLocation rightLocation mapping =>
      have leftReachable :
          Reachable left.heap (runtimeRoots left leftExtra) leftLocation := by
        exact .root (extra_subset_runtimeRoots left leftExtra _ objectRoot)
      have rightReachable :
          Reachable right.heap (runtimeRoots right rightExtra) rightLocation := by
        rcases reachable_forward related.roots related.heap
            leftReachable with
          ⟨mappedLocation, mappedEq, reachable⟩
        have locationEq : mappedLocation = rightLocation := by
          rw [mapping] at mappedEq
          exact (Option.some.inj mappedEq).symm
        simpa [locationEq] using reachable
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      cases leftLiveEq : leftCell.live with
      | false =>
          simp [reset, getLiveCell, leftFound, leftLiveEq,
            Bind.bind, Except.bind] at sourceEffect
      | true =>
          have rightLiveEq : rightCell.live = true := by
            rw [← cells.2.2.1]
            exact leftLiveEq
          have leftGet :
              getLiveCell left leftLocation = .ok leftCell := by
            simp [getLiveCell, leftFound, leftLiveEq]
          have rightGet :
              getLiveCell right rightLocation = .ok rightCell := by
            simp [getLiveCell, rightFound, rightLiveEq]
          have persistentEq :
              leftCell.persistent = rightCell.persistent := cells.2.1
          have rcEq : leftCell.rc = rightCell.rc := cells.1
          cases leftSharedEq :
              (leftCell.persistent || leftCell.rc != 1) with
          | true =>
              have rightSharedEq :
                  (rightCell.persistent || rightCell.rc != 1) = true := by
                simpa [← persistentEq, ← rcEq] using leftSharedEq
              have source := sourceEffect
              simp only [reset, leftGet, Bind.bind, Except.bind] at source
              rw [if_pos (by simpa using leftSharedEq)] at source
              generalize leftDecEq :
                  decLocation left leftLocation = leftDecResult at source
              cases leftDecResult with
              | error fault =>
                  contradiction
              | ok computedLeft =>
                  have pairEq := Except.ok.inj source
                  have runtimeEq := congrArg Prod.fst pairEq
                  have tokenEq := congrArg Prod.snd pairEq
                  simp at runtimeEq tokenEq
                  subst leftResult
                  subst leftToken
                  rcases related.decLocationBoth mapping leftReachable
                      leftDecEq with
                    ⟨rightResult, rightDecEq, next⟩
                  have targetEffect :
                      reset right count (.object (.heap rightLocation)) =
                        .ok (rightResult, .reuseToken none) := by
                    simp only [reset, rightGet, Bind.bind, Except.bind]
                    rw [if_pos (by simpa using rightSharedEq)]
                    rw [rightDecEq]
                    rfl
                  exact ⟨rightResult, .reuseToken none, targetEffect,
                    .reuseNone,
                    next.prependNonHeap .reuseNone
                      (by intro location; simp)
                      (by intro location; simp)⟩
          | false =>
              have rightSharedEq :
                  (rightCell.persistent || rightCell.rc != 1) = false := by
                simpa [← persistentEq, ← rcEq] using leftSharedEq
              have heapObjects := cells.2.2.2
              generalize leftObjectEq :
                leftCell.object = leftHeapObject at heapObjects
              generalize rightObjectEq :
                rightCell.object = rightHeapObject at heapObjects
              cases heapObjects with
              | @ctor leftConstructor rightConstructor tag fields usizes
                  scalars =>
                  by_cases tooMany :
                      count > leftConstructor.objectFields.size
                  · have source := sourceEffect
                    simp only [reset, leftGet, Bind.bind, Except.bind]
                      at source
                    rw [if_neg (by simpa using leftSharedEq)] at source
                    rw [leftObjectEq] at source
                    simp only at source
                    rw [if_pos tooMany] at source
                    simp at source
                  · have sizeEq :
                        leftConstructor.objectFields.size =
                          rightConstructor.objectFields.size :=
                      arrayRel_size_eq fields
                    have rightTooMany :
                        ¬count > rightConstructor.objectFields.size := by
                      rw [← sizeEq]
                      exact tooMany
                    let leftReleased :=
                      leftConstructor.objectFields.extract 0 count
                    let rightReleased :=
                      rightConstructor.objectFields.extract 0 count
                    let leftCleared :=
                      leftConstructor.objectFields.mapIdx fun index field =>
                        if index < count then .object (.tagged 0) else field
                    let rightCleared :=
                      rightConstructor.objectFields.mapIdx fun index field =>
                        if index < count then .object (.tagged 0) else field
                    have releasedFields :
                        ArrayRel (ValueRel rho)
                          leftReleased rightReleased := by
                      exact arrayRel_extract fields 0 count
                    have clearedFields :
                        ArrayRel (ValueRel rho)
                          leftCleared rightCleared := by
                      exact arrayRel_mapIdx_replacePrefix fields (.tagged 0)
                        count
                    let leftReplacement : HeapCell :=
                      { leftCell with object := .ctor {
                          leftConstructor with
                          objectFields := leftCleared } }
                    let rightReplacement : HeapCell :=
                      { rightCell with object := .ctor {
                          rightConstructor with
                          objectFields := rightCleared } }
                    have replacement :
                        HeapCellRel rho leftReplacement rightReplacement := by
                      refine ⟨cells.1, cells.2.1, cells.2.2.1, ?_⟩
                      dsimp only [leftReplacement, rightReplacement]
                      exact @HeapObjectRel.ctor rho
                        { leftConstructor with objectFields := leftCleared }
                        { rightConstructor with objectFields := rightCleared }
                        tag clearedFields usizes scalars
                    have published := related.publishOwnedValues
                      leftReachable rightReachable leftFound rightFound cells
                    have leftOwned : ∀ {child},
                        Value.object (.heap child) ∈
                            leftReplacement.object.ownedValues.toList →
                          Value.object (.heap child) ∈
                              leftCell.object.ownedValues.toList ∨
                            Reachable left.heap
                              (runtimeRoots left
                                (leftCell.object.ownedValues.toList ++
                                  leftExtra)) child := by
                      intro child member
                      left
                      have clearedMember :
                          Value.object (.heap child) ∈ leftCleared.toList := by
                        simpa [leftReplacement, HeapObject.ownedValues] using
                          member
                      have oldMember :=
                        heap_mem_of_mem_clearPrefix
                          leftConstructor.objectFields clearedMember
                      simpa [leftObjectEq, HeapObject.ownedValues] using
                        oldMember
                    have rightOwned : ∀ {child},
                        Value.object (.heap child) ∈
                            rightReplacement.object.ownedValues.toList →
                          Value.object (.heap child) ∈
                              rightCell.object.ownedValues.toList ∨
                            Reachable right.heap
                              (runtimeRoots right
                                (rightCell.object.ownedValues.toList ++
                                  rightExtra)) child := by
                      intro child member
                      left
                      have clearedMember :
                          Value.object (.heap child) ∈ rightCleared.toList := by
                        simpa [rightReplacement, HeapObject.ownedValues] using
                          member
                      have oldMember :=
                        heap_mem_of_mem_clearPrefix
                          rightConstructor.objectFields clearedMember
                      simpa [rightObjectEq, HeapObject.ownedValues] using
                        oldMember
                    rcases published.setCellBothRooted mapping leftFound
                        rightFound leftOwned rightOwned replacement with
                      ⟨leftParent, rightParent, leftSet, rightSet,
                        parentRelated⟩
                    let release (runtime : RuntimeState) (field : Value) :=
                      decValueOnce runtime field true
                    have source := sourceEffect
                    simp only [reset, leftGet, Bind.bind, Except.bind]
                      at source
                    rw [if_neg (by simpa using leftSharedEq)] at source
                    rw [leftObjectEq] at source
                    simp only at source
                    rw [if_neg tooMany] at source
                    have leftSetRaw :
                        setCell left leftLocation
                            { leftCell with object := .ctor {
                                leftConstructor with objectFields :=
                                  (Array.mapIdx
                                    (fun index field =>
                                      if index < count then
                                        .object (.tagged 0)
                                      else field)
                                    leftConstructor.objectFields) } } =
                          .ok leftParent := by
                      simpa [leftReplacement, leftCleared] using leftSet
                    rw [leftSetRaw] at source
                    simp only at source
                    generalize leftFoldEq :
                        Array.foldlM
                            (fun runtime field =>
                              decValueOnce runtime field true)
                            leftParent
                            (leftConstructor.objectFields.extract 0 count) =
                          leftFoldResult at source
                    cases leftFoldResult with
                    | error fault =>
                        contradiction
                    | ok computedLeft =>
                        have pairEq := Except.ok.inj source
                        have runtimeEq := congrArg Prod.fst pairEq
                        have tokenEq := congrArg Prod.snd pairEq
                        simp at runtimeEq tokenEq
                        subst leftResult
                        subst leftToken
                        have foldBoth : ∀
                            {leftValues rightValues : List Value}
                            {beforeLeft beforeRight afterLeft : RuntimeState},
                            ListRel (ValueRel rho) leftValues rightValues →
                            RootSubset leftValues
                              leftCell.object.ownedValues.toList →
                            RootSubset rightValues
                              rightCell.object.ownedValues.toList →
                            ShadowRuntimeRel rho beforeLeft beforeRight
                              (leftCell.object.ownedValues.toList ++ leftExtra)
                              (rightCell.object.ownedValues.toList ++
                                rightExtra) →
                            leftValues.foldlM
                                (init := beforeLeft) release =
                              .ok afterLeft →
                            ∃ afterRight,
                              rightValues.foldlM
                                  (init := beforeRight) release =
                                .ok afterRight ∧
                              ShadowRuntimeRel rho afterLeft afterRight
                                (leftCell.object.ownedValues.toList ++
                                  leftExtra)
                                (rightCell.object.ownedValues.toList ++
                                  rightExtra) := by
                          intro leftValues rightValues beforeLeft beforeRight
                            afterLeft values leftSubset rightSubset states
                            operation
                          induction values generalizing beforeLeft beforeRight
                              afterLeft with
                          | nil =>
                              simp only [List.foldlM_nil] at operation ⊢
                              have stateEq := Except.ok.inj operation
                              subst afterLeft
                              exact ⟨beforeRight, rfl, states⟩
                          | @cons leftHead rightHead leftTail rightTail heads
                              tails recurse =>
                              have leftTailSubset : RootSubset leftTail
                                  leftCell.object.ownedValues.toList := by
                                intro value member
                                exact leftSubset value
                                  (List.mem_cons_of_mem leftHead member)
                              have rightTailSubset : RootSubset rightTail
                                  rightCell.object.ownedValues.toList := by
                                intro value member
                                exact rightSubset value
                                  (List.mem_cons_of_mem rightHead member)
                              simp only [List.foldlM_cons, Bind.bind,
                                Except.bind] at operation ⊢
                              simp only [release] at operation ⊢
                              cases headEffect :
                                  decValueOnce beforeLeft leftHead true with
                              | error fault =>
                                  rw [headEffect] at operation
                                  contradiction
                              | ok middleLeft =>
                                  rw [headEffect] at operation
                                  have headRoot :
                                      leftHead ∈
                                        leftCell.object.ownedValues.toList ++
                                          leftExtra :=
                                    List.mem_append_left _
                                      (leftSubset _ List.mem_cons_self)
                                  rcases states
                                      |>.decValueOnceBoth_of_related
                                        headRoot heads headEffect with
                                    ⟨middleRight, targetHead, middleStates⟩
                                  rw [targetHead]
                                  exact recurse leftTailSubset
                                    rightTailSubset middleStates operation
                        have leftSubset : RootSubset leftReleased.toList
                            leftCell.object.ownedValues.toList := by
                          intro value member
                          have oldMember :=
                            array_mem_of_mem_extract
                              leftConstructor.objectFields member
                          simpa [leftObjectEq, HeapObject.ownedValues] using
                            oldMember
                        have rightSubset : RootSubset rightReleased.toList
                            rightCell.object.ownedValues.toList := by
                          intro value member
                          have oldMember :=
                            array_mem_of_mem_extract
                              rightConstructor.objectFields member
                          simpa [rightObjectEq, HeapObject.ownedValues] using
                            oldMember
                        have sourceFoldList :
                            leftReleased.toList.foldlM
                                (init := leftParent) release =
                              .ok computedLeft := by
                          simpa only [leftReleased, release,
                            Array.foldlM_toList] using leftFoldEq
                        rcases foldBoth releasedFields leftSubset rightSubset
                            parentRelated sourceFoldList with
                          ⟨rightResult, rightFoldList, finalPublished⟩
                        have rightFold :
                            Array.foldlM release rightParent rightReleased =
                              .ok rightResult := by
                          simpa only [Array.foldlM_toList] using rightFoldList
                        have rightSetRaw :
                            setCell right rightLocation
                                { rightCell with object := .ctor {
                                    rightConstructor with objectFields :=
                                      (Array.mapIdx
                                        (fun index field =>
                                          if index < count then
                                            .object (.tagged 0)
                                          else field)
                                        rightConstructor.objectFields) } } =
                              .ok rightParent := by
                          simpa [rightReplacement, rightCleared] using rightSet
                        have rightFoldRaw :
                            Array.foldlM
                                (fun runtime field =>
                                  decValueOnce runtime field true)
                                rightParent
                                (rightConstructor.objectFields.extract
                                  0 count) =
                              .ok rightResult := by
                          simpa only [rightReleased, release] using rightFold
                        have targetEffect :
                            reset right count
                                (.object (.heap rightLocation)) =
                              .ok (rightResult,
                                .reuseToken (some rightLocation)) := by
                          simp only [reset, rightGet, Bind.bind, Except.bind]
                          rw [if_neg (by simpa using rightSharedEq)]
                          rw [rightObjectEq]
                          simp only
                          rw [if_neg rightTooMany]
                          rw [rightSetRaw]
                          simp only
                          rw [rightFoldRaw]
                          rfl
                        have restricted :=
                          finalPublished.restrictExtra related.extra
                            (by
                              intro value member
                              exact List.mem_append_right _ member)
                            (by
                              intro value member
                              exact List.mem_append_right _ member)
                        exact ⟨rightResult,
                          .reuseToken (some rightLocation), targetEffect,
                          .reuseSome mapping,
                          restricted.prependNonHeap (.reuseSome mapping)
                            (by intro location; simp)
                            (by intro location; simp)⟩
              | closure fixed =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect
              | boxed value =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect
              | string value =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect
              | natural value =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect
              | integer value =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect
              | byteArray value =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect
              | «opaque» value =>
                  simp [reset, leftGet, leftSharedEq, leftObjectEq,
                    Bind.bind, Except.bind] at sourceEffect

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

/-- Evaluating the same literal in related runtimes produces related values.
Immediate literals preserve the current address renaming; heap-backed
literals allocate a fresh related pair and extend it. -/
theorem ShadowRuntimeRel.literalBoth
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (literalValue : LCNF.LitValue) :
    ∃ larger,
      RenamingExtends rho larger ∧
      ValueRel larger (literal left literalValue).2
        (literal right literalValue).2 ∧
      ShadowRuntimeRel larger
        (literal left literalValue).1 (literal right literalValue).1
        ((literal left literalValue).2 :: leftExtra)
        ((literal right literalValue).2 :: rightExtra) := by
  cases literalValue with
  | nat value =>
      by_cases small : value ≤ maxTaggedPayload
      · refine ⟨rho, RenamingExtends.refl rho, ?_, ?_⟩
        · simpa [literal, small] using
            (ValueRel.tagged (rho := rho) (UInt64.ofNat value))
        · simpa [literal, small] using related.prependNonHeap
            (ValueRel.tagged (rho := rho) (UInt64.ofNat value))
            (by intro location; simp) (by intro location; simp)
      · rcases related.allocBoth (HeapObjectRel.natural value)
            (by simp [RootSubset, HeapObject.ownedValues])
            (by simp [RootSubset, HeapObject.ownedValues]) false with
          ⟨larger, extension, values, runtime⟩
        exact ⟨larger, extension,
          by simpa [literal, small] using values,
          by simpa [literal, small] using runtime⟩
  | str value =>
      rcases related.allocBoth (HeapObjectRel.string value)
            (by simp [RootSubset, HeapObject.ownedValues])
            (by simp [RootSubset, HeapObject.ownedValues]) false with
        ⟨larger, extension, values, runtime⟩
      exact ⟨larger, extension,
        by simpa [literal] using values,
        by simpa [literal] using runtime⟩
  | uint8 value =>
      refine ⟨rho, RenamingExtends.refl rho, ?_, ?_⟩
      · exact .scalar (.uint8 value)
      · simpa [literal] using related.prependNonHeap
          (ValueRel.scalar (rho := rho) (.uint8 value))
          (by intro location; simp) (by intro location; simp)
  | uint16 value =>
      refine ⟨rho, RenamingExtends.refl rho, ?_, ?_⟩
      · exact .scalar (.uint16 value)
      · simpa [literal] using related.prependNonHeap
          (ValueRel.scalar (rho := rho) (.uint16 value))
          (by intro location; simp) (by intro location; simp)
  | uint32 value =>
      refine ⟨rho, RenamingExtends.refl rho, ?_, ?_⟩
      · exact .scalar (.uint32 value)
      · simpa [literal] using related.prependNonHeap
          (ValueRel.scalar (rho := rho) (.uint32 value))
          (by intro location; simp) (by intro location; simp)
  | uint64 value =>
      refine ⟨rho, RenamingExtends.refl rho, ?_, ?_⟩
      · exact .scalar (.uint64 value)
      · simpa [literal] using related.prependNonHeap
          (ValueRel.scalar (rho := rho) (.uint64 value))
          (by intro location; simp) (by intro location; simp)
  | usize value =>
      refine ⟨rho, RenamingExtends.refl rho, ?_, ?_⟩
      · exact .usize value
      · simpa [literal] using related.prependNonHeap
          (ValueRel.usize (rho := rho) value)
          (by intro location; simp) (by intro location; simp)

/-- Boxing related published scalar inputs produces related retained values.
Small payloads remain identical tagged objects; large payloads allocate a
fresh related pair and extend the address renaming. -/
theorem ShadowRuntimeRel.boxBoth_of_related
    (related : ShadowRuntimeRel rho left right leftExtra rightExtra)
    (leftMember : leftValue ∈ leftExtra)
    (values : ValueRel rho leftValue rightValue)
    (sourceBox : box left type leftValue = .ok (leftRuntime, leftResult)) :
    ∃ larger rightRuntime rightResult,
      RenamingExtends rho larger ∧
      box right type rightValue = .ok (rightRuntime, rightResult) ∧
      ValueRel larger leftResult rightResult ∧
      ShadowRuntimeRel larger leftRuntime rightRuntime
        (leftResult :: leftExtra) (rightResult :: rightExtra) := by
  cases values with
  | tagged payload => simp [box, Bind.bind, Except.bind] at sourceBox
  | erased => simp [box, Bind.bind, Except.bind] at sourceBox
  | reuseNone => simp [box, Bind.bind, Except.bind] at sourceBox
  | reuseSome mapped => simp [box, Bind.bind, Except.bind] at sourceBox
  | heap mapped => simp [box, Bind.bind, Except.bind] at sourceBox
  | scalar scalar =>
      have rightMember : Value.scalar scalar ∈ rightExtra := by
        rcases listRel_exists_right_of_mem related.extra leftMember with
          ⟨target, targetMember, targetRelated⟩
        cases targetRelated
        exact targetMember
      by_cases small : scalar.toUInt64.toNat ≤ maxTaggedPayload
      · have normalized := sourceBox
        simp [box, small, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at normalized
        rcases normalized with ⟨resultEq, runtimeEq⟩
        subst leftResult
        subst leftRuntime
        refine ⟨rho, right, .object (.tagged scalar.toUInt64),
          .refl rho, ?_, .tagged _, ?_⟩
        · simp [box, small, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
        · exact related.prependNonHeap (.tagged _)
            (by intro location; simp) (by intro location; simp)
      · let leftObject : HeapObject := .boxed type (.scalar scalar)
        let rightObject : HeapObject := .boxed type (.scalar scalar)
        have objects : HeapObjectRel rho leftObject rightObject := by
          exact .boxed (.scalar scalar)
        have leftOwned : RootSubset leftObject.ownedValues.toList
            (runtimeRoots left leftExtra) := by
          intro value member
          have same : value = .scalar scalar := by
            simpa [leftObject, HeapObject.ownedValues] using member
          subst value
          exact extra_subset_runtimeRoots left leftExtra _ leftMember
        have rightOwned : RootSubset rightObject.ownedValues.toList
            (runtimeRoots right rightExtra) := by
          intro value member
          have same : value = .scalar scalar := by
            simpa [rightObject, HeapObject.ownedValues] using member
          subst value
          exact extra_subset_runtimeRoots right rightExtra _ rightMember
        rcases related.allocBoth objects leftOwned rightOwned false with
          ⟨larger, extension, resultValues, nextRuntime⟩
        have normalized := sourceBox
        simp [box, small, leftObject, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at normalized
        rcases normalized with ⟨resultEq, runtimeEq⟩
        subst leftResult
        subst leftRuntime
        exact ⟨larger, (alloc right rightObject).1,
          .object (alloc right rightObject).2, extension,
          by simp [box, small, rightObject, Bind.bind, Except.bind,
            Pure.pure, Except.pure],
          resultValues, nextRuntime⟩
  | usize word =>
      have rightMember : Value.usize word ∈ rightExtra := by
        rcases listRel_exists_right_of_mem related.extra leftMember with
          ⟨target, targetMember, targetRelated⟩
        cases targetRelated
        exact targetMember
      by_cases small : word.toNat ≤ maxTaggedPayload
      · have normalized := sourceBox
        simp [box, small, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at normalized
        rcases normalized with ⟨resultEq, runtimeEq⟩
        subst leftResult
        subst leftRuntime
        refine ⟨rho, right, .object (.tagged word),
          .refl rho, ?_, .tagged _, ?_⟩
        · simp [box, small, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
        · exact related.prependNonHeap (.tagged _)
            (by intro location; simp) (by intro location; simp)
      · let leftObject : HeapObject := .boxed type (.usize word)
        let rightObject : HeapObject := .boxed type (.usize word)
        have objects : HeapObjectRel rho leftObject rightObject := by
          exact .boxed (.usize word)
        have leftOwned : RootSubset leftObject.ownedValues.toList
            (runtimeRoots left leftExtra) := by
          intro value member
          have same : value = .usize word := by
            simpa [leftObject, HeapObject.ownedValues] using member
          subst value
          exact extra_subset_runtimeRoots left leftExtra _ leftMember
        have rightOwned : RootSubset rightObject.ownedValues.toList
            (runtimeRoots right rightExtra) := by
          intro value member
          have same : value = .usize word := by
            simpa [rightObject, HeapObject.ownedValues] using member
          subst value
          exact extra_subset_runtimeRoots right rightExtra _ rightMember
        rcases related.allocBoth objects leftOwned rightOwned false with
          ⟨larger, extension, resultValues, nextRuntime⟩
        have normalized := sourceBox
        simp [box, small, leftObject, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at normalized
        rcases normalized with ⟨resultEq, runtimeEq⟩
        subst leftResult
        subst leftRuntime
        exact ⟨larger, (alloc right rightObject).1,
          .object (alloc right rightObject).2, extension,
          by simp [box, small, rightObject, Bind.bind, Except.bind,
            Pure.pure, Except.pure],
          resultValues, nextRuntime⟩

/-- Related fixed arguments allocate matching retained closures. The freshly
allocated references replace their captured arguments as direct roots because
the arguments are thereafter reachable through the closure ownership edge. -/
theorem ShadowRuntimeRel.allocClosureBoth
    (related : ShadowRuntimeRel rho left right
      (leftArguments.toList ++ leftExtra)
      (rightArguments.toList ++ rightExtra))
    (arguments : ArrayRel (ValueRel rho) leftArguments rightArguments)
    (tail : ListRel (ValueRel rho) leftExtra rightExtra)
    (arityEq : leftArity = rightArity) :
    let leftObject : HeapObject :=
      .closure name leftArity leftArguments
    let rightObject : HeapObject :=
      .closure name rightArity rightArguments
    let leftValue : Value := .object (alloc left leftObject).2
    let rightValue : Value := .object (alloc right rightObject).2
    ∃ larger,
      RenamingExtends rho larger ∧
      ValueRel larger leftValue rightValue ∧
      ShadowRuntimeRel larger
        (alloc left leftObject).1 (alloc right rightObject).1
        (leftValue :: leftExtra) (rightValue :: rightExtra) := by
  dsimp only
  let leftObject : HeapObject :=
    .closure name leftArity leftArguments
  let rightObject : HeapObject :=
    .closure name rightArity rightArguments
  have objects : HeapObjectRel rho leftObject rightObject := by
    rw [show leftObject = .closure name leftArity leftArguments from rfl]
    rw [show rightObject = .closure name rightArity rightArguments from rfl]
    rw [← arityEq]
    exact .closure arguments
  have leftOwned : RootSubset leftObject.ownedValues.toList
      (runtimeRoots left (leftArguments.toList ++ leftExtra)) := by
    intro value member
    apply extra_subset_runtimeRoots
    apply List.mem_append_left
    simpa [leftObject, HeapObject.ownedValues] using member
  have rightOwned : RootSubset rightObject.ownedValues.toList
      (runtimeRoots right (rightArguments.toList ++ rightExtra)) := by
    intro value member
    apply extra_subset_runtimeRoots
    apply List.mem_append_left
    simpa [rightObject, HeapObject.ownedValues] using member
  rcases related.allocBoth objects leftOwned rightOwned false with
    ⟨larger, extension, values, allocated⟩
  let leftValue : Value := .object (alloc left leftObject).2
  let rightValue : Value := .object (alloc right rightObject).2
  have leftSubset : RootSubset
      (leftValue :: leftExtra)
      (leftValue :: (leftArguments.toList ++ leftExtra)) := by
    intro value member
    simp only [List.mem_cons] at member ⊢
    rcases member with same | member
    · exact Or.inl same
    · exact Or.inr (List.mem_append_right _ member)
  have rightSubset : RootSubset
      (rightValue :: rightExtra)
      (rightValue :: (rightArguments.toList ++ rightExtra)) := by
    intro value member
    simp only [List.mem_cons] at member ⊢
    rcases member with same | member
    · exact Or.inl same
    · exact Or.inr (List.mem_append_right _ member)
  have nextRuntime : ShadowRuntimeRel larger
      (alloc left leftObject).1 (alloc right rightObject).1
      (leftValue :: leftExtra) (rightValue :: rightExtra) := by
    apply allocated.restrictExtra
    · exact .cons values
        (listRel_mono (valueRel_mono extension) tail)
    · exact leftSubset
    · exact rightSubset
  exact ⟨larger, extension, values, nextRuntime⟩

/-- Related constructor arguments produce related retained constructor
values.  Nullary constructors are the same immediate tag; every other shape
allocates a fresh related object, then removes the now-owned arguments from
the direct-root suffix. -/
theorem ShadowRuntimeRel.allocCtorBoth
    (related : ShadowRuntimeRel rho left right
      (leftArguments.toList ++ leftExtra)
      (rightArguments.toList ++ rightExtra))
    (arguments : ArrayRel (ValueRel rho) leftArguments rightArguments)
    (tail : ListRel (ValueRel rho) leftExtra rightExtra)
    (info : LCNF.CtorInfo)
    (arity : leftArguments.size = info.size) :
    ∃ larger leftRuntime leftValue rightRuntime rightValue,
      RenamingExtends rho larger ∧
      allocCtor left info leftArguments = .ok (leftRuntime, leftValue) ∧
      allocCtor right info rightArguments = .ok (rightRuntime, rightValue) ∧
      ValueRel larger leftValue rightValue ∧
      ShadowRuntimeRel larger leftRuntime rightRuntime
        (leftValue :: leftExtra) (rightValue :: rightExtra) := by
  have rightArity : rightArguments.size = info.size := by
    rw [← arity, arrayRel_size_eq arguments]
  by_cases empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0
  · have leftEmpty : leftArguments = #[] :=
      Array.size_eq_zero_iff.mp (arity.trans empty.1.1)
    have rightEmpty : rightArguments = #[] :=
      Array.size_eq_zero_iff.mp (rightArity.trans empty.1.1)
    have base : ShadowRuntimeRel rho left right leftExtra rightExtra := by
      simpa [leftEmpty, rightEmpty] using related
    let value : Value := .object (.tagged (UInt64.ofNat info.cidx))
    refine ⟨rho, left, value, right, value,
      RenamingExtends.refl rho, ?_, ?_, .tagged _, ?_⟩
    · simp [allocCtor, arity, empty.1.1, empty.1.2, empty.2, value,
        Pure.pure, Except.pure]
    · simp [allocCtor, rightArity, empty.1.1, empty.1.2, empty.2, value,
        Pure.pure, Except.pure]
    · exact base.prependNonHeap (.tagged _)
        (by intro location; simp [value])
        (by intro location; simp [value])
  · let leftObject : ConstructorObject := {
      tag := info.cidx
      objectFields := leftArguments
      usizeFields := Array.replicate info.usize 0
      scalarFields := []
    }
    let rightObject : ConstructorObject := {
      tag := info.cidx
      objectFields := rightArguments
      usizeFields := Array.replicate info.usize 0
      scalarFields := []
    }
    have objects : HeapObjectRel rho (.ctor leftObject) (.ctor rightObject) := by
      exact .ctor rfl arguments rfl rfl
    have leftOwned : RootSubset
        (HeapObject.ownedValues (.ctor leftObject)).toList
        (runtimeRoots left (leftArguments.toList ++ leftExtra)) := by
      intro value member
      apply extra_subset_runtimeRoots
      apply List.mem_append_left
      simpa [leftObject, HeapObject.ownedValues] using member
    have rightOwned : RootSubset
        (HeapObject.ownedValues (.ctor rightObject)).toList
        (runtimeRoots right (rightArguments.toList ++ rightExtra)) := by
      intro value member
      apply extra_subset_runtimeRoots
      apply List.mem_append_left
      simpa [rightObject, HeapObject.ownedValues] using member
    rcases related.allocBoth objects leftOwned rightOwned false with
      ⟨larger, extension, values, allocated⟩
    let leftRuntime := (alloc left (.ctor leftObject)).1
    let rightRuntime := (alloc right (.ctor rightObject)).1
    let leftValue : Value := .object (alloc left (.ctor leftObject)).2
    let rightValue : Value := .object (alloc right (.ctor rightObject)).2
    have leftSubset : RootSubset
        (leftValue :: leftExtra)
        (leftValue :: (leftArguments.toList ++ leftExtra)) := by
      intro value member
      simp only [List.mem_cons] at member ⊢
      rcases member with same | member
      · exact Or.inl same
      · exact Or.inr (List.mem_append_right _ member)
    have rightSubset : RootSubset
        (rightValue :: rightExtra)
        (rightValue :: (rightArguments.toList ++ rightExtra)) := by
      intro value member
      simp only [List.mem_cons] at member ⊢
      rcases member with same | member
      · exact Or.inl same
      · exact Or.inr (List.mem_append_right _ member)
    have nextRuntime : ShadowRuntimeRel larger leftRuntime rightRuntime
        (leftValue :: leftExtra) (rightValue :: rightExtra) := by
      apply allocated.restrictExtra
      · exact .cons values (listRel_mono (valueRel_mono extension) tail)
      · exact leftSubset
      · exact rightSubset
    refine ⟨larger, leftRuntime, leftValue, rightRuntime, rightValue,
      extension, ?_, ?_, values, nextRuntime⟩
    · simp [allocCtor, arity, empty, leftRuntime, leftValue, leftObject]
      rfl
    · simp [allocCtor, rightArity, empty, rightRuntime, rightValue,
        rightObject]
      rfl

/-- Related retained reuse operations match.  The `none` branch delegates to
paired constructor allocation and may extend the address renaming.  A
concrete token reuses an already mapped reachable cell; its explicit
reachability premise is the ownership boundary recorded by machine
readiness. -/
theorem ShadowRuntimeRel.reuseBoth_of_related
    (related : ShadowRuntimeRel rho left right
      (leftArguments.toList ++ leftExtra)
      (rightArguments.toList ++ rightExtra))
    (tokens : ValueRel rho leftToken rightToken)
    (arguments : ArrayRel (ValueRel rho) leftArguments rightArguments)
    (tail : ListRel (ValueRel rho) leftExtra rightExtra)
    (tokenReachable : ∀ location,
      leftToken = .reuseToken (some location) →
        Reachable left.heap
          (runtimeRoots left (leftArguments.toList ++ leftExtra)) location)
    (arity : leftArguments.size = info.size)
    (sourceEffect :
      reuse left leftToken info updateHeader leftArguments =
        .ok (leftResult, leftValue)) :
    ∃ larger rightResult rightValue,
      RenamingExtends rho larger ∧
      reuse right rightToken info updateHeader rightArguments =
        .ok (rightResult, rightValue) ∧
      ValueRel larger leftValue rightValue ∧
      ShadowRuntimeRel larger leftResult rightResult
        (leftValue :: leftExtra) (rightValue :: rightExtra) := by
  cases tokens with
  | reuseNone =>
      rcases related.allocCtorBoth arguments tail info arity with
        ⟨larger, computedLeft, computedValue, rightResult, rightValue,
          extension, leftAllocation, rightAllocation, values,
          allocatedRuntime⟩
      have leftReuse :
          reuse left (.reuseToken none) info updateHeader leftArguments =
            .ok (computedLeft, computedValue) := by
        simpa [reuse] using leftAllocation
      rw [leftReuse] at sourceEffect
      have pairEq := Except.ok.inj sourceEffect
      have runtimeEq := congrArg Prod.fst pairEq
      have valueEq := congrArg Prod.snd pairEq
      simp at runtimeEq valueEq
      subst leftResult
      subst leftValue
      exact ⟨larger, rightResult, rightValue, extension,
        by simpa [reuse] using rightAllocation, values, allocatedRuntime⟩
  | @reuseSome leftLocation rightLocation mapping =>
      have leftReachable := tokenReachable leftLocation rfl
      have rightReachable :
          Reachable right.heap
            (runtimeRoots right
              (rightArguments.toList ++ rightExtra)) rightLocation := by
        rcases reachable_forward related.roots related.heap
            leftReachable with
          ⟨mappedLocation, mappedEq, reachable⟩
        have locationEq : mappedLocation = rightLocation := by
          rw [mapping] at mappedEq
          exact (Option.some.inj mappedEq).symm
        simpa [locationEq] using reachable
      rcases related.heap.1 leftLocation leftReachable with
        ⟨mappedLocation, leftCell, rightCell, mappedEq, leftFound,
          rightFound, cells⟩
      have locationEq : mappedLocation = rightLocation := by
        rw [mapping] at mappedEq
        exact (Option.some.inj mappedEq).symm
      subst mappedLocation
      have source := sourceEffect
      simp only [reuse, Bind.bind, Except.bind] at source
      rw [if_neg (by simp [arity])] at source
      cases leftLiveEq : leftCell.live with
      | false =>
          simp [getLiveCell, leftFound, leftLiveEq] at source
      | true =>
          have rightLiveEq : rightCell.live = true := by
            rw [← cells.2.2.1]
            exact leftLiveEq
          have leftGet :
              getLiveCell left leftLocation = .ok leftCell := by
            simp [getLiveCell, leftFound, leftLiveEq]
          have rightGet :
              getLiveCell right rightLocation = .ok rightCell := by
            simp [getLiveCell, rightFound, rightLiveEq]
          rw [leftGet] at source
          simp only [Bind.bind, Except.bind] at source
          have heapObjects := cells.2.2.2
          generalize leftObjectEq :
            leftCell.object = leftHeapObject at heapObjects
          generalize rightObjectEq :
            rightCell.object = rightHeapObject at heapObjects
          cases heapObjects with
          | @ctor leftConstructor rightConstructor oldTags oldFields
              oldUSizes oldScalars =>
              rw [leftObjectEq] at source
              simp only at source
              have rightArity :
                  rightArguments.size = info.size := by
                rw [← arity, arrayRel_size_eq arguments]
              let leftTag :=
                if updateHeader then info.cidx else leftConstructor.tag
              let rightTag :=
                if updateHeader then info.cidx else rightConstructor.tag
              have newTags : leftTag = rightTag := by
                simp [leftTag, rightTag, oldTags]
              let leftObject : ConstructorObject := {
                tag := leftTag
                objectFields := leftArguments
                usizeFields := Array.replicate info.usize 0
                scalarFields := [] }
              let rightObject : ConstructorObject := {
                tag := rightTag
                objectFields := rightArguments
                usizeFields := Array.replicate info.usize 0
                scalarFields := [] }
              let leftReplacement : HeapCell :=
                { leftCell with object := .ctor leftObject }
              let rightReplacement : HeapCell :=
                { rightCell with object := .ctor rightObject }
              have replacement :
                  HeapCellRel rho leftReplacement rightReplacement := by
                refine ⟨cells.1, cells.2.1, cells.2.2.1, ?_⟩
                exact @HeapObjectRel.ctor rho leftObject rightObject
                  newTags arguments rfl rfl
              have leftOwned : ∀ {child},
                  Value.object (.heap child) ∈
                      leftReplacement.object.ownedValues.toList →
                    Value.object (.heap child) ∈
                        leftCell.object.ownedValues.toList ∨
                      Reachable left.heap
                        (runtimeRoots left
                          (leftArguments.toList ++ leftExtra)) child := by
                intro child member
                right
                apply Reachable.root
                apply extra_subset_runtimeRoots
                apply List.mem_append_left
                simpa [leftReplacement, leftObject,
                  HeapObject.ownedValues] using member
              have rightOwned : ∀ {child},
                  Value.object (.heap child) ∈
                      rightReplacement.object.ownedValues.toList →
                    Value.object (.heap child) ∈
                        rightCell.object.ownedValues.toList ∨
                      Reachable right.heap
                        (runtimeRoots right
                          (rightArguments.toList ++ rightExtra)) child := by
                intro child member
                right
                apply Reachable.root
                apply extra_subset_runtimeRoots
                apply List.mem_append_left
                simpa [rightReplacement, rightObject,
                  HeapObject.ownedValues] using member
              rcases related.setCellBothRooted mapping leftFound rightFound
                  leftOwned rightOwned replacement with
                ⟨computedLeft, computedRight, leftSet, rightSet,
                  updatedRuntime⟩
              change (do
                let runtime ←
                  setCell left leftLocation leftReplacement
                pure (runtime,
                  Value.object (ObjectRef.heap leftLocation))) =
                    .ok (leftResult, leftValue) at source
              rw [leftSet] at source
              have pairEq := Except.ok.inj source
              have runtimeEq := congrArg Prod.fst pairEq
              have valueEq := congrArg Prod.snd pairEq
              simp at runtimeEq valueEq
              subst leftResult
              subst leftValue
              have targetEffect :
                  reuse right (.reuseToken (some rightLocation)) info
                      updateHeader rightArguments =
                    .ok (computedRight,
                      .object (.heap rightLocation)) := by
                simp only [reuse, Bind.bind, Except.bind]
                rw [if_neg (by simp [rightArity])]
                rw [rightGet]
                simp only [Bind.bind, Except.bind]
                rw [rightObjectEq]
                change (do
                  let runtime ←
                    setCell right rightLocation rightReplacement
                  pure (runtime,
                    Value.object (ObjectRef.heap rightLocation))) = _
                rw [rightSet]
                rfl
              have leftOutputReachable :
                  Reachable computedLeft.heap
                    (runtimeRoots computedLeft
                      (leftArguments.toList ++ leftExtra)) leftLocation :=
                reachable_setCell_location leftFound leftSet leftReachable
              have rightOutputReachable :
                  Reachable computedRight.heap
                    (runtimeRoots computedRight
                      (rightArguments.toList ++ rightExtra)) rightLocation :=
                reachable_setCell_location rightFound rightSet rightReachable
              have withOutput := updatedRuntime.prependReachable
                (.heap mapping)
                (by
                  intro location equal
                  cases equal
                  exact leftOutputReachable)
                (by
                  intro location equal
                  cases equal
                  exact rightOutputReachable)
              have finalRuntime := withOutput.restrictExtra
                (.cons (.heap mapping) tail)
                (by
                  intro value member
                  simp only [List.mem_cons] at member ⊢
                  rcases member with same | old
                  · exact Or.inl same
                  · exact Or.inr (List.mem_append_right _ old))
                (by
                  intro value member
                  simp only [List.mem_cons] at member ⊢
                  rcases member with same | old
                  · exact Or.inl same
                  · exact Or.inr (List.mem_append_right _ old))
              exact ⟨rho, computedRight, .object (.heap rightLocation),
                RenamingExtends.refl rho, targetEffect, .heap mapping,
                finalRuntime⟩
          | closure fixed =>
              simp [leftObjectEq] at source
          | boxed value =>
              simp [leftObjectEq] at source
          | string value =>
              simp [leftObjectEq] at source
          | natural value =>
              simp [leftObjectEq] at source
          | integer value =>
              simp [leftObjectEq] at source
          | byteArray value =>
              simp [leftObjectEq] at source
          | «opaque» value =>
              simp [leftObjectEq] at source
  | tagged payload => simp [reuse, Bind.bind, Except.bind] at sourceEffect
  | heap mapping => simp [reuse, Bind.bind, Except.bind] at sourceEffect
  | usize value => simp [reuse, Bind.bind, Except.bind] at sourceEffect
  | scalar value => simp [reuse, Bind.bind, Except.bind] at sourceEffect
  | erased => simp [reuse, Bind.bind, Except.bind] at sourceEffect

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
