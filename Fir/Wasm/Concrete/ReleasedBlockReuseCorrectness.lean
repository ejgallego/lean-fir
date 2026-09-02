import Fir.Wasm.Concrete.ReferenceCountCorrectness

namespace Fir.Wasm.Concrete

/-!
# Released-block allocator contract

This module gives the resident allocator a proof-facing model of exact-size
reuse without committing W7 to a particular free-list representation.  The
reuse index is ghost state: it is not part of `MemoryState` and therefore is
not observable as a live Lean object.

The contract deliberately stops before whole-machine attachment.  The current
`LiveHeapRel` remembers dead semantic locations at their old physical address.
Rebinding such an address requires a separate compiler/runtime admission fact
that the old dead location is unreachable; otherwise a stale source reference
could denote the newly allocated target object.  Keeping that obligation
explicit avoids weakening ordinary dead-object decoding.
-/

/-- One exact physical allocation that may be returned by the resident
allocator. `bytes` includes the common header and final alignment. -/
structure ReleasedBlock where
  address : Word32
  bytes : Nat
  deriving Repr

namespace ReleasedBlock

/-- A reusable entry names one complete canonical dead allocation below the
current frontier.  The old payload is intentionally unconstrained: resident
implementations may keep allocator-private links there while the block is
dead, but must completely initialize the next live object before exposure. -/
structure Valid (state : MemoryState) (block : ReleasedBlock) : Prop where
  dead : DeadCellRel state block.address
  exactExtent : ∃ header,
    Header.read state.memory block.address = .ok header ∧
    header.allocationBytes.toNat = block.bytes
  extentOwned : block.address.value + block.bytes ≤ state.heapCursor

/-- Two reusable allocations must retain disjoint physical extents. -/
def Disjoint (left right : ReleasedBlock) : Prop :=
  left.address.value + left.bytes ≤ right.address.value ∨
    right.address.value + right.bytes ≤ left.address.value

theorem Disjoint.symm {left right : ReleasedBlock}
    (disjoint : left.Disjoint right) : right.Disjoint left := by
  rcases disjoint with leftBefore | rightBefore
  · exact .inr leftBefore
  · exact .inl rightBefore

/-- A valid reusable block has at least one complete common header. -/
theorem Valid.minimum {state : MemoryState} {block : ReleasedBlock}
    (valid : block.Valid state) : headerBytes ≤ block.bytes := by
  obtain ⟨deadHeader, deadRead, _, _, _, _, _, _, _, _, _, minimum, _, _⟩ :=
    valid.dead.header
  obtain ⟨extentHeader, extentRead, extentEq⟩ := valid.exactExtent
  rw [deadRead] at extentRead
  have headerEq := Except.ok.inj extentRead
  subst extentHeader
  simpa [extentEq] using minimum

/-- Reusable entries are ordinary dead blocks, never shared or persistent
live objects. -/
theorem Valid.canonicalReleasedHeader
    {state : MemoryState} {block : ReleasedBlock}
    (valid : block.Valid state) :
    ∃ header,
      Header.read state.memory block.address = .ok header ∧
      header.kind = .freed ∧ header.persistent = false ∧
      header.live = false ∧ header.refCount = 0 ∧
      header.allocationBytes.toNat = block.bytes := by
  obtain ⟨header, headerRead, _, kind, persistent, live, refCount, _, _, _, _,
      _, _, _⟩ := valid.dead.header
  obtain ⟨extentHeader, extentRead, extentEq⟩ := valid.exactExtent
  rw [headerRead] at extentRead
  have headerEq := Except.ok.inj extentRead
  subst extentHeader
  exact ⟨header, headerRead, kind, persistent, live, refCount, extentEq⟩

/-- Fresh monotone allocation transports every older released entry. -/
theorem Valid.prefixExtension
    {before after : MemoryState} {block : ReleasedBlock}
    (valid : block.Valid before) (extension : before.PrefixExtension after) :
    block.Valid after := by
  obtain ⟨header, headerRead, extentEq⟩ := valid.exactExtent
  refine {
    dead := valid.dead.prefixExtension extension
    exactExtent := ⟨header, ?_, extentEq⟩
    extentOwned := Nat.le_trans valid.extentOwned extension.cursor }
  rw [extension.readHeader block.address valid.dead.headerOwned]
  exact headerRead

/-- The ordinary last-reference/delete header transition produces a reusable
entry as soon as the released allocation's complete retained extent is known
to lie below the frontier.  `LiveHeapRel.descriptorRegion` supplies that fact
for compiler-visible objects. -/
theorem MemoryState.FrontierInvariant.releaseHeader_reusable
    {state : MemoryState} {address : Word32} {header : Header}
    (valid : state.FrontierInvariant)
    (headerRead : state.readLiveHeader address = .ok header)
    (headerOwned : address.value + headerBytes ≤ state.heapCursor)
    (extentOwned :
      address.value + header.allocationBytes.toNat ≤ state.heapCursor) :
    ∃ result memory,
      writeLiveHeader state address header.forRelease = .ok result ∧
      result = { state with memory } ∧
      header.forRelease.write state.memory address = .ok memory ∧
      result.FrontierInvariant ∧
      ({ address := address
         bytes := header.allocationBytes.toNat } : ReleasedBlock).Valid result := by
  obtain ⟨result, memory, operation, resultEq, written, finalValid, dead⟩ :=
    releaseHeader valid headerRead headerOwned
  obtain ⟨_, _, _, _, _, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans headerOwned valid.cursorInBounds
  have readAfter :
      Header.read memory address = .ok header.forRelease :=
    Header.read_of_write_eq_ok state.memory memory address header.forRelease
      headerInBounds written
  refine ⟨result, memory, operation, resultEq, written, finalValid, ?_⟩
  refine {
    dead
    exactExtent := ⟨header.forRelease, ?_, by simp [Header.forRelease]⟩
    extentOwned := ?_ }
  · simpa [resultEq] using readAfter
  · simpa [resultEq] using extentOwned

end ReleasedBlock

/-- Abstract free-list contents.  W7 may implement this with segregated heads,
linked dead payloads, or another private representation, provided it refines
this sequence. -/
abbrev ReleasedBlockIndex := List ReleasedBlock

namespace ReleasedBlockIndex

/-- The first exact-size entry is removed from the abstract index. -/
def takeExact : ReleasedBlockIndex → Nat →
    Option (ReleasedBlock × ReleasedBlockIndex)
  | [], _ => none
  | block :: rest, bytes =>
      if block.bytes = bytes then
        some (block, rest)
      else
        match takeExact rest bytes with
        | none => none
        | some (selected, remaining) => some (selected, block :: remaining)

/-- Relational certificate for exact-size selection.  It exposes precisely
the source-shape facts needed by the W7 implementation proof: exact extent,
membership, and removal of one occurrence while preserving order otherwise. -/
inductive TakesExact (bytes : Nat) :
    ReleasedBlockIndex → ReleasedBlock → ReleasedBlockIndex → Prop where
  | head {block rest} (exact : block.bytes = bytes) :
      TakesExact bytes (block :: rest) block rest
  | tail {head rest selected remaining}
      (different : head.bytes ≠ bytes)
      (take : TakesExact bytes rest selected remaining) :
      TakesExact bytes (head :: rest) selected (head :: remaining)

theorem takeExact_sound {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (operation : takeExact blocks bytes = some (selected, remaining)) :
    TakesExact bytes blocks selected remaining := by
  induction blocks generalizing selected remaining with
  | nil => simp [takeExact] at operation
  | cons head rest ih =>
      unfold takeExact at operation
      by_cases exact : head.bytes = bytes
      · rw [if_pos exact] at operation
        have pairEq := Option.some.inj operation
        cases pairEq
        exact .head exact
      · rw [if_neg exact] at operation
        cases tailOperation : takeExact rest bytes with
        | none => rw [tailOperation] at operation; contradiction
        | some result =>
            obtain ⟨tailSelected, tailRemaining⟩ := result
            rw [tailOperation] at operation
            have pairEq := Option.some.inj operation
            cases pairEq
            exact .tail exact (ih tailOperation)

theorem TakesExact.selectedExact
    {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining) :
    selected.bytes = bytes := by
  induction take with
  | head exact => exact exact
  | tail _ _ ih => exact ih

theorem TakesExact.selectedMem
    {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining) :
    selected ∈ blocks := by
  induction take with
  | head => simp
  | tail _ _ ih => exact List.Mem.tail _ ih

theorem TakesExact.remainingMem
    {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining) :
    ∀ block, block ∈ remaining → block ∈ blocks := by
  induction take with
  | head =>
      intro block member
      exact List.Mem.tail _ member
  | tail different next ih =>
      intro block member
      simp only [List.mem_cons] at member ⊢
      rcases member with rfl | member
      · exact .inl rfl
      · exact .inr (ih block member)

/-- Every indexed block is canonical, entries are unique, and their retained
physical extents do not overlap. -/
structure Valid (state : MemoryState) (blocks : ReleasedBlockIndex) : Prop where
  block : ∀ entry, entry ∈ blocks → entry.Valid state
  nodup : blocks.Nodup
  pairwise : blocks.Pairwise ReleasedBlock.Disjoint

/-- Monotone allocation beyond the frontier transports the complete reuse
index without changing its membership or disjointness. -/
theorem Valid.prefixExtension
    {before after : MemoryState} {blocks : ReleasedBlockIndex}
    (valid : Valid before blocks) (extension : before.PrefixExtension after) :
    Valid after blocks := {
  block := fun entry member =>
    (valid.block entry member).prefixExtension extension
  nodup := valid.nodup
  pairwise := valid.pairwise }

theorem TakesExact.selectedValid
    {state : MemoryState} {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining)
    (valid : Valid state blocks) : selected.Valid state :=
  valid.block selected take.selectedMem

theorem TakesExact.selectedNotMemRemaining
    {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining)
    (nodup : blocks.Nodup) : selected ∉ remaining := by
  induction take with
  | head exact =>
      simpa using (List.nodup_cons.mp nodup).1
  | @tail head rest selected remaining different next ih =>
      have restNodup := (List.nodup_cons.mp nodup).2
      have selectedNotRest := (List.nodup_cons.mp nodup).1
      simp only [List.mem_cons, not_or]
      exact ⟨fun selectedEq => selectedNotRest (selectedEq ▸ next.selectedMem),
        ih restNodup⟩

theorem TakesExact.remainingNodup
    {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining)
    (nodup : blocks.Nodup) : remaining.Nodup := by
  induction take with
  | head => exact (List.nodup_cons.mp nodup).2
  | @tail head rest selected remaining different next ih =>
      have headNotRest := (List.nodup_cons.mp nodup).1
      have restNodup := (List.nodup_cons.mp nodup).2
      apply List.nodup_cons.mpr
      refine ⟨?_, ih restNodup⟩
      intro headMem
      exact headNotRest (next.remainingMem head headMem)

theorem TakesExact.remainingPairwise
    {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining)
    (pairwise : blocks.Pairwise ReleasedBlock.Disjoint) :
    remaining.Pairwise ReleasedBlock.Disjoint := by
  induction take with
  | head => exact (List.pairwise_cons.mp pairwise).2
  | @tail head rest selected remaining different next ih =>
      obtain ⟨headDisjoint, restPairwise⟩ := List.pairwise_cons.mp pairwise
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih restPairwise⟩
      intro other otherMem
      exact headDisjoint other (next.remainingMem other otherMem)

theorem TakesExact.remainingValid
    {state : MemoryState} {blocks : ReleasedBlockIndex} {bytes : Nat}
    {selected : ReleasedBlock} {remaining : ReleasedBlockIndex}
    (take : TakesExact bytes blocks selected remaining)
    (valid : Valid state blocks) : Valid state remaining := {
  block := fun entry member =>
    valid.block entry (take.remainingMem entry member)
  nodup := take.remainingNodup valid.nodup
  pairwise := take.remainingPairwise valid.pairwise }

/-- Keep only entries whose complete extent lies below a restored frontier.
Clearing the whole index is a valid conservative implementation. -/
def invalidateForRewind (checkpoint : Nat) (blocks : ReleasedBlockIndex) :
    ReleasedBlockIndex :=
  blocks.filter fun block => block.address.value + block.bytes ≤ checkpoint

@[simp] theorem invalidateForRewind_empty (checkpoint : Nat) :
    invalidateForRewind checkpoint [] = [] := rfl

end ReleasedBlockIndex

/-- The allocator-level invariant needed by exact reuse and frontier movement.
Unlike `FrontierInvariant`, it does not claim that bytes after a rewound
frontier are zero; resident helpers must completely initialize reused or
post-rewind allocations before exposing them. -/
structure MemoryState.AllocatorInvariant (state : MemoryState) : Prop where
  frontierBase : heapBase ≤ state.heapCursor
  cursorAligned : state.heapCursor % target.heapAlignment = 0
  cursorInBounds : state.heapCursor ≤ state.memory.size

theorem MemoryState.FrontierInvariant.allocatorInvariant
    {state : MemoryState} (valid : state.FrontierInvariant)
    (frontierBase : heapBase ≤ state.heapCursor) :
    state.AllocatorInvariant := {
  frontierBase
  cursorAligned := valid.cursorAligned
  cursorInBounds := valid.cursorInBounds }

/-- Restore an already-observed frontier without changing linear memory. -/
def MemoryState.rewindTo (state : MemoryState) (checkpoint : Nat) : MemoryState :=
  { state with heapCursor := checkpoint }

/-- Checked source facts required of the resident rewind helper. -/
structure MemoryState.RewindAdmission (state : MemoryState)
    (checkpoint : Nat) : Prop where
  notFuture : checkpoint ≤ state.heapCursor
  frontierBase : heapBase ≤ checkpoint
  aligned : checkpoint % target.heapAlignment = 0

theorem MemoryState.AllocatorInvariant.rewindTo
    {state : MemoryState} {checkpoint : Nat}
    (valid : state.AllocatorInvariant)
    (admission : state.RewindAdmission checkpoint) :
    (state.rewindTo checkpoint).AllocatorInvariant := {
  frontierBase := admission.frontierBase
  cursorAligned := admission.aligned
  cursorInBounds := Nat.le_trans admission.notFuture valid.cursorInBounds }

/-- Rewind retains exactly the reusable blocks whose complete extents remain
below the restored frontier. -/
theorem ReleasedBlock.Valid.rewindTo
    {state : MemoryState} {block : ReleasedBlock} {checkpoint : Nat}
    (valid : block.Valid state)
    (retained : block.address.value + block.bytes ≤ checkpoint) :
    block.Valid (state.rewindTo checkpoint) := by
  have minimum := valid.minimum
  refine {
    dead := {
      header := by simpa [MemoryState.rewindTo] using valid.dead.header
      headerOwned := by
        change block.address.value + headerBytes ≤ checkpoint
        omega }
    exactExtent := by
      simpa [MemoryState.rewindTo] using valid.exactExtent
    extentOwned := by
      simpa [MemoryState.rewindTo] using retained }

/-- Filtering the abstract index is the complete rewind invalidation rule.
An implementation that clears all segregated heads is a special case. -/
theorem ReleasedBlockIndex.Valid.invalidateForRewind
    {state : MemoryState} {blocks : ReleasedBlockIndex} {checkpoint : Nat}
    (valid : blocks.Valid state) :
    (blocks.invalidateForRewind checkpoint).Valid
      (state.rewindTo checkpoint) := by
  refine {
    block := ?_
    nodup := List.Pairwise.filter _ valid.nodup
    pairwise := List.Pairwise.filter _ valid.pairwise }
  intro block member
  have facts : block ∈ blocks ∧
      block.address.value + block.bytes ≤ checkpoint := by
    simpa [ReleasedBlockIndex.invalidateForRewind] using member
  exact (valid.block block facts.1).rewindTo facts.2

/-- The weaker allocator invariant is sufficient to show that the existing
bump allocator remains a prefix extension.  No zero-suffix premise is used. -/
theorem MemoryState.AllocatorInvariant.allocate_prefixExtension
    {before after : MemoryState} {requestedBytes : Nat} {address : Word32}
    (valid : before.AllocatorInvariant)
    (allocated : before.allocate requestedBytes = .ok (after, address)) :
    before.PrefixExtension after := by
  have post := MemoryState.allocate_spec before after requestedBytes address
    allocated
  have alignedCursor : align8 before.heapCursor = before.heapCursor :=
    align8_eq_of_mod_eq_zero before.heapCursor (by
      simpa [target] using valid.cursorAligned)
  refine {
    cursor := ?_
    memorySize := ?_
    readByte := ?_ }
  · rw [post.cursor, alignedCursor]
    omega
  · rw [post.memory]
    unfold LinearMemory.growToFit
    split
    · exact Nat.le_refl _
    · simp
  · intro byte beforeCursor
    rw [post.memory]
    exact LinearMemory.readByte_growToFit_before_size before.memory _ byte
      (Nat.lt_of_lt_of_le beforeCursor valid.cursorInBounds)

/-- Bump allocation preserves the allocator-level frontier facts. -/
theorem MemoryState.AllocatorInvariant.allocate
    {before after : MemoryState} {requestedBytes : Nat} {address : Word32}
    (valid : before.AllocatorInvariant)
    (allocated : before.allocate requestedBytes = .ok (after, address)) :
    after.AllocatorInvariant := by
  have post := MemoryState.allocate_spec before after requestedBytes address
    allocated
  have extension := valid.allocate_prefixExtension allocated
  refine {
    frontierBase := Nat.le_trans valid.frontierBase extension.cursor
    cursorAligned := ?_
    cursorInBounds := ?_ }
  · rw [post.cursor]
    simp [target, align8]
  · rw [post.cursor]
    have endInBounds := post.endInBounds
    rw [post.addressValue] at endInBounds
    exact endInBounds

/-- One raw allocator result: either an exact canonical dead block was removed
from the private index without moving the frontier, or the existing bump
allocator ran unchanged. -/
def MemoryState.allocateReusing (state : MemoryState)
    (blocks : ReleasedBlockIndex) (requestedBytes : Nat) :
    Except MemoryError (MemoryState × ReleasedBlockIndex × Word32) := do
  if requestedBytes < headerBytes then
    throw (.invalidAllocationSize requestedBytes)
  match blocks.takeExact (align8 requestedBytes) with
  | some (block, remaining) => return (state, remaining, block.address)
  | none =>
      let (after, address) ← state.allocate requestedBytes
      return (after, blocks, address)

/-- Exact semantic classification of `allocateReusing`. -/
inductive MemoryState.ReusableAllocatePost
    (before : MemoryState) (blocks : ReleasedBlockIndex)
    (requestedBytes : Nat) :
    MemoryState → ReleasedBlockIndex → Word32 → Prop where
  | reused {selected remaining}
      (take : blocks.TakesExact (align8 requestedBytes) selected remaining)
      (selectedValid : selected.Valid before) :
      ReusableAllocatePost before blocks requestedBytes before remaining
        selected.address
  | bump {after address}
      (noExact : blocks.takeExact (align8 requestedBytes) = none)
      (allocated : before.allocate requestedBytes = .ok (after, address)) :
      ReusableAllocatePost before blocks requestedBytes after blocks address

theorem MemoryState.allocateReusing_spec
    {before after : MemoryState} {blocks remaining : ReleasedBlockIndex}
    {requestedBytes : Nat} {address : Word32}
    (valid : blocks.Valid before)
    (operation : before.allocateReusing blocks requestedBytes =
      .ok (after, remaining, address)) :
    ReusableAllocatePost before blocks requestedBytes after remaining address := by
  have minimum : headerBytes ≤ requestedBytes := by
    by_cases enough : headerBytes ≤ requestedBytes
    · exact enough
    · have less : requestedBytes < headerBytes := Nat.lt_of_not_ge enough
      unfold MemoryState.allocateReusing at operation
      rw [if_pos less] at operation
      contradiction
  unfold MemoryState.allocateReusing at operation
  rw [if_neg (Nat.not_lt.mpr minimum)] at operation
  cases selectedEq : blocks.takeExact (align8 requestedBytes) with
  | some result =>
      obtain ⟨selected, rest⟩ := result
      rw [selectedEq] at operation
      have tripleEq := Except.ok.inj operation
      cases tripleEq
      have take := ReleasedBlockIndex.takeExact_sound selectedEq
      exact .reused take (take.selectedValid valid)
  | none =>
      rw [selectedEq] at operation
      cases allocated : before.allocate requestedBytes with
      | error failure => rw [allocated] at operation; contradiction
      | ok result =>
          obtain ⟨bumpState, bumpAddress⟩ := result
          rw [allocated] at operation
          have tripleEq := Except.ok.inj operation
          cases tripleEq
          exact .bump selectedEq allocated

/-- The exact reused branch returns a canonical dead block of the requested
aligned extent and removes it uniquely from the result index. -/
theorem MemoryState.ReusableAllocatePost.reusedFacts
    {before after : MemoryState} {blocks remaining : ReleasedBlockIndex}
    {requestedBytes : Nat} {address : Word32}
    (post : ReusableAllocatePost before blocks requestedBytes after remaining
      address)
    (valid : blocks.Valid before) :
    (∃ block,
        after = before ∧ address = block.address ∧
        block.bytes = align8 requestedBytes ∧ block.Valid before ∧
        block ∈ blocks ∧ block ∉ remaining) ∨
      (blocks.takeExact (align8 requestedBytes) = none ∧
        before.allocate requestedBytes = .ok (after, address) ∧
        remaining = blocks) := by
  cases post with
  | @reused selected remaining take selectedValid =>
      left
      exact ⟨selected, rfl, rfl, take.selectedExact, selectedValid,
        take.selectedMem, take.selectedNotMemRemaining
          valid.nodup⟩
  | @bump after address noExact allocated =>
      exact .inr ⟨noExact, allocated, rfl⟩

/-- Exact-size selection preserves a valid index; bump fallback transports it
through the old monotone allocator. -/
theorem MemoryState.ReusableAllocatePost.remainingValid
    {before after : MemoryState} {blocks remaining : ReleasedBlockIndex}
    {requestedBytes : Nat} {address : Word32}
    (post : ReusableAllocatePost before blocks requestedBytes after remaining
      address)
    (allocatorValid : before.AllocatorInvariant)
    (indexValid : blocks.Valid before) :
    remaining.Valid after := by
  cases post with
  | reused take selectedValid =>
      exact take.remainingValid indexValid
  | bump noExact allocated =>
      exact indexValid.prefixExtension
        (allocatorValid.allocate_prefixExtension allocated)

/-- Reuse leaves the frontier fixed; bump fallback preserves the weaker
allocator invariant by the original checked allocation theorem. -/
theorem MemoryState.ReusableAllocatePost.allocatorInvariant
    {before after : MemoryState} {blocks remaining : ReleasedBlockIndex}
    {requestedBytes : Nat} {address : Word32}
    (post : ReusableAllocatePost before blocks requestedBytes after remaining
      address)
    (valid : before.AllocatorInvariant) : after.AllocatorInvariant := by
  cases post with
  | reused => exact valid
  | bump noExact allocated => exact valid.allocate allocated

/-- Existing source-computed wasm32 budgets remain sound.  Reuse consumes no
frontier space; weakening to the usual post-budget lets current compiler proofs
remain branch-independent. -/
theorem MemoryState.ReusableAllocatePost.addressSpaceBudget
    {before after : MemoryState} {blocks remaining : ReleasedBlockIndex}
    {requestedBytes remainingBytes : Nat} {address : Word32}
    (post : ReusableAllocatePost before blocks requestedBytes after remaining
      address)
    (allocatorValid : before.AllocatorInvariant)
    (budget : before.AddressSpaceBudget remainingBytes)
    (fits : align8 requestedBytes ≤ remainingBytes) :
    after.AddressSpaceBudget
      (remainingBytes - align8 requestedBytes) := by
  cases post with
  | reused =>
      exact budget.weaken (Nat.sub_le remainingBytes (align8 requestedBytes))
  | bump noExact allocated =>
      exact budget.consume allocatorValid.cursorAligned fits
        (MemoryState.allocate_spec before after requestedBytes address allocated)

/-- Reinitialize the common header of a selected block.  The address is still
allocator-private at this point; kind-specific payload initialization must
finish before the caller exposes it as a live Lean value. -/
def MemoryState.initializeReleasedBlock (state : MemoryState)
    (block : ReleasedBlock) (kind : ObjectKind) (persistent := false)
    (aux0 : UInt32 := 0) (aux1 : UInt32 := 0)
    (aux2 : UInt32 := 0) (aux3 : UInt32 := 0) :
    Except MemoryError MemoryState := do
  let header := Header.forAllocation kind block.bytes persistent
    aux0 aux1 aux2 aux3
  let memory ← header.write state.memory block.address
  return { state with memory }

/-- Header reinitialization converts the removed dead allocation into exact
fresh ownership at the same extent without moving the frontier. -/
theorem ReleasedBlock.Valid.initializeReleasedBlock
    {before after : MemoryState} {block : ReleasedBlock}
    {kind : ObjectKind} {persistent : Bool} {aux0 aux1 aux2 aux3 : UInt32}
    (valid : block.Valid before)
    (allocatorValid : before.AllocatorInvariant)
    (operation : before.initializeReleasedBlock block kind persistent
      aux0 aux1 aux2 aux3 = .ok after) :
    let header := Header.forAllocation kind block.bytes persistent
      aux0 aux1 aux2 aux3
    after.heapCursor = before.heapCursor ∧
      after.memory.size = before.memory.size ∧
      after.readLiveHeader block.address = .ok header ∧
      after.AllocatorInvariant := by
  let header := Header.forAllocation kind block.bytes persistent
    aux0 aux1 aux2 aux3
  obtain ⟨oldHeader, oldRead, oldExtent⟩ := valid.exactExtent
  obtain ⟨deadHeader, deadRead, addressHeap, _, _, _, _, _, _, _, _, _,
      oldAligned, extentInMemory⟩ := valid.dead.header
  rw [deadRead] at oldRead
  have actualEq := Except.ok.inj oldRead
  subst oldHeader
  have minimum : headerBytes ≤ block.bytes := valid.minimum
  have headerInBounds : block.address.value + headerBytes ≤ before.memory.size := by
    have completeInBounds : block.address.value + block.bytes ≤ before.memory.size := by
      simpa [oldExtent] using extentInMemory
    omega
  unfold MemoryState.initializeReleasedBlock at operation
  dsimp only at operation
  cases written : header.write before.memory block.address with
  | error failure => rw [written] at operation; contradiction
  | ok memory =>
      rw [written] at operation
      have stateEq := Except.ok.inj operation
      subst after
      have memorySize := Header.write_preserves_size before.memory memory
        block.address header headerInBounds written
      have headerRead := Header.read_of_write_eq_ok before.memory memory
        block.address header headerInBounds written
      have liveRead :
          ({ before with memory } : MemoryState).readLiveHeader block.address =
            .ok header := by
        unfold MemoryState.readLiveHeader
        rw [addressHeap, headerRead]
        simp only [Bind.bind, Except.bind]
        have blockAligned : block.bytes % target.heapAlignment = 0 := by
          simpa [oldExtent] using oldAligned
        have blockFits : block.bytes < UInt32.size := by
          rw [← oldExtent]
          exact UInt32.toNat_lt deadHeader.allocationBytes
        have blockWord : (UInt32.ofNat block.bytes).toNat = block.bytes :=
          UInt32.toNat_ofNat_of_lt' blockFits
        have extentAfter : block.address.value + block.bytes ≤ memory.size := by
          rw [memorySize]
          simpa [oldExtent] using extentInMemory
        simp [header, Header.forAllocation, minimum, blockAligned,
          blockWord, extentAfter]
        rfl
      refine ⟨rfl, memorySize, liveRead, ?_⟩
      exact {
        frontierBase := allocatorValid.frontierBase
        cursorAligned := allocatorValid.cursorAligned
        cursorInBounds := by simpa [memorySize] using allocatorValid.cursorInBounds }

/-- The current witness cannot bind one physical address to a distinct new
semantic location.  Whole-machine reuse must therefore retire an unreachable
dead mapping (or move to a generation-aware witness) before rebinding. -/
theorem RefinementWitness.WellFormed.reusedAddress_requires_sameLocation
    {witness : RefinementWitness} (valid : witness.WellFormed)
    {oldLocation newLocation : Fir.LeanIR.Impure.Location} {address : Word32}
    (oldMapped : witness.locations.lookup? oldLocation = some address)
    (newMapped : witness.locations.lookup? newLocation = some address) :
    oldLocation = newLocation :=
  valid.locationInjective oldLocation newLocation address oldMapped newMapped

end Fir.Wasm.Concrete
