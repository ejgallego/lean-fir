import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Emit.ResidentByteArray
import Fir.Wasm.Concrete.ReleasedBlockReuseCorrectness
import FirTalos.ConcreteResidentAllocator

namespace FirTalos.Concrete.ResidentReleasedBlockReuse

open Fir.Wasm
open Fir.Wasm.Concrete

/-!
# Production released-block reuse attachment

This module attaches W7's reduction-visible payload-link recycler to the
representation-independent W6 contract in
`ReleasedBlockReuseCorrectness`.  It records exact source equations and the
semantic extent facts needed by a future instruction-execution theorem.

It deliberately does not claim that `ResidentAllocatorRel` observes a
nonempty reuse index.  That legacy relation equates every physical byte and
therefore describes the empty-index bump subrelation.  Whole-machine reuse
still needs an indexed/masked memory relation and retirement of the old dead
location from `RefinementWitness` before the address is rebound.
-/

def addressId : Lean.FVarId := ⟨`address⟩
def persistentFloorId : Lean.FVarId := ⟨`persistentFloor⟩
def freeListCursorId : Lean.FVarId := ⟨`freeListCursor⟩
def arrayInputAddressId : Lean.FVarId := ⟨`inputAddress⟩

/-- Shared source spelling of the canonical dead-header stores.  Allocator
links are intentionally absent: the link is written only after this header
has been validated and only into the first ignored payload word. -/
def canonicalDeadHeaderSource (address : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet address,
  .i32Const .uint32 ObjectKind.freed.code,
  .i32Store .uint32 (UInt32.ofNat headerKindOffset),
  .localGet address,
  .i32Const .uint32 0,
  .i32Store .uint32 (UInt32.ofNat headerFlagsOffset),
  .localGet address,
  .i32Const .uint32 0,
  .i32Store .uint32 (UInt32.ofNat headerRefCountOffset),
  .localGet address,
  .i32Const .uint32 0,
  .i32Store .uint32 (UInt32.ofNat headerAux0Offset),
  .localGet address,
  .i32Const .uint32 0,
  .i32Store .uint32 (UInt32.ofNat headerAux1Offset),
  .localGet address,
  .i32Const .uint32 0,
  .i32Store .uint32 (UInt32.ofNat headerAux2Offset),
  .localGet address,
  .i32Const .uint32 0,
  .i32Store .uint32 (UInt32.ofNat headerAux3Offset)]

theorem bucketCount_eq :
    Fir.Wasm.Emit.ResidentAllocator.freeListBucketCount = 256 := by
  decide

theorem bucketMask_eq :
    Fir.Wasm.Emit.ResidentAllocator.freeListBucketMask = 255 := by
  decide

theorem payloadLinkOffset_eq :
    Fir.Wasm.Emit.ResidentAllocator.freeListLinkOffset = headerBytes := rfl

theorem minimumReusableAllocationBytes_eq :
    Fir.Wasm.Emit.ResidentAllocator.minimumReusableAllocationBytes =
      headerBytes + 4 := rfl

/-- The production validator is exactly the W6-visible complete canonical
dead-header, alignment, and recorded-extent check. -/
theorem validateCandidateBody_eq :
    Fir.Wasm.Emit.ResidentAllocator.validateCandidateBody =
      ResidentAllocator.validateCandidateSource := rfl

/-- Exact source body of the private recycler.  The payload link is written
before the reserved-prefix head, so a published head always names a linked
candidate.  The early return excludes allocations without a link word. -/
def recyclerSource (frontierIndex : Nat) : List Fir.Wasm.Instruction :=
  [.globalGet frontierIndex .uint32,
    .localSet ResidentAllocator.currentId,
    .localGet addressId,
    .localSet ResidentAllocator.candidateId] ++
  ResidentAllocator.validateCandidateSource ++ [
    .localGet ResidentAllocator.allocationBytesId,
    .i32Const .uint32 (UInt32.ofNat
      Fir.Wasm.Emit.ResidentAllocator.minimumReusableAllocationBytes),
    .i32LtU,
    .ifElse [.ret] []] ++
  Fir.Wasm.Emit.ResidentAllocator.bucketAddressBody
    ResidentAllocator.allocationBytesId ResidentAllocator.bucketAddressId ++ [
    .localGet ResidentAllocator.bucketAddressId,
    .i32Load .uint32 0,
    .localSet ResidentAllocator.nextId,
    .localGet addressId,
    .localGet ResidentAllocator.nextId,
    .i32Store .uint32 (UInt32.ofNat
      Fir.Wasm.Emit.ResidentAllocator.freeListLinkOffset),
    .localGet ResidentAllocator.bucketAddressId,
    .localGet addressId,
    .i32Store .uint32 0,
    .ret]

theorem recycleFunction_shape (frontierIndex : Nat) :
    (Fir.Wasm.Emit.ResidentAllocator.recycleFunction frontierIndex).body =
      recyclerSource frontierIndex := rfl

/-- Standard rewind clears the complete segregated-head table before moving
the frontier.  This implements the abstract contract's conservative empty
invalidation policy. -/
theorem rewindFunction_shape (frontierIndex : Nat) :
    (Fir.Wasm.Emit.ResidentAllocator.rewindFunction frontierIndex).body =
      [.globalGet frontierIndex .uint32,
        .localSet ResidentAllocator.currentId] ++
      ResidentAllocator.trapWhenTrueSource [
        .localGet ResidentAllocator.currentId,
        .localGet addressId,
        .i32LtU] ++
      ResidentAllocator.trapWhenTrueSource [
        .localGet addressId,
        .i32Const .uint32 (UInt32.ofNat heapBase),
        .i32LtU] ++
      ResidentAllocator.requireAlignedSource addressId ++
      Fir.Wasm.Emit.ResidentAllocator.clearFreeListsBody ++ [
        .localGet addressId,
        .globalSet frontierIndex .uint32,
        .ret] := rfl

/-- Cache-aware rewind has the same clear-before-frontier-update boundary. -/
theorem cacheAwareRewindFunction_shape
    (frontierIndex persistentFloorIndex : Nat) :
    (Fir.Wasm.Emit.ResidentAllocator.cacheAwareRewindFunction
      frontierIndex persistentFloorIndex).body =
      [.globalGet frontierIndex .uint32,
        .localSet ResidentAllocator.currentId,
        .globalGet persistentFloorIndex .uint32,
        .localSet persistentFloorId] ++
      ResidentAllocator.trapWhenTrueSource [
        .localGet ResidentAllocator.currentId,
        .localGet persistentFloorId,
        .i32LtU] ++ [
        .localGet addressId,
        .localGet persistentFloorId,
        .i32LtU,
        .ifElse
          [.localGet persistentFloorId, .localSet addressId]
          []] ++
      ResidentAllocator.trapWhenTrueSource [
        .localGet ResidentAllocator.currentId,
        .localGet addressId,
        .i32LtU] ++
      ResidentAllocator.trapWhenTrueSource [
        .localGet addressId,
        .i32Const .uint32 (UInt32.ofNat heapBase),
        .i32LtU] ++
      ResidentAllocator.requireAlignedSource addressId ++
      Fir.Wasm.Emit.ResidentAllocator.clearFreeListsBody ++ [
        .localGet addressId,
        .globalSet frontierIndex .uint32,
        .ret] := rfl

/-- Header release remains canonical and contains no private allocator write.
Recursive and explicit-delete paths call the recycler only through their
terminal `finishReleaseBody`. -/
theorem releaseHeaderBody_shape (recycle : Bool) :
    Fir.Wasm.Emit.ResidentRelease.releaseHeaderBody recycle =
      canonicalDeadHeaderSource addressId ++ [.ret] := by
  cases recycle <;> rfl

theorem finishReleaseBody_recycling_shape :
    Fir.Wasm.Emit.ResidentRelease.finishReleaseBody true = [
      .localGet addressId,
      .call (.declaration Fir.Wasm.Emit.ResidentAllocator.recycleName),
      .ret] := rfl

theorem finishReleaseBody_standalone_shape :
    Fir.Wasm.Emit.ResidentRelease.finishReleaseBody false = [.ret] := rfl

/-- Constructor children are traversed before the allocator-private link may
overwrite the released payload. -/
theorem constructorReleaseBody_recycling_shape :
    Fir.Wasm.Emit.ResidentRelease.constructorReleaseBody true = [
      .i32Const .uint32 (UInt32.ofNat
        Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit),
      .localGet ⟨`count⟩,
      .i32LtU,
      .ifElse
        [.unreachable]
        (Fir.Wasm.Emit.ResidentRelease.releaseConstructorFields ++
          Fir.Wasm.Emit.ResidentRelease.finishReleaseBody true)] := rfl

/-- Transferred Array retirement performs every canonical dead-header store
before publishing the container to the reuse index. -/
theorem retireTransferredArray_shape :
    Fir.Wasm.Emit.ResidentArray.retireTransferredArray =
      canonicalDeadHeaderSource arrayInputAddressId ++ [
        .localGet arrayInputAddressId,
        .call (.declaration Fir.Wasm.Emit.ResidentAllocator.recycleName)] := rfl

/-- Every object-valued Array lane is published as a complete zero-extended
eight-byte slot, so reusing an allocation cannot expose stale high padding. -/
theorem storeObjectWord_shape (address value : Lean.FVarId) (offset : Nat) :
    Fir.Wasm.Emit.ResidentArray.storeObjectWord address value offset = [
      .localGet address,
      .localGet value,
      .i64ExtendI32U .uint64,
      .i64Store .uint64 (UInt32.ofNat offset)] := rfl

/-- A canonical abstract released block supplies every semantic header fact
checked by the production candidate validator. -/
theorem ReleasedBlock.Valid.productionCandidateFacts
    {state : MemoryState} {block : ReleasedBlock}
    (valid : block.Valid state) :
    ∃ header,
      Header.read state.memory block.address = .ok header ∧
      block.address.classify = .heap ∧
      header.kind = .freed ∧
      header.persistent = false ∧
      header.live = false ∧
      header.refCount = 0 ∧
      header.aux0 = 0 ∧ header.aux1 = 0 ∧
      header.aux2 = 0 ∧ header.aux3 = 0 ∧
      header.allocationBytes.toNat = block.bytes ∧
      block.bytes % target.heapAlignment = 0 ∧
      block.address.value + block.bytes ≤ state.memory.size := by
  obtain ⟨header, headerRead, addressHeap, kind, persistent, live, refCount,
      aux0, aux1, aux2, aux3, minimum, aligned, extentInMemory⟩ :=
    valid.dead.header
  obtain ⟨extentHeader, extentRead, extentEq⟩ := valid.exactExtent
  rw [headerRead] at extentRead
  have headerEq := Except.ok.inj extentRead
  subst extentHeader
  exact ⟨header, headerRead, addressHeap, kind, persistent, live, refCount,
    aux0, aux1, aux2, aux3, extentEq, by simpa [extentEq] using aligned,
    by simpa [extentEq] using extentInMemory⟩

/-- Eligibility excludes the header-only case and places the complete private
payload-link word inside the retained allocation and current memory extent. -/
theorem ReleasedBlock.Valid.payloadLinkInBounds
    {state : MemoryState} {block : ReleasedBlock}
    (valid : block.Valid state)
    (eligible :
      Fir.Wasm.Emit.ResidentAllocator.minimumReusableAllocationBytes ≤
        block.bytes) :
    block.address.value +
        Fir.Wasm.Emit.ResidentAllocator.freeListLinkOffset + 4 ≤
      state.memory.size := by
  obtain ⟨deadHeader, deadRead, _, _, _, _, _, _, _, _, _, _, _,
      extentInMemory⟩ := valid.dead.header
  rw [payloadLinkOffset_eq]
  rw [minimumReusableAllocationBytes_eq] at eligible
  obtain ⟨extentHeader, extentRead, extentEq⟩ := valid.exactExtent
  rw [deadRead] at extentRead
  have headerEq := Except.ok.inj extentRead
  subst extentHeader
  rw [extentEq] at extentInMemory
  omega

theorem headerOnly_isIneligible :
    headerBytes <
      Fir.Wasm.Emit.ResidentAllocator.minimumReusableAllocationBytes := by
  rw [minimumReusableAllocationBytes_eq]
  omega

/-- Abstract exact selection packages the reused branch expected from a
successful production candidate search.  The future machine proof needs only
to establish this `takeExact` equation and the physical/index relation. -/
theorem reusablePost_of_takeExact
    {before : MemoryState} {blocks remaining : ReleasedBlockIndex}
    {requestedBytes : Nat} {selected : ReleasedBlock}
    (valid : blocks.Valid before)
    (operation : blocks.takeExact (align8 requestedBytes) =
      some (selected, remaining)) :
    MemoryState.ReusableAllocatePost before blocks requestedBytes before
      remaining selected.address := by
  have take := ReleasedBlockIndex.takeExact_sound operation
  exact .reused take (take.selectedValid valid)

end FirTalos.Concrete.ResidentReleasedBlockReuse
