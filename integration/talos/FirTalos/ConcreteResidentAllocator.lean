import Fir.Wasm.Emit.ResidentAllocator
import Fir.Wasm.Concrete.FreshAllocationCorrectness
import FirTalos.ConcreteResidentMemory
import FirTalos.Correctness.Adapter
import FirTalos.Correctness.Function

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident allocator refinement

The byte relation used by ordinary resident helpers intentionally observes
only the current linear-memory extent.  Allocation additionally needs two
facts: the resident frontier global denotes W6's heap cursor, and Talos's
total byte function is zero beyond the current extent.  The latter is what
makes a later `memory.grow` reveal the same zero-filled pages as W6's finite
`LinearMemory.growToFit` operation.
-/

/-- Complete relation needed while a resident helper may allocate or grow
linear memory.  This is runtime state, not a compiler-produced certificate. -/
structure ResidentAllocatorRel (heap : MemoryState) (store : Wasm.Store host)
    (frontierIndex : Nat) : Prop extends ResidentMemoryRel heap store.mem where
  frontierBase : heapBase ≤ heap.heapCursor
  frontierFits : heap.heapCursor < wordModulus
  frontier : store.globals.globals[frontierIndex]? =
    some (.i32 (UInt32.ofNat heap.heapCursor))
  zeroAfterExtent : ∀ address, heap.memory.size ≤ address →
    store.mem.bytes address = 0

namespace ResidentAllocatorRel

/-- The one-page zero memory and heap-base global installed by the resident
runtime satisfy the complete allocator relation. -/
theorem initial
    {store : Wasm.Store host} {frontierIndex : Nat}
    (memory : store.mem = Wasm.Mem.empty 1)
    (frontier : store.globals.globals[frontierIndex]? =
      some (.i32 (UInt32.ofNat heapBase))) :
    ResidentAllocatorRel MemoryState.initial store frontierIndex := by
  refine {
    toResidentMemoryRel := ?_
    frontierBase := by decide
    frontierFits := by decide
    frontier := ?_
    zeroAfterExtent := ?_ }
  · rw [memory]
    exact ResidentMemoryRel.initial
  · simpa [MemoryState.initial] using frontier
  · intro address _
    simp [memory, Wasm.Mem.empty]

/-- An in-bounds paired W6/Talos word store preserves both the frontier and
the zero bytes that a future memory growth may expose. -/
theorem writeUInt32
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Nat} {value : UInt32} {result : LinearMemory}
    (inBounds : address + 3 < heap.memory.size)
    (written : heap.memory.writeUInt32 address value = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      { store with mem := store.mem.write32 (UInt32.ofNat address) value }
      frontierIndex := by
  obtain ⟨actual, actualWrite, actualSize, _, _, _, _, _⟩ :=
    LinearMemory.writeUInt32_spec heap.memory address value inBounds
  rw [actualWrite] at written
  cases written
  refine {
    toResidentMemoryRel := related.toResidentMemoryRel.writeUInt32
      inBounds actualWrite
    frontierBase := related.frontierBase
    frontierFits := related.frontierFits
    frontier := by simpa using related.frontier
    zeroAfterExtent := ?_ }
  intro other afterExtent
  have roundtrip : (UInt32.ofNat address).toNat = address :=
    UInt32.toNat_ofNat_of_lt' (related.toResidentMemoryRel.address_lt_uint32
      inBounds)
  have afterOld : heap.memory.size ≤ other := by
    simpa [actualSize] using afterExtent
  have disjoint : address + 3 < other := by omega
  calc
    (store.mem.write32 (UInt32.ofNat address) value).bytes other =
        store.mem.bytes other :=
      ResidentMemoryRel.bytes_write32_of_disjoint _ _ _ _
        (.inr (by simpa [roundtrip] using disjoint))
    _ = 0 := related.zeroAfterExtent other afterOld

/-- Page growth preserves the byte relation once arithmetic has identified
the exact W6 successor extent.  Keeping the page calculation as an explicit
premise separates generic memory reasoning from the allocator program's
wasm32 shift arithmetic. -/
theorem growToFit
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex pages : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    (requiredBytes : Nat)
    (sizeEq : (heap.memory.growToFit requiredBytes).size =
      pages * wasmPageBytes)
    (sizeLe : pages * wasmPageBytes ≤ UInt32.size) :
    ResidentMemoryRel
      { heap with memory := heap.memory.growToFit requiredBytes }
      { store.mem with pages := pages } := by
  refine {
    size_eq := sizeEq
    size_le := by simpa [sizeEq] using sizeLe
    byte_eq := ?_ }
  intro address inBounds
  by_cases oldBounds : address < heap.memory.size
  · have preserved := LinearMemory.readByte_growToFit_before_size
      heap.memory requiredBytes address oldBounds
    have oldByte := related.toResidentMemoryRel.byte_eq address oldBounds
    simp [LinearMemory.readByte, oldBounds, inBounds] at preserved
    simpa [preserved] using oldByte
  · have oldAfter : heap.memory.size ≤ address := Nat.le_of_not_gt oldBounds
    have grownZero := LinearMemory.growToFit_zero_from heap.memory
      heap.memory.size requiredBytes (by
        intro other after before
        omega) address oldAfter inBounds
    have targetZero := related.zeroAfterExtent address oldAfter
    simp [inBounds] at grownZero
    simpa [grownZero] using targetZero

/-- Successful Talos growth to an explicitly chosen page frontier. -/
theorem mem_grow_to_pages
    (memory : Wasm.Mem) (pages cap : Nat)
    (monotone : memory.pages ≤ pages)
    (fits32 : pages < UInt32.size)
    (withinCap : pages ≤ cap) :
    memory.grow (UInt32.ofNat (pages - memory.pages)) cap =
      some ({ memory with pages := pages }, memory.pages) := by
  unfold Wasm.Mem.grow
  have deltaFits : pages - memory.pages < UInt32.size :=
    lt_of_le_of_lt (Nat.sub_le pages memory.pages) fits32
  rw [UInt32.toNat_ofNat_of_lt' deltaFits]
  dsimp only
  have sumEq : memory.pages + (pages - memory.pages) = pages :=
    Nat.add_sub_of_le monotone
  rw [sumEq, if_pos withinCap]

/-- Exact page extent selected jointly by W6 growth and the resident
allocator.  This is the arithmetic bridge between `growToFit` and W7's
`pagesForEnd` instruction sequence. -/
theorem growToFit_size_eq_max_pages
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    (requiredBytes : Nat) (positive : 0 < requiredBytes) :
    (heap.memory.growToFit requiredBytes).size =
      max store.mem.pages ((requiredBytes - 1) / wasmPageBytes + 1) *
        wasmPageBytes := by
  unfold LinearMemory.growToFit
  split
  next enough =>
    rw [related.toResidentMemoryRel.size_eq] at enough ⊢
    rw [Nat.max_eq_left (by
      unfold wasmPageBytes at enough ⊢
      omega)]
  next notEnough =>
    simp only [Array.size_append, Array.size_replicate]
    rw [related.toResidentMemoryRel.size_eq] at notEnough ⊢
    rw [Nat.max_eq_right (by
      unfold wasmPageBytes at notEnough ⊢
      omega)]
    unfold wasmPageBytes at notEnough ⊢
    omega

/-- W7's wasm32 `pagesForEnd` sequence computes the natural ceiling used in
the W6 growth theorem, without either subtraction or addition wrapping. -/
theorem pagesForEnd_word_toNat
    {requiredBytes : Nat} (positive : 0 < requiredBytes)
    (fits32 : requiredBytes < UInt32.size) :
    ((((UInt32.ofNat requiredBytes - 1) >>> 16) + 1 : UInt32).toNat) =
      (requiredBytes - 1) / wasmPageBytes + 1 := by
  have reqLt : requiredBytes < 4294967296 := by
    simpa [UInt32.size] using fits32
  have subEq : (UInt32.ofNat requiredBytes - 1).toNat =
      requiredBytes - 1 := by
    rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' fits32]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have rearrange : 4294967296 - 1 + requiredBytes =
        4294967296 + (requiredBytes - 1) := by omega
    rw [rearrange, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : requiredBytes - 1 < 4294967296)]
  rw [UInt32.toNat_add, UInt32.toNat_shiftRight, subEq]
  simp only [UInt32.toNat_ofNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  unfold wasmPageBytes
  rw [Nat.mod_eq_of_lt]
  omega

/-- Adjacent checked W6 word stores refine the corresponding Talos stores
while preserving the complete allocating-runtime relation. -/
theorem writeUInt32s
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Nat} {values : List UInt32} {result : LinearMemory}
    (inBounds : address + 4 * values.length ≤ heap.memory.size)
    (written : heap.memory.writeUInt32s address values = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      { store with mem :=
          (ResidentMemoryRel.writeUInt32sMemory store.mem
            (UInt32.ofNat address) values) }
      frontierIndex := by
  induction values generalizing heap store address result with
  | nil =>
      simp [LinearMemory.writeUInt32s] at written
      subst result
      simpa [ResidentMemoryRel.writeUInt32sMemory] using related
  | cons value rest ih =>
      simp only [List.length_cons] at inBounds
      have headInBounds : address + 3 < heap.memory.size := by omega
      obtain ⟨middle, headWrite, middleSize, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec heap.memory address value headInBounds
      unfold LinearMemory.writeUInt32s at written
      rw [headWrite] at written
      have middleRelated := related.writeUInt32 headInBounds headWrite
      have tailInBounds : address + 4 + 4 * rest.length ≤ middle.size := by
        omega
      have tailRelated := ih middleRelated tailInBounds written
      simpa [ResidentMemoryRel.writeUInt32sMemory, UInt32.ofNat_add] using
        tailRelated

/-- The eight adjacent W6 common-header stores refine one exact Talos header
memory update. -/
theorem writeHeader
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Word32} {header : Header} {result : LinearMemory}
    (inBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : header.write heap.memory address = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      { store with mem :=
          (ResidentMemoryRel.writeUInt32sMemory store.mem
            (UInt32.ofNat address.value) header.words) }
      frontierIndex := by
  apply related.writeUInt32s
  · simpa [Header.words, headerBytes] using inBounds
  · exact written

end ResidentAllocatorRel

namespace ResidentAllocator

/-- Public W6 spelling of the emitter's private checked-trap combinator. -/
def trapWhenTrueSource (condition : List Fir.Wasm.Instruction) :
    List Fir.Wasm.Instruction :=
  condition ++ [.ifElse [.unreachable] []]

/-- Public W6 spelling of the emitter's private alignment check. -/
def requireAlignedSource (localId : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  trapWhenTrueSource [
    .localGet localId,
    .i32Const .uint32 (UInt32.ofNat (target.heapAlignment - 1)),
    .i32And]

/-- Public W6 spelling of the emitter's private page-ceiling sequence. -/
def pagesForEndSource (localId : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet localId,
  .i32Const .uint32 1,
  .i32Sub,
  .i32Const .uint32 16,
  .i32ShrU,
  .i32Const .uint32 1,
  .i32Add]

/-- Public W6 spelling of the complete symbolic allocator body. -/
def allocateSourceProgram (frontierIndex : Nat)
    (requested current allocationEnd requiredPages currentPages growResult :
      Lean.FVarId) : List Fir.Wasm.Instruction :=
  trapWhenTrueSource [
    .localGet requested,
    .i32Const .uint32 (UInt32.ofNat headerBytes),
    .i32LtU] ++
  requireAlignedSource requested ++
  [.globalGet frontierIndex .uint32, .localSet current] ++
  trapWhenTrueSource [
    .localGet current,
    .i32Const .uint32 (UInt32.ofNat heapBase),
    .i32LtU] ++
  requireAlignedSource current ++
  [.localGet current,
    .localGet requested,
    .i32Add,
    .localSet allocationEnd] ++
  trapWhenTrueSource [
    .localGet allocationEnd,
    .localGet current,
    .i32LtU] ++
  pagesForEndSource allocationEnd ++
  [.localSet requiredPages,
    .memorySize,
    .localSet currentPages,
    .localGet currentPages,
    .localGet requiredPages,
    .i32LtU,
    .ifElse
      ([.localGet requiredPages,
        .localGet currentPages,
        .i32Sub,
        .memoryGrow,
        .localSet growResult] ++
        trapWhenTrueSource [
          .localGet growResult,
          .i32Const .uint32 4294967295,
          .i32Eq])
      [],
    .localGet allocationEnd,
    .globalSet frontierIndex .uint32,
    .localGet current,
    .ret]

/-- The public emitter definition has exactly the W6-spelled source shape. -/
theorem allocateFunction_shape (frontierIndex : Nat) :
    (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).body =
      allocateSourceProgram frontierIndex
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).params[0]!.1
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).locals[0]!.1
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).locals[1]!.1
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).locals[2]!.1
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).locals[3]!.1
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).locals[4]!.1 := by
  rfl

/-- Talos spelling of the resident allocator's checked-trap combinator. -/
def trapWhenTrueProgram (condition : Wasm.Program) : Wasm.Program :=
  condition ++ [.iff 0 0 [.unreachable] []]

/-- Talos spelling of the emitter's eight-byte alignment check. -/
def requireAlignedProgram (localIndex : Nat) : Wasm.Program :=
  trapWhenTrueProgram [.localGet localIndex, .const 7, .and]

/-- Talos spelling of the emitter's wasm32 ceiling-by-pages calculation. -/
def pagesForEndProgram (localIndex : Nat) : Wasm.Program := [
  .localGet localIndex,
  .const 1,
  .sub,
  .const 16,
  .shrU,
  .const 1,
  .add]

/-- Exact adapted body of `fir_heap_alloc`.  Local zero is the requested
byte count; locals one through five are respectively current frontier,
allocation end, required pages, current pages, and the grow result. -/
def allocateProgram (frontierIndex : Nat) : Wasm.Program :=
  trapWhenTrueProgram [.localGet 0, .const 32, .ltU] ++
  requireAlignedProgram 0 ++
  [.globalGet frontierIndex, .localSet 1] ++
  trapWhenTrueProgram [.localGet 1, .const 1024, .ltU] ++
  requireAlignedProgram 1 ++
  [.localGet 1, .localGet 0, .add, .localSet 2] ++
  trapWhenTrueProgram [.localGet 2, .localGet 1, .ltU] ++
  pagesForEndProgram 2 ++
  [.localSet 3,
    .memorySize,
    .localSet 4,
    .localGet 4,
    .localGet 3,
    .ltU,
    .iff 0 0
      ([.localGet 3,
        .localGet 4,
        .sub,
        .memoryGrow,
        .localSet 5] ++
        trapWhenTrueProgram [.localGet 5, .const 4294967295, .eq])
      [],
    .localGet 2,
    .globalSet frontierIndex,
    .localGet 1,
    .ret]

/-- Machine value computed by `pagesForEndProgram`. -/
def pagesForEndWord (allocationEnd : UInt32) : UInt32 :=
  ((allocationEnd - 1) >>> 16) + 1

/-- Concrete call frame of the one-parameter/five-local allocator body. -/
def allocateEntry (requestedBytes : UInt32) : Wasm.Locals := {
  params := [.i32 requestedBytes]
  locals := List.replicate 5 (.i32 0)
  values := [] }

/-- Store update performed after a successful optional memory growth. -/
def setFrontierStore (store : Wasm.Store host) (frontierIndex : Nat)
    (frontier : UInt32) : Wasm.Store host :=
  { store with globals := {
      globals := store.globals.globals.set frontierIndex (.i32 frontier) } }

/-- Replacing the related memory and advancing the resident frontier packages
the state relation used by an allocating helper.  The old relation supplies
the proof that the frontier global is present; the new heap's strict wasm32
bound is explicit because an `i32` global cannot denote the value `2^32`. -/
theorem setFrontierStore_related
    {before after : MemoryState} {store : Wasm.Store host}
    {frontierIndex : Nat} {memory : Wasm.Mem}
    (oldRelated : ResidentAllocatorRel before store frontierIndex)
    (memoryRelated : ResidentMemoryRel after memory)
    (frontierBase : heapBase ≤ after.heapCursor)
    (frontierFits : after.heapCursor < wordModulus)
    (zeroAfterExtent : ∀ address, after.memory.size ≤ address →
      memory.bytes address = 0) :
    ResidentAllocatorRel after
      (setFrontierStore { store with mem := memory } frontierIndex
        (UInt32.ofNat after.heapCursor)) frontierIndex := by
  obtain ⟨indexInBounds, _⟩ :=
    List.getElem?_eq_some_iff.mp oldRelated.frontier
  refine {
    toResidentMemoryRel := by simpa [setFrontierStore] using memoryRelated
    frontierBase
    frontierFits
    frontier := by simp [setFrontierStore, indexInBounds]
    zeroAfterExtent := by simpa [setFrontierStore] using zeroAfterExtent }

/-- Eight-byte natural alignment transfers exactly to the wasm32 mask check
once the natural is known to fit in a machine word. -/
theorem alignedWord_of_mod8
    {value : Nat} (fits32 : value < UInt32.size)
    (aligned : value % 8 = 0) :
    UInt32.ofNat value &&& 7 = 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' fits32]
  change value &&& 7 = 0
  rw [show 7 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  exact aligned

/-- Exact scalar execution of the resident allocator when its reservation
already fits in the current linear-memory extent.  The theorem exposes only
the machine checks performed by the emitter; W6 refinement discharges them
from allocation and frontier invariants below. -/
theorem wp_allocateProgram_noGrow
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {frontierIndex : Nat} {requested current : UInt32}
    (memory32 : module.memIs64 = false)
    (frontier : store.globals.globals[frontierIndex]? = some (.i32 current))
    (requestedMinimum : ¬ requested < 32)
    (requestedAligned : requested &&& 7 = 0)
    (currentBase : ¬ current < 1024)
    (currentAligned : current &&& 7 = 0)
    (noWrap : ¬ current + requested < current)
    (noGrow : ¬ UInt32.ofNat store.mem.pages <
      pagesForEndWord (current + requested))
    (returned : Q (.Return
      (setFrontierStore store frontierIndex (current + requested))
      [.i32 current])) :
    Wasm.wp module (allocateProgram frontierIndex) Q store
      (allocateEntry requested) env := by
  have requestedAligned' : 7 &&& requested = 0 := by
    simpa [UInt32.and_comm] using requestedAligned
  have currentAligned' : 7 &&& current = 0 := by
    simpa [UInt32.and_comm] using currentAligned
  have noWrap' : ¬ requested + current < current := by
    simpa [UInt32.add_comm] using noWrap
  simp [pagesForEndWord, UInt32.add_comm] at noGrow
  have noGrow' : ¬ UInt32.ofNat store.mem.pages <
      (1 : UInt32) + ((requested + current - 1) >>> 16) :=
    UInt32.not_lt.mpr noGrow
  unfold allocateProgram requireAlignedProgram pagesForEndProgram allocateEntry
  simp only [trapWhenTrueProgram, List.cons_append, List.nil_append]
  wp_run
  simp [requestedMinimum]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [requestedAligned']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  rw [Wasm.wp_globalGet_cons, frontier]
  wp_run
  simp [currentBase]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [currentAligned']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [noWrap']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [memory32, noGrow']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [frontier, setFrontierStore, UInt32.add_comm] at returned ⊢
  exact returned

/-- Exact scalar execution of the resident allocator when it grows linear
memory.  `grown` is Talos's atomic `memory.grow` contract; the W6 corollary
constructs it from the page arithmetic and module capacity. -/
theorem wp_allocateProgram_grow
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {frontierIndex : Nat} {requested current : UInt32}
    {grownMemory : Wasm.Mem}
    (memory32 : module.memIs64 = false)
    (frontier : store.globals.globals[frontierIndex]? = some (.i32 current))
    (requestedMinimum : ¬ requested < 32)
    (requestedAligned : requested &&& 7 = 0)
    (currentBase : ¬ current < 1024)
    (currentAligned : current &&& 7 = 0)
    (noWrap : ¬ current + requested < current)
    (grow : UInt32.ofNat store.mem.pages <
      pagesForEndWord (current + requested))
    (grown : store.mem.grow
      (pagesForEndWord (current + requested) - UInt32.ofNat store.mem.pages)
      (store.memoryCap module 0) = some (grownMemory, store.mem.pages))
    (growResultValid : UInt32.ofNat store.mem.pages ≠ 4294967295)
    (returned : Q (.Return
      (setFrontierStore { store with mem := grownMemory } frontierIndex
        (current + requested))
      [.i32 current])) :
    Wasm.wp module (allocateProgram frontierIndex) Q store
      (allocateEntry requested) env := by
  have requestedAligned' : 7 &&& requested = 0 := by
    simpa [UInt32.and_comm] using requestedAligned
  have currentAligned' : 7 &&& current = 0 := by
    simpa [UInt32.and_comm] using currentAligned
  have noWrap' : ¬ requested + current < current := by
    simpa [UInt32.add_comm] using noWrap
  simp [pagesForEndWord, UInt32.add_comm] at grow grown
  unfold allocateProgram requireAlignedProgram pagesForEndProgram allocateEntry
  simp only [trapWhenTrueProgram, List.cons_append, List.nil_append]
  wp_run
  simp [requestedMinimum]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [requestedAligned']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  rw [Wasm.wp_globalGet_cons, frontier]
  wp_run
  simp [currentBase]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [currentAligned']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [noWrap']
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [memory32, grow]
  apply Wasm.wp_iff_cons rfl
  simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
  wp_run
  simp [grown, growResultValid]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp [frontier, setFrontierStore, UInt32.add_comm] at returned ⊢
  exact returned

/-- A successful W6 raw allocation is realized by the emitted resident
allocator.  The strict endpoint premise exposes the sole current discrepancy
between the two contracts: W6 still admits the unrepresentable cursor `2^32`,
whereas the resident wasm32 allocator must reject it. -/
theorem wp_allocateProgram_of_allocate
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {before after : MemoryState} {store : Wasm.Store host}
    {frontierIndex requestedBytes : Nat} {address : Word32}
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (requestedAligned : requestedBytes % target.heapAlignment = 0)
    (allocated : before.allocate requestedBytes = .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      Wasm.wp module (allocateProgram frontierIndex)
        (fun completion => completion = .Return finalStore
          [.i32 (UInt32.ofNat address.value)])
        store (allocateEntry (UInt32.ofNat requestedBytes)) env := by
  let requiredPages := (after.heapCursor - 1) / wasmPageBytes + 1
  let finalMemory : Wasm.Mem := {
    store.mem with pages := max store.mem.pages requiredPages }
  let finalStore := setFrontierStore { store with mem := finalMemory }
    frontierIndex (UInt32.ofNat after.heapCursor)
  have post := MemoryState.allocate_spec before after requestedBytes address
    allocated
  have beforeAligned8 : before.heapCursor % 8 = 0 := by
    simpa [target] using valid.cursorAligned
  have requestAligned8 : requestedBytes % 8 = 0 := by
    simpa [target] using requestedAligned
  have beforeAlignEq : align8 before.heapCursor = before.heapCursor :=
    align8_eq_of_mod_eq_zero before.heapCursor beforeAligned8
  have requestAlignEq : align8 requestedBytes = requestedBytes :=
    align8_eq_of_mod_eq_zero requestedBytes requestAligned8
  have cursorEq : after.heapCursor = before.heapCursor + requestedBytes := by
    simpa [beforeAlignEq, requestAlignEq] using post.cursor
  have memoryEq : after.memory =
      before.memory.growToFit after.heapCursor := by
    rw [post.memory, post.cursor]
  have addressEq : address.value = before.heapCursor := by
    simpa [beforeAlignEq] using post.addressValue
  have beforeFits32 : before.heapCursor < UInt32.size := by
    simpa [wordModulus, UInt32.size] using related.frontierFits
  have afterFits32 : after.heapCursor < UInt32.size := by
    simpa [wordModulus, UInt32.size] using strictEnd
  have requestedFits32 : requestedBytes < UInt32.size := by
    omega
  have afterPositive : 0 < after.heapCursor := by
    have basePositive : 0 < heapBase := by decide
    exact lt_of_lt_of_le basePositive
      (Nat.le_trans related.frontierBase (by omega))
  have requestedMinimum : ¬ UInt32.ofNat requestedBytes < 32 := by
    have minimum32 : 32 ≤ requestedBytes := by
      simpa [headerBytes] using post.minimum
    intro tooSmall
    have naturalTooSmall := UInt32.lt_iff_toNat_lt.mp tooSmall
    have constant32 : (32 : UInt32).toNat = 32 := by decide
    rw [UInt32.toNat_ofNat_of_lt' requestedFits32, constant32] at naturalTooSmall
    omega
  have currentBase : ¬ UInt32.ofNat before.heapCursor < 1024 := by
    have base1024 : 1024 ≤ before.heapCursor := by
      simpa [heapBase] using related.frontierBase
    intro belowBase
    have naturalBelow := UInt32.lt_iff_toNat_lt.mp belowBase
    have constant1024 : (1024 : UInt32).toNat = 1024 := by decide
    rw [UInt32.toNat_ofNat_of_lt' beforeFits32, constant1024] at naturalBelow
    omega
  have requestedWordAligned : UInt32.ofNat requestedBytes &&& 7 = 0 :=
    alignedWord_of_mod8 requestedFits32 requestAligned8
  have currentWordAligned : UInt32.ofNat before.heapCursor &&& 7 = 0 :=
    alignedWord_of_mod8 beforeFits32 beforeAligned8
  have additionWord : UInt32.ofNat before.heapCursor +
      UInt32.ofNat requestedBytes = UInt32.ofNat after.heapCursor := by
    rw [← UInt32.ofNat_add, cursorEq]
  have noWrap : ¬ UInt32.ofNat before.heapCursor +
      UInt32.ofNat requestedBytes < UInt32.ofNat before.heapCursor := by
    intro wrapped
    rw [additionWord] at wrapped
    have naturalWrapped := UInt32.lt_iff_toNat_lt.mp wrapped
    rw [UInt32.toNat_ofNat_of_lt' afterFits32,
      UInt32.toNat_ofNat_of_lt' beforeFits32] at naturalWrapped
    omega
  have requiredPagesBound : requiredPages ≤ 65536 := by
    have quotientLt : (after.heapCursor - 1) / 65536 < 65536 := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 65536)]
      unfold wordModulus at strictEnd
      omega
    simpa [requiredPages, wasmPageBytes] using (show
      (after.heapCursor - 1) / 65536 + 1 ≤ 65536 by omega)
  have requiredPagesFits32 : requiredPages < UInt32.size := by
    unfold UInt32.size
    omega
  have oldPagesBound : store.mem.pages ≤ 65536 := by
    have sizeBound := related.toResidentMemoryRel.size_le
    rw [related.toResidentMemoryRel.size_eq] at sizeBound
    unfold wasmPageBytes UInt32.size at sizeBound
    omega
  have oldPagesFits32 : store.mem.pages < UInt32.size := by
    unfold UInt32.size
    omega
  have pageWord : pagesForEndWord (UInt32.ofNat before.heapCursor +
      UInt32.ofNat requestedBytes) = UInt32.ofNat requiredPages := by
    apply UInt32.toNat_inj.mp
    rw [additionWord, UInt32.toNat_ofNat_of_lt' requiredPagesFits32]
    simpa [pagesForEndWord, requiredPages] using
      ResidentAllocatorRel.pagesForEnd_word_toNat afterPositive afterFits32
  have finalPageBound : max store.mem.pages requiredPages ≤ 65536 :=
    max_le oldPagesBound requiredPagesBound
  have finalSizeBound : max store.mem.pages requiredPages * wasmPageBytes ≤
      UInt32.size := by
    unfold wasmPageBytes UInt32.size
    omega
  have grownSize := ResidentAllocatorRel.growToFit_size_eq_max_pages related
    after.heapCursor afterPositive
  have memoryRelatedRaw := ResidentAllocatorRel.growToFit related
    after.heapCursor grownSize finalSizeBound
  have memoryRelated : ResidentMemoryRel after finalMemory := by
    refine {
      size_eq := by
        simpa [memoryEq, finalMemory, requiredPages] using
          memoryRelatedRaw.size_eq
      size_le := by
        simpa [memoryEq] using memoryRelatedRaw.size_le
      byte_eq := ?_ }
    intro other inBounds
    have rawBounds : other <
        ({ before with memory := before.memory.growToFit after.heapCursor } :
          MemoryState).memory.size := by
      simpa [memoryEq] using inBounds
    simpa [memoryEq, finalMemory, requiredPages] using
      memoryRelatedRaw.byte_eq other rawBounds
  have extension := valid.allocate_prefixExtension allocated
  have zeroAfter : ∀ other, after.memory.size ≤ other →
      finalMemory.bytes other = 0 := by
    intro other afterExtent
    have beforeExtent : before.memory.size ≤ other :=
      Nat.le_trans extension.memorySize afterExtent
    simpa [finalMemory] using related.zeroAfterExtent other beforeExtent
  have finalBase : heapBase ≤ after.heapCursor := by
    exact Nat.le_trans related.frontierBase (by omega)
  have finalRelated : ResidentAllocatorRel after finalStore frontierIndex := by
    simpa [finalStore] using setFrontierStore_related related memoryRelated
      finalBase strictEnd zeroAfter
  refine ⟨finalStore, finalRelated, ?_⟩
  by_cases grows : store.mem.pages < requiredPages
  · have growsWord : UInt32.ofNat store.mem.pages <
        pagesForEndWord (UInt32.ofNat before.heapCursor +
          UInt32.ofNat requestedBytes) := by
      rw [pageWord, UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' oldPagesFits32,
        UInt32.toNat_ofNat_of_lt' requiredPagesFits32]
      exact grows
    have grown := ResidentAllocatorRel.mem_grow_to_pages store.mem requiredPages
      (store.memoryCap module 0) (Nat.le_of_lt grows) requiredPagesFits32
      (by simpa [requiredPages] using withinCap)
    have grownFinal : store.mem.grow
        (pagesForEndWord (UInt32.ofNat before.heapCursor +
          UInt32.ofNat requestedBytes) - UInt32.ofNat store.mem.pages)
        (store.memoryCap module 0) = some (finalMemory, store.mem.pages) := by
      rw [pageWord]
      rw [← UInt32.ofNat_sub (Nat.le_of_lt grows)]
      simpa [finalMemory, Nat.max_eq_right (Nat.le_of_lt grows)] using grown
    have growResultValid : UInt32.ofNat store.mem.pages ≠ 4294967295 := by
      intro impossible
      have equalNats := congrArg UInt32.toNat impossible
      rw [UInt32.toNat_ofNat_of_lt' oldPagesFits32] at equalNats
      have sentinel : (4294967295 : UInt32).toNat = 4294967295 := by decide
      rw [sentinel] at equalNats
      omega
    apply wp_allocateProgram_grow memory32 related.frontier requestedMinimum
      requestedWordAligned currentBase currentWordAligned noWrap growsWord
      grownFinal growResultValid
    simp only [addressEq]
    rw [additionWord]
  · have noGrowsWord : ¬ UInt32.ofNat store.mem.pages <
        pagesForEndWord (UInt32.ofNat before.heapCursor +
          UInt32.ofNat requestedBytes) := by
      rw [pageWord, UInt32.not_lt, UInt32.le_iff_toNat_le,
        UInt32.toNat_ofNat_of_lt' requiredPagesFits32,
        UInt32.toNat_ofNat_of_lt' oldPagesFits32]
      exact Nat.le_of_not_gt grows
    have finalMemoryEq : finalMemory = store.mem := by
      change { store.mem with pages := max store.mem.pages requiredPages } =
        store.mem
      rw [Nat.max_eq_left (Nat.le_of_not_gt grows)]
    apply wp_allocateProgram_noGrow memory32 related.frontier requestedMinimum
      requestedWordAligned currentBase currentWordAligned noWrap noGrowsWord
    simp only [finalStore, finalMemoryEq, addressEq]
    rw [additionWord]

/-- Canonical Talos function shape of the resident raw allocator.  Keeping
the optional physical suffix explicit lets execution proofs compose with the
adapter without assuming how its terminal-marker policy evolves. -/
def allocateTargetFunction (frontierIndex : Nat)
    (suffix : Wasm.Program := []) : Wasm.Function := {
  params := [.i32]
  locals := [.i32, .i32, .i32, .i32, .i32]
  results := [.i32]
  body := allocateProgram frontierIndex ++ suffix }

set_option maxRecDepth 2048 in
/-- The symbolic allocator adapts exactly to the target body above.  This
pins the proof to W7's public emitter definition while keeping its private
identifier names out of the theorem statement. -/
theorem instructions_allocateFunction
    {sourceModule : Fir.Wasm.Module} {frontierIndex : Nat} :
    FirTalos.instructions sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) []
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex).body =
        .ok (allocateProgram frontierIndex) := by
  let source := Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex
  have requestedFound : FirTalos.findFVar?
      (source.params.toList ++ source.locals.toList) source.params[0]!.1 =
        some 0 := by rfl
  have currentFound : FirTalos.findFVar?
      (source.params.toList ++ source.locals.toList) source.locals[0]!.1 =
        some 1 := by rfl
  have endFound : FirTalos.findFVar?
      (source.params.toList ++ source.locals.toList) source.locals[1]!.1 =
        some 2 := by rfl
  have requiredPagesFound : FirTalos.findFVar?
      (source.params.toList ++ source.locals.toList) source.locals[2]!.1 =
        some 3 := by rfl
  have currentPagesFound : FirTalos.findFVar?
      (source.params.toList ++ source.locals.toList) source.locals[3]!.1 =
        some 4 := by rfl
  have growResultFound : FirTalos.findFVar?
      (source.params.toList ++ source.locals.toList) source.locals[4]!.1 =
        some 5 := by rfl
  change FirTalos.instructions sourceModule source [] source.body = _
  rw [allocateFunction_shape]
  simp [source, allocateSourceProgram, requireAlignedSource,
    pagesForEndSource, trapWhenTrueSource, allocateProgram,
    requireAlignedProgram, pagesForEndProgram, trapWhenTrueProgram,
    FirTalos.instructions, FirTalos.instruction,
    requestedFound, currentFound, endFound, requiredPagesFound,
    currentPagesFound, growResultFound, Bind.bind, Except.bind, pure,
    Except.pure]
  decide

/-- Successful adaptation produces the complete canonical target function,
not merely a body fragment.  Call-level proofs can therefore recover the
parameter, local, result, and terminal-suffix conventions from one fact. -/
theorem adaptedAllocateFunction_eq
    {sourceModule : Fir.Wasm.Module} {frontierIndex : Nat}
    {targetFunction : Wasm.Function}
    (adapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok targetFunction) :
    targetFunction = allocateTargetFunction frontierIndex
      (FirTalos.functionTerminal sourceModule
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex)) := by
  unfold FirTalos.function at adapted
  rw [instructions_allocateFunction] at adapted
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at adapted
  simpa [allocateTargetFunction,
    Fir.Wasm.Emit.ResidentAllocator.allocateFunction, FirTalos.abiKind,
    Fir.Wasm.AbiKind.valueType, FirTalos.valueType] using adapted.symm

/-- Successful adaptation installs the proved allocator body followed only
by the adapter's standard physical terminal suffix. -/
theorem adaptedAllocateFunction_body
    {sourceModule : Fir.Wasm.Module} {frontierIndex : Nat}
    {targetFunction : Wasm.Function}
    (adapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok targetFunction) :
    targetFunction.body = allocateProgram frontierIndex ++
      FirTalos.functionTerminal sourceModule
        (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) := by
  rw [adaptedAllocateFunction_eq adapted]
  rfl

/-- A successful checked W6 allocation yields the exact total-correctness
theorem for the actual adapted resident allocator call.  This is the reusable
call boundary for every resident object constructor: clients no longer carry
an independently trusted `TerminatesWith` premise for `fir_heap_alloc`. -/
theorem terminatesWith_allocateFunction_of_allocate
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {targetFunction : Wasm.Function}
    {functionIndex frontierIndex : Nat}
    {before after : MemoryState} {store : Wasm.Store host}
    {requestedBytes : Nat} {address : Word32}
    (adapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (requestedAligned : requestedBytes % target.heapAlignment = 0)
    (allocated : before.allocate requestedBytes = .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      Wasm.TerminatesWith env module functionIndex store
        [.i32 (UInt32.ofNat requestedBytes)]
        (fun final values =>
          final = finalStore ∧
            values = [.i32 (UInt32.ofNat address.value)]) := by
  obtain ⟨finalStore, finalRelated, coreWP⟩ :=
    wp_allocateProgram_of_allocate memory32 valid related requestedAligned
      allocated strictEnd withinCap
  refine ⟨finalStore, finalRelated, ?_⟩
  have targetShape := adaptedAllocateFunction_eq adapted
  rw [targetShape] at found
  let suffix := FirTalos.functionTerminal sourceModule
    (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex)
  let targetFunction' := allocateTargetFunction frontierIndex suffix
  refine FirTalos.Correctness.terminatesWith_of_wp_body_at
    (function := targetFunction')
    (Post := fun final values =>
      final = finalStore ∧
        values = [.i32 (UInt32.ofNat address.value)])
    notImport (by simpa [targetFunction', suffix] using found) ?_
  have coreWP' : Wasm.wp module (allocateProgram frontierIndex)
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (targetFunction'.toLocals
        (([.i32 (UInt32.ofNat requestedBytes)] : List Wasm.Value).take
          targetFunction'.numParams).reverse) env := by
    simpa [targetFunction', allocateTargetFunction, allocateEntry,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero] using coreWP
  have physicalWP : Wasm.wp module targetFunction'.body
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (targetFunction'.toLocals
        (([.i32 (UInt32.ofNat requestedBytes)] : List Wasm.Value).take
          targetFunction'.numParams).reverse) env := by
    change Wasm.wp module (allocateProgram frontierIndex ++ suffix) _ _ _ _
    exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
      (by intros; simp) coreWP'
  apply Wasm.wp.conseq _ physicalWP
  intro completion completed
  subst completion
  simp [FirTalos.Correctness.FunctionBodyPost, targetFunction',
    allocateTargetFunction, Wasm.Function.numParams]

end ResidentAllocator

end FirTalos.Concrete
