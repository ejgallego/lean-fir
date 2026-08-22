import Fir.Wasm.Emit.ResidentBigNumeric
import FirTalos.ConcreteResidentAllocator
import FirTalos.Correctness.Adapter
import FirTalos.Correctness.Function
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident BigNumeric object allocator refinement

This module connects W7's shared BigNumeric header installer to the raw
resident allocator proved in `ConcreteResidentAllocator`.  The generic raw
reservation and the eight common-header stores remain separate proof layers
so every other resident object family can reuse the same boundaries.
-/

namespace ResidentBigNumericAllocator

/-- Public W6 spelling of the emitter's private scale-by-eight sequence. -/
def scale8Source (source destination : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .localGet source,
  .localGet source,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination,
  .localGet destination,
  .localGet destination,
  .i32Add,
  .localSet destination]

/-- Public W6 spelling of the emitter's private checked-false trap. -/
def trapUnlessTrueSource (condition : List Fir.Wasm.Instruction) :
    List Fir.Wasm.Instruction :=
  ResidentAllocator.trapWhenTrueSource
    (condition ++ [.i32Const .uint32 0, .i32Eq])

/-- Public spelling of the complete W7 BigNumeric allocation body. -/
def allocateObjectSourceProgram
    (kind marker sign count scaled address : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  trapUnlessTrueSource [
    .localGet count,
    .i32Const .uint32 536870908,
    .i32LtU] ++
  scale8Source count scaled ++ [
    .i32Const .uint32 (UInt32.ofNat headerBytes),
    .localGet scaled,
    .i32Add,
    .call (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName),
    .localSet address,
    .localGet address,
    .localGet kind,
    .i32Store .uint32 (UInt32.ofNat headerKindOffset),
    .localGet address,
    .i32Const .uint32 liveFlag,
    .i32Store .uint32 (UInt32.ofNat headerFlagsOffset),
    .localGet address,
    .i32Const .uint32 1,
    .i32Store .uint32 (UInt32.ofNat headerRefCountOffset),
    .localGet address,
    .i32Const .uint32 (UInt32.ofNat headerBytes),
    .localGet scaled,
    .i32Add,
    .i32Store .uint32 (UInt32.ofNat headerAllocationBytesOffset),
    .localGet address,
    .localGet marker,
    .i32Store .uint32 (UInt32.ofNat headerAux0Offset),
    .localGet address,
    .localGet count,
    .i32Store .uint32 (UInt32.ofNat headerAux1Offset),
    .localGet address,
    .localGet sign,
    .i32Store .uint32 (UInt32.ofNat headerAux2Offset),
    .localGet address,
    .i32Const .uint32 0,
    .i32Store .uint32 (UInt32.ofNat headerAux3Offset),
    .localGet address,
    .ret]

/-- The public W7 function has exactly the proof-side source shape. -/
theorem allocateFunction_shape :
    Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.body =
      allocateObjectSourceProgram
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[1]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[2]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[3]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals[1]!.1 := by
  rfl

/-- Talos spelling of `scale8Source`. -/
def scale8Program (sourceIndex destinationIndex : Nat) : Wasm.Program := [
  .localGet sourceIndex,
  .localGet sourceIndex,
  .add,
  .localSet destinationIndex,
  .localGet destinationIndex,
  .localGet destinationIndex,
  .add,
  .localSet destinationIndex,
  .localGet destinationIndex,
  .localGet destinationIndex,
  .add,
  .localSet destinationIndex]

/-- Exact modular result of W7's three doublings. -/
def scale8Word (count : UInt32) : UInt32 :=
  let twice := count + count
  let fourTimes := twice + twice
  fourTimes + fourTimes

/-- The resident three-doubling sequence is exactly one W6 semantic-slot
extent, modulo the physical word as required by Wasm arithmetic. -/
theorem scale8Word_ofNat (limbCount : Nat) :
    scale8Word (UInt32.ofNat limbCount) =
      UInt32.ofNat (target.semanticSlotBytes * limbCount) := by
  simp only [scale8Word]
  rw [← UInt32.ofNat_add, ← UInt32.ofNat_add, ← UInt32.ofNat_add]
  congr
  simp [target]
  omega

/-- A BigNumeric payload contains whole eight-byte semantic slots, so its
common-header extent is already allocator-aligned. -/
theorem objectAllocationBytes_eq (limbCount : Nat) :
    align8 (headerBytes + target.semanticSlotBytes * limbCount) =
      headerBytes + target.semanticSlotBytes * limbCount := by
  apply align8_eq_of_mod_eq_zero
  simp [headerBytes, target]

/-- Talos spelling of the checked count guard. -/
def trapUnlessTrueProgram (condition : Wasm.Program) : Wasm.Program :=
  ResidentAllocator.trapWhenTrueProgram (condition ++ [.const 0, .eq])

/-- Exact adapted body of `fir_big_numeric_allocate`. -/
def allocateObjectProgram (allocatorIndex : Nat) : Wasm.Program :=
  trapUnlessTrueProgram [.localGet 3, .const 536870908, .ltU] ++
  scale8Program 3 4 ++ [
    .const (UInt32.ofNat headerBytes),
    .localGet 4,
    .add,
    .call allocatorIndex,
    .localSet 5,
    .localGet 5,
    .localGet 0,
    .store32 (UInt32.ofNat headerKindOffset),
    .localGet 5,
    .const liveFlag,
    .store32 (UInt32.ofNat headerFlagsOffset),
    .localGet 5,
    .const 1,
    .store32 (UInt32.ofNat headerRefCountOffset),
    .localGet 5,
    .const (UInt32.ofNat headerBytes),
    .localGet 4,
    .add,
    .store32 (UInt32.ofNat headerAllocationBytesOffset),
    .localGet 5,
    .localGet 1,
    .store32 (UInt32.ofNat headerAux0Offset),
    .localGet 5,
    .localGet 3,
    .store32 (UInt32.ofNat headerAux1Offset),
    .localGet 5,
    .localGet 2,
    .store32 (UInt32.ofNat headerAux2Offset),
    .localGet 5,
    .const 0,
    .store32 (UInt32.ofNat headerAux3Offset),
    .localGet 5,
    .ret]

/-- Canonical Talos function shape of the shared BigNumeric object allocator.
The adapter's optional physical terminal suffix remains explicit so the call
theorem depends on adaptation rather than a fixed suffix policy. -/
def allocateObjectTargetFunction (allocatorIndex : Nat)
    (suffix : Wasm.Program := []) : Wasm.Function := {
  params := [.i32, .i32, .i32, .i32]
  locals := [.i32, .i32]
  results := [.i32]
  body := allocateObjectProgram allocatorIndex ++ suffix }

/-- Concrete local frame of the four-parameter/two-local object allocator. -/
def allocateObjectEntry (kind marker sign count : UInt32) : Wasm.Locals := {
  params := [.i32 kind, .i32 marker, .i32 sign, .i32 count]
  locals := [.i32 0, .i32 0]
  values := [] }

/-- Stable local frame after the raw allocator result has been installed.
The frame is shared by the independent common-header execution theorem. -/
def allocatedObjectLocals
    (kind marker sign count address : UInt32) : Wasm.Locals := {
  params := [.i32 kind, .i32 marker, .i32 sign, .i32 count]
  locals := [.i32 (scale8Word count), .i32 address]
  values := [] }

/-- Local frame immediately before installing the returned raw address. -/
def scaledObjectLocals (kind marker sign count : UInt32) : Wasm.Locals := {
  params := [.i32 kind, .i32 marker, .i32 sign, .i32 count]
  locals := [.i32 (scale8Word count), .i32 0]
  values := [] }

/-- Header words physically installed by W7. -/
def headerWords (kind marker sign count : UInt32) : List UInt32 := [
  kind, liveFlag, 1, UInt32.ofNat headerBytes + scale8Word count,
  marker, count, sign, 0]

/-- Exact physical store produced by the eight common-header instructions.
This operation-specific layer stays compact while the generic adjacent-word
fold below supplies its W6 refinement boundary. -/
def writeHeaderStore (store : Wasm.Store host) (address kind marker sign count :
    UInt32) : Wasm.Store host :=
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerKindOffset) kind
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerFlagsOffset) liveFlag
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerRefCountOffset) 1
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerAllocationBytesOffset)
    (scale8Word count + UInt32.ofNat headerBytes)
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerAux0Offset) marker
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerAux1Offset) count
  let store := ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerAux2Offset) sign
  ResidentMemoryRel.write32Store store
    (address + UInt32.ofNat headerAux3Offset) 0

/-- The operation-specific eight-store spelling is exactly the generic
adjacent-word store fold. -/
theorem writeHeaderStore_eq_words
    (store : Wasm.Store host) (address kind marker sign count : UInt32) :
    writeHeaderStore store address kind marker sign count =
      ResidentMemoryRel.writeUInt32sStore store address
        (headerWords kind marker sign count) := by
  simp [writeHeaderStore, ResidentMemoryRel.writeUInt32sStore, headerWords,
    headerKindOffset, headerFlagsOffset, headerRefCountOffset,
    headerAllocationBytesOffset, headerAux0Offset, headerAux1Offset,
    headerAux2Offset, headerAux3Offset, headerBytes]
  ac_rfl

/-- W6's canonical nonpersistent allocation header has exactly the words
installed by the resident BigNumeric writer once the allocation-size word is
identified. -/
theorem forAllocation_words
    (kind : ObjectKind) (allocationBytes : Nat)
    (marker sign count : UInt32)
    (allocationWord : UInt32.ofNat allocationBytes =
      UInt32.ofNat headerBytes + scale8Word count) :
    (Header.forAllocation kind allocationBytes false marker count sign 0).words =
      headerWords kind.code marker sign count := by
  simp [Header.words, Header.forAllocation, Header.flags, headerWords,
    allocationWord, liveFlag]

/-- The compact eight-store writer refines any successful W6 header write
whose canonical words match the BigNumeric header. -/
theorem writeHeaderStore_refines
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Word32} {header : Header} {result : LinearMemory}
    {kind marker sign count : UInt32}
    (words : header.words = headerWords kind marker sign count)
    (inBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : header.write heap.memory address = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      (writeHeaderStore store (UInt32.ofNat address.value)
        kind marker sign count) frontierIndex := by
  have refined := related.writeHeader inBounds written
  rw [writeHeaderStore_eq_words, ResidentMemoryRel.writeUInt32sStore_eq,
    ← words]
  exact refined

/-- Canonical nonpersistent allocation-header specialization used by Nat and
Int object constructors. -/
theorem writeAllocationHeaderStore_refines
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Word32} {result : LinearMemory} {kind : ObjectKind}
    {allocationBytes : Nat} {marker sign count : UInt32}
    (allocationWord : UInt32.ofNat allocationBytes =
      UInt32.ofNat headerBytes + scale8Word count)
    (inBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : (Header.forAllocation kind allocationBytes false marker count
      sign 0).write heap.memory address = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      (writeHeaderStore store (UInt32.ofNat address.value)
        kind.code marker sign count) frontierIndex := by
  apply writeHeaderStore_refines related
  · exact forAllocation_words kind allocationBytes marker sign count
      allocationWord
  · exact inBounds
  · exact written

/-- Exact scalar execution of the BigNumeric object allocator after its raw
allocator call has returned. -/
theorem wp_allocateObjectProgram
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store allocatedStore : Wasm.Store host}
    {allocatorIndex : Nat} {kind marker sign count address : UInt32}
    (countFits : count < 536870908)
    (allocateRun : Wasm.TerminatesWith env module allocatorIndex store
      [.i32 (UInt32.ofNat headerBytes + scale8Word count)]
      (fun final values =>
        final = allocatedStore ∧ values = [.i32 address]))
    (headerInBounds : address.toNat + headerBytes ≤
      allocatedStore.mem.pages * wasmPageBytes)
    (returned : Q (.Return
      (writeHeaderStore allocatedStore address kind marker sign count)
      [.i32 address])) :
    Wasm.wp module (allocateObjectProgram allocatorIndex) Q store
      (allocateObjectEntry kind marker sign count) env := by
  unfold allocateObjectProgram trapUnlessTrueProgram allocateObjectEntry
  unfold scale8Program
  simp only [ResidentAllocator.trapWhenTrueProgram, List.cons_append,
    List.nil_append]
  wp_run
  simp [countFits]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  simp
  have requestEq :
      count + count + (count + count) +
          (count + count + (count + count)) + UInt32.ofNat headerBytes =
        UInt32.ofNat headerBytes + scale8Word count := by
    simp only [scale8Word]
    ac_rfl
  simp [headerBytes, wasmPageBytes] at headerInBounds
  have bound4 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 4 := by
    omega
  have bound8 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 8 := by
    omega
  have bound12 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 12 := by
    omega
  have bound16 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 16 := by
    omega
  have bound20 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 20 := by
    omega
  have bound24 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 24 := by
    omega
  have bound28 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 28 := by
    omega
  have bound32 : ¬ allocatedStore.mem.pages * 65536 < address.toNat + 32 := by
    omega
  apply Wasm.wp_call_tw (by
    simpa only [requestEq] using allocateRun)
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply FirTalos.Correctness.wp_localSet_of_set
    (locals := scaledObjectLocals kind marker sign count)
    (updated := allocatedObjectLocals kind marker sign count address)
    (tail := [])
  · simp [Wasm.Locals.set?, scaledObjectLocals, allocatedObjectLocals]
  · apply ResidentMemoryRel.wp_store32_localGet_of_inBounds
      (address := address) (value := kind)
      (offset := UInt32.ofNat headerKindOffset)
      (addressIndex := 5) (valueIndex := 0)
    · simp [allocatedObjectLocals, Wasm.Locals.get]
    · simp [allocatedObjectLocals, Wasm.Locals.get]
    · simp [headerKindOffset, wasmPageBytes]
      omega
    · apply ResidentMemoryRel.wp_store32_const_of_inBounds
        (address := address) (value := liveFlag)
        (offset := UInt32.ofNat headerFlagsOffset) (addressIndex := 5)
      · simp [allocatedObjectLocals, Wasm.Locals.get]
      · simp [headerFlagsOffset, wasmPageBytes]
        omega
      · apply ResidentMemoryRel.wp_store32_const_of_inBounds
          (address := address) (value := 1)
          (offset := UInt32.ofNat headerRefCountOffset) (addressIndex := 5)
        · simp [allocatedObjectLocals, Wasm.Locals.get]
        · simp [headerRefCountOffset, wasmPageBytes]
          omega
        · apply ResidentMemoryRel.wp_store32_constAddLocalGet_of_inBounds
            (address := address) (constant := UInt32.ofNat headerBytes)
            (value := scale8Word count)
            (offset := UInt32.ofNat headerAllocationBytesOffset)
            (addressIndex := 5) (valueIndex := 4)
          · simp [allocatedObjectLocals, Wasm.Locals.get]
          · simp [allocatedObjectLocals, Wasm.Locals.get]
          · simp [headerAllocationBytesOffset, wasmPageBytes]
            omega
          · apply ResidentMemoryRel.wp_store32_localGet_of_inBounds
              (address := address) (value := marker)
              (offset := UInt32.ofNat headerAux0Offset)
              (addressIndex := 5) (valueIndex := 1)
            · simp [allocatedObjectLocals, Wasm.Locals.get]
            · simp [allocatedObjectLocals, Wasm.Locals.get]
            · simp [headerAux0Offset, wasmPageBytes]
              omega
            · apply ResidentMemoryRel.wp_store32_localGet_of_inBounds
                (address := address) (value := count)
                (offset := UInt32.ofNat headerAux1Offset)
                (addressIndex := 5) (valueIndex := 3)
              · simp [allocatedObjectLocals, Wasm.Locals.get]
              · simp [allocatedObjectLocals, Wasm.Locals.get]
              · simp [headerAux1Offset, wasmPageBytes]
                omega
              · apply ResidentMemoryRel.wp_store32_localGet_of_inBounds
                  (address := address) (value := sign)
                  (offset := UInt32.ofNat headerAux2Offset)
                  (addressIndex := 5) (valueIndex := 2)
                · simp [allocatedObjectLocals, Wasm.Locals.get]
                · simp [allocatedObjectLocals, Wasm.Locals.get]
                · simp [headerAux2Offset, wasmPageBytes]
                  omega
                · apply ResidentMemoryRel.wp_store32_const_of_inBounds
                    (address := address) (value := 0)
                    (offset := UInt32.ofNat headerAux3Offset)
                    (addressIndex := 5)
                  · simp [allocatedObjectLocals, Wasm.Locals.get]
                  · simp [headerAux3Offset, wasmPageBytes]
                    omega
                  · apply ResidentMemoryRel.wp_localGet_return
                      (index := 5) (value := address)
                    · simp [allocatedObjectLocals, Wasm.Locals.get]
                    · simpa [writeHeaderStore] using returned

/-- A successful W6 object allocation is realized by the complete emitted
BigNumeric allocation body using the actual adapted `fir_heap_alloc` callee.
The result relates the fully header-initialized W6 state to the exact physical
store returned by the Wasm helper. -/
theorem wp_allocateObjectProgram_of_allocateObject
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {targetAllocator : Wasm.Function}
    {allocatorIndex frontierIndex : Nat}
    {before after : MemoryState} {store : Wasm.Store host}
    {kind : ObjectKind} {marker sign : UInt32} {limbCount : Nat}
    {address : Word32}
    (allocatorAdapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok targetAllocator)
    (allocatorNotImport : module.imports[allocatorIndex]? = none)
    (allocatorFound :
      module.funcs[allocatorIndex - module.imports.length]? =
        some targetAllocator)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (countFits : limbCount < 536870908)
    (allocated : before.allocateObject kind
      (target.semanticSlotBytes * limbCount) false marker
      (UInt32.ofNat limbCount) sign 0 = .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      Wasm.wp module (allocateObjectProgram allocatorIndex)
        (fun completion => completion = .Return finalStore
          [.i32 (UInt32.ofNat address.value)]) store
        (allocateObjectEntry kind.code marker sign
          (UInt32.ofNat limbCount)) env := by
  obtain ⟨middle, rawAllocation, headerWritten, cursorEq, _⟩ :=
    MemoryState.allocateObject_header before after kind
      (target.semanticSlotBytes * limbCount) false marker
      (UInt32.ofNat limbCount) sign 0 address allocated
  have requestedAligned :
      align8 (headerBytes + target.semanticSlotBytes * limbCount) %
          target.heapAlignment = 0 := by
    change align8 (headerBytes + target.semanticSlotBytes * limbCount) % 8 = 0
    exact align8_mod (headerBytes + target.semanticSlotBytes * limbCount)
  have middleStrict : middle.heapCursor < wordModulus := by
    rw [← cursorEq]
    exact strictEnd
  have middleWithinCap :
      (middle.heapCursor - 1) / wasmPageBytes + 1 ≤
        store.memoryCap module 0 := by
    rw [← cursorEq]
    exact withinCap
  obtain ⟨allocatedStore, middleRelated, allocatorRun⟩ :=
    ResidentAllocator.terminatesWith_allocateFunction_of_allocate
      allocatorAdapted allocatorNotImport allocatorFound memory32 valid related
      requestedAligned rawAllocation middleStrict middleWithinCap
  have countFits32 : limbCount < UInt32.size := by
    unfold UInt32.size
    omega
  have countFitsWord : UInt32.ofNat limbCount < 536870908 := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' countFits32]
    exact countFits
  have allocationWord :
      UInt32.ofNat
          (align8 (headerBytes + target.semanticSlotBytes * limbCount)) =
        UInt32.ofNat headerBytes + scale8Word (UInt32.ofNat limbCount) := by
    rw [objectAllocationBytes_eq, scale8Word_ofNat,
      ← UInt32.ofNat_add]
  have allocatorRun' : Wasm.TerminatesWith env module allocatorIndex store
      [.i32 (UInt32.ofNat headerBytes +
        scale8Word (UInt32.ofNat limbCount))]
      (fun final values =>
        final = allocatedStore ∧
          values = [.i32 (UInt32.ofNat address.value)]) := by
    simpa only [allocationWord] using allocatorRun
  have rawPost := MemoryState.allocate_spec before middle
    (align8 (headerBytes + target.semanticSlotBytes * limbCount)) address
    rawAllocation
  have headerInBounds :
      address.value + headerBytes ≤ middle.memory.size := by
    have endInBounds := rawPost.endInBounds
    rw [align8_align8] at endInBounds
    have minimum := align8_ge
      (headerBytes + target.semanticSlotBytes * limbCount)
    omega
  have addressFits : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have physicalHeaderInBounds :
      (UInt32.ofNat address.value).toNat + headerBytes ≤
        allocatedStore.mem.pages * wasmPageBytes := by
    rw [UInt32.toNat_ofNat_of_lt' addressFits,
      ← middleRelated.toResidentMemoryRel.size_eq]
    exact headerInBounds
  let finalStore := writeHeaderStore allocatedStore
    (UInt32.ofNat address.value) kind.code marker sign
      (UInt32.ofNat limbCount)
  have finalRelatedRaw := writeAllocationHeaderStore_refines middleRelated
    allocationWord headerInBounds headerWritten
  have stateEq : ({ middle with memory := after.memory } : MemoryState) =
      after := by
    cases middle
    cases after
    simp_all
  have finalRelated : ResidentAllocatorRel after finalStore frontierIndex := by
    rw [← stateEq]
    simpa [finalStore] using finalRelatedRaw
  refine ⟨finalStore, finalRelated, ?_⟩
  apply wp_allocateObjectProgram countFitsWord allocatorRun'
    physicalHeaderInBounds
  rfl

/-- The full symbolic object allocator adapts exactly to the target program. -/
theorem instructions_allocateFunction
    {sourceModule : Fir.Wasm.Module} {allocatorIndex : Nat}
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.body =
        .ok (allocateObjectProgram allocatorIndex) := by
  have kindFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[0]!.1 =
        some 0 := by decide
  have markerFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[1]!.1 =
        some 1 := by decide
  have signFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[2]!.1 =
        some 2 := by decide
  have countFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params[3]!.1 =
        some 3 := by decide
  have scaledFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals[0]!.1 =
        some 4 := by decide
  have addressFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals.toList)
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction.locals[1]!.1 =
        some 5 := by decide
  rw [allocateFunction_shape]
  set_option maxRecDepth 100000 in
    simp [allocateObjectSourceProgram, allocateObjectProgram,
      trapUnlessTrueSource, trapUnlessTrueProgram,
      ResidentAllocator.trapWhenTrueSource,
      ResidentAllocator.trapWhenTrueProgram, scale8Source, scale8Program,
      FirTalos.instructions, FirTalos.instruction, allocatorFound, kindFound,
      markerFound, signFound, countFound, scaledFound, addressFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Successful adaptation produces the complete canonical BigNumeric
allocator function, including its call index and physical terminal suffix. -/
theorem adaptedAllocateObjectFunction_eq
    {sourceModule : Fir.Wasm.Module} {allocatorIndex : Nat}
    {targetFunction : Wasm.Function}
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex)
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction =
        .ok targetFunction) :
    targetFunction = allocateObjectTargetFunction allocatorIndex
      (FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction) := by
  unfold FirTalos.function at adapted
  rw [instructions_allocateFunction allocatorFound] at adapted
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at adapted
  simpa [allocateObjectTargetFunction,
    Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction, FirTalos.abiKind,
    Fir.Wasm.AbiKind.valueType, FirTalos.valueType] using adapted.symm

/-- Call-level total correctness for the actual adapted BigNumeric allocator.
The caller's operand tail is preserved exactly, and the returned physical
address is related to the fully initialized W6 object state. -/
theorem terminatesWith_allocateObjectFunction_of_allocateObject
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host}
    {targetFunction targetAllocator : Wasm.Function}
    {functionIndex allocatorIndex frontierIndex : Nat}
    {before after : MemoryState} {store : Wasm.Store host}
    {kind : ObjectKind} {marker sign : UInt32} {limbCount : Nat}
    {address : Word32} {tail : List Wasm.Value}
    (allocatorCallFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex)
    (objectAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction =
        .ok targetFunction)
    (objectNotImport : module.imports[functionIndex]? = none)
    (objectFound :
      module.funcs[functionIndex - module.imports.length]? =
        some targetFunction)
    (allocatorAdapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok targetAllocator)
    (allocatorNotImport : module.imports[allocatorIndex]? = none)
    (allocatorFound :
      module.funcs[allocatorIndex - module.imports.length]? =
        some targetAllocator)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (countFits : limbCount < 536870908)
    (allocated : before.allocateObject kind
      (target.semanticSlotBytes * limbCount) false marker
      (UInt32.ofNat limbCount) sign 0 = .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      Wasm.TerminatesWith env module functionIndex store
        ([.i32 (UInt32.ofNat limbCount), .i32 sign, .i32 marker,
          .i32 kind.code] ++ tail)
        (fun final values =>
          final = finalStore ∧
            values = .i32 (UInt32.ofNat address.value) :: tail) := by
  obtain ⟨finalStore, finalRelated, coreWP⟩ :=
    wp_allocateObjectProgram_of_allocateObject allocatorAdapted
      allocatorNotImport allocatorFound memory32 valid related countFits
      allocated strictEnd withinCap
  refine ⟨finalStore, finalRelated, ?_⟩
  have targetShape :=
    adaptedAllocateObjectFunction_eq allocatorCallFound objectAdapted
  rw [targetShape] at objectFound
  let suffix := FirTalos.functionTerminal sourceModule
    Fir.Wasm.Emit.ResidentBigNumeric.allocateFunction
  let targetFunction' := allocateObjectTargetFunction allocatorIndex suffix
  let args : List Wasm.Value :=
    [.i32 (UInt32.ofNat limbCount), .i32 sign, .i32 marker, .i32 kind.code] ++
      tail
  refine FirTalos.Correctness.terminatesWith_of_wp_body_at
    (function := targetFunction') (args := args)
    (Post := fun final values =>
      final = finalStore ∧
        values = .i32 (UInt32.ofNat address.value) :: tail)
    objectNotImport
    (by simpa [targetFunction', suffix] using objectFound) ?_
  have coreWP' : Wasm.wp module (allocateObjectProgram allocatorIndex)
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (targetFunction'.toLocals
        (args.take targetFunction'.numParams).reverse) env := by
    simpa [targetFunction', allocateObjectTargetFunction,
      allocateObjectEntry, args, Wasm.Function.toLocals,
      Wasm.Function.numParams, Wasm.ValueType.zero] using coreWP
  have physicalWP : Wasm.wp module targetFunction'.body
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (targetFunction'.toLocals
        (args.take targetFunction'.numParams).reverse) env := by
    change Wasm.wp module (allocateObjectProgram allocatorIndex ++ suffix)
      _ _ _ _
    exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
      (by intros; simp) coreWP'
  apply Wasm.wp.conseq _ physicalWP
  intro completion completed
  subst completion
  simp [FirTalos.Correctness.FunctionBodyPost, targetFunction',
    allocateObjectTargetFunction, args, Wasm.Function.numParams]

end ResidentBigNumericAllocator

end FirTalos.Concrete
