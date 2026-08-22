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

end ResidentBigNumericAllocator

end FirTalos.Concrete
