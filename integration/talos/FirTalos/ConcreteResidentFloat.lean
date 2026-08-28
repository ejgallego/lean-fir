import Fir.Wasm.Emit.ResidentFloat
import Fir.Wasm.Concrete.BoxingCorrectness
import FirTalos.ConcreteResidentAllocator
import FirTalos.ConcreteResidentScalarBox

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident `Float32` and `Float` box refinement

This module connects W7's production floating box/unbox functions to W6's
heap-only, bit-exact concrete scalar contract.  The shared definitions below
make the common allocation, zero-initialization, header validation, scratch
retyping, installation, and malformed-layout boundaries explicit; the two
width-specific proofs differ only at the payload reinterpret/store/load.
-/

namespace ResidentFloat

private def u32 (value : Nat) : UInt32 := UInt32.ofNat value

def equalsConstSource (kind : Fir.Wasm.AbiKind) (value : UInt32) :
    List Fir.Wasm.Instruction :=
  [.i32Const kind value, .i32Eq]

def trapUnlessSource (condition : List Fir.Wasm.Instruction) :
    List Fir.Wasm.Instruction :=
  condition ++ [.ifElse [] [.unreachable]]

/-- Exact floating-helper heap guard.  Unlike the older scalar-box helper,
the below-heap branch traps directly before the alignment equality guard. -/
def requireHeapAddressSource (object : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  [.localGet object,
    .i32Const .uint32 (u32 heapBase),
    .i32LtU,
    .ifElse [.unreachable] [],
    .localGet object,
    .i32Const .uint32 (u32 (target.heapAlignment - 1)),
    .i32And] ++
  equalsConstSource .uint32 0 ++
  [.ifElse [] [.unreachable]]

def requireHeaderWordSource (object : Lean.FVarId) (offset : Nat)
    (value : UInt32) : List Fir.Wasm.Instruction :=
  trapUnlessSource ([.localGet object, .i32Load .uint32 (u32 offset)] ++
    equalsConstSource .uint32 value)

def storeAddress32Source (address : Lean.FVarId)
    (value : List Fir.Wasm.Instruction) (offset : Nat) :
    List Fir.Wasm.Instruction :=
  [.localGet address] ++ value ++ [.i32Store .uint32 (u32 offset)]

/-- Proof-side spelling of W7's unrolled zero initialization. -/
def zeroAllocationSource (address : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  storeAddress32Source address [.i32Const .uint32 0] 0 ++
  storeAddress32Source address [.i32Const .uint32 0] 4 ++
  storeAddress32Source address [.i32Const .uint32 0] 8 ++
  storeAddress32Source address [.i32Const .uint32 0] 12 ++
  storeAddress32Source address [.i32Const .uint32 0] 16 ++
  storeAddress32Source address [.i32Const .uint32 0] 20 ++
  storeAddress32Source address [.i32Const .uint32 0] 24 ++
  storeAddress32Source address [.i32Const .uint32 0] 28 ++
  storeAddress32Source address [.i32Const .uint32 0] 32 ++
  storeAddress32Source address [.i32Const .uint32 0] 36

/-- Source prefix common to production Float32 and Float allocation. -/
def boxPrefixSource (address : Lean.FVarId) (marker payloadBytes : UInt32) :
    List Fir.Wasm.Instruction :=
  [.i32Const .uint32 40,
    .call (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName),
    .localSet address] ++
  zeroAllocationSource address ++
  storeAddress32Source address
    [.i32Const .uint32 ObjectKind.boxed.code] headerKindOffset ++
  storeAddress32Source address
    [.i32Const .uint32 liveFlag] headerFlagsOffset ++
  storeAddress32Source address
    [.i32Const .uint32 1] headerRefCountOffset ++
  storeAddress32Source address
    [.i32Const .uint32 40] headerAllocationBytesOffset ++
  storeAddress32Source address
    [.i32Const .uint32 marker] headerAux0Offset ++
  storeAddress32Source address
    [.i32Const .uint32 payloadBytes] headerAux1Offset

/-- Proof-side spelling of W7's address-to-object scratch retyping. -/
def retypeAddressSource (address saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction := [
  .i32Const .uint32 0,
  .i32Load .uint32 0,
  .localSet saved,
  .i32Const .uint32 0,
  .localGet address,
  .i32Store .uint32 0,
  .i32Const .uint32 0,
  .i32Load .object 0,
  .localSet result,
  .i32Const .uint32 0,
  .localGet saved,
  .i32Store .uint32 0,
  .localGet result,
  .ret]

def float32BoxSourceProgram (value address saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  boxPrefixSource address BoxedScalarKind.float32.code 4 ++
  [.localGet address,
    .localGet value,
    .i32ReinterpretF32 .uint32,
    .i32Store .uint32 (u32 headerBytes)] ++
  retypeAddressSource address saved result

def floatBoxSourceProgram (value address saved result : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  boxPrefixSource address BoxedScalarKind.float.code 8 ++
  [.localGet address,
    .localGet value,
    .i64ReinterpretF64 .uint64,
    .i64Store .uint64 (u32 headerBytes)] ++
  retypeAddressSource address saved result

/-- Shared checked floating header prefix, including Float32's zero-padding
guard when `checkHighPadding` is true. -/
def unboxPrefixSource (object : Lean.FVarId) (marker payloadBytes : UInt32)
    (checkHighPadding : Bool) : List Fir.Wasm.Instruction :=
  requireHeapAddressSource object ++
  trapUnlessSource ([.localGet object,
    .i32Load .uint32 (u32 headerFlagsOffset),
    .i32Const .uint32 liveFlag, .i32And] ++
    equalsConstSource .uint32 liveFlag) ++
  requireHeaderWordSource object headerKindOffset
    ObjectKind.boxed.code ++
  requireHeaderWordSource object headerAux0Offset marker ++
  requireHeaderWordSource object headerAllocationBytesOffset 40 ++
  requireHeaderWordSource object headerAux1Offset payloadBytes ++
  requireHeaderWordSource object headerAux2Offset 0 ++
  requireHeaderWordSource object headerAux3Offset 0 ++
  if checkHighPadding then
    requireHeaderWordSource object (headerBytes + 4) 0
  else
    []

def float32UnboxSourceProgram (object : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  unboxPrefixSource object BoxedScalarKind.float32.code 4 true ++
  [.localGet object,
    .i32Load .uint32 (u32 headerBytes),
    .f32ReinterpretI32 .float32,
    .ret]

def floatUnboxSourceProgram (object : Lean.FVarId) :
    List Fir.Wasm.Instruction :=
  unboxPrefixSource object BoxedScalarKind.float.code 8 false ++
  [.localGet object,
    .i64Load .uint64 (u32 headerBytes),
    .f64ReinterpretI64 .float,
    .ret]

theorem float32BoxFunction_shape :
    Fir.Wasm.Emit.ResidentFloat.float32BoxFunction.body =
      float32BoxSourceProgram
        Fir.Wasm.Emit.ResidentFloat.float32BoxFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentFloat.float32BoxFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentFloat.float32BoxFunction.locals[1]!.1
        Fir.Wasm.Emit.ResidentFloat.float32BoxFunction.locals[2]!.1 := by
  rfl

theorem floatBoxFunction_shape :
    Fir.Wasm.Emit.ResidentFloat.boxFunction.body =
      floatBoxSourceProgram
        Fir.Wasm.Emit.ResidentFloat.boxFunction.params[0]!.1
        Fir.Wasm.Emit.ResidentFloat.boxFunction.locals[0]!.1
        Fir.Wasm.Emit.ResidentFloat.boxFunction.locals[1]!.1
        Fir.Wasm.Emit.ResidentFloat.boxFunction.locals[2]!.1 := by
  rfl

theorem float32UnboxFunction_shape :
    Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction.body =
      float32UnboxSourceProgram
        Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction.params[0]!.1 := by
  rfl

theorem floatUnboxFunction_shape :
    Fir.Wasm.Emit.ResidentFloat.unboxFunction.body =
      floatUnboxSourceProgram
        Fir.Wasm.Emit.ResidentFloat.unboxFunction.params[0]!.1 := by
  rfl

/-- Talos spelling of the unrolled 40-byte zero initialization. -/
def zeroAllocationProgram (address : Nat) : Wasm.Program :=
  [.localGet address, .const 0, .store32 0,
    .localGet address, .const 0, .store32 4,
    .localGet address, .const 0, .store32 8,
    .localGet address, .const 0, .store32 12,
    .localGet address, .const 0, .store32 16,
    .localGet address, .const 0, .store32 20,
    .localGet address, .const 0, .store32 24,
    .localGet address, .const 0, .store32 28,
    .localGet address, .const 0, .store32 32,
    .localGet address, .const 0, .store32 36]

/-- Six descriptor-dependent header writes after the zeroed common header. -/
def boxHeaderWriteProgram (address : Nat) (marker payloadBytes : UInt32) :
    Wasm.Program :=
  [.localGet address, .const ObjectKind.boxed.code,
      .store32 (u32 headerKindOffset),
    .localGet address, .const liveFlag,
      .store32 (u32 headerFlagsOffset),
    .localGet address, .const 1,
      .store32 (u32 headerRefCountOffset),
    .localGet address, .const 40,
      .store32 (u32 headerAllocationBytesOffset),
    .localGet address, .const marker,
      .store32 (u32 headerAux0Offset),
    .localGet address, .const payloadBytes,
      .store32 (u32 headerAux1Offset)]

/-- Physical Talos prefix common to both floating box helpers. -/
def boxPrefixProgram (allocatorIndex address : Nat)
    (marker payloadBytes : UInt32) : Wasm.Program :=
  [.const 40, .call allocatorIndex, .localSet address] ++
  zeroAllocationProgram address ++
  boxHeaderWriteProgram address marker payloadBytes

/-- Physical scratch cast used by both floating box helpers. -/
def retypeAddressProgram (address saved result : Nat) : Wasm.Program := [
  .const 0, .load32 0, .localSet saved,
  .const 0, .localGet address, .store32 0,
  .const 0, .load32 0, .localSet result,
  .const 0, .localGet saved, .store32 0,
  .localGet result, .ret]

def trapUnlessProgram (condition : Wasm.Program) : Wasm.Program :=
  condition ++ [.iff 0 0 [] [.unreachable]]

def requireHeapAddressProgram : Wasm.Program :=
  [.localGet 0, .const (u32 heapBase), .ltU,
    .iff 0 0 [.unreachable] [],
    .localGet 0, .const (u32 (target.heapAlignment - 1)), .and,
    .const 0, .eq, .iff 0 0 [] [.unreachable]]

def requireHeaderWordProgram (offset : Nat) (value : UInt32) : Wasm.Program :=
  trapUnlessProgram [.localGet 0, .load32 (u32 offset), .const value, .eq]

def float32BoxProgram (allocatorIndex : Nat) : Wasm.Program :=
  boxPrefixProgram allocatorIndex 1 BoxedScalarKind.float32.code 4 ++
  [.localGet 1, .localGet 0, .i32ReinterpretF32,
    .store32 (u32 headerBytes)] ++
  retypeAddressProgram 1 2 3

def floatBoxProgram (allocatorIndex : Nat) : Wasm.Program :=
  boxPrefixProgram allocatorIndex 1 BoxedScalarKind.float.code 8 ++
  [.localGet 1, .localGet 0, .i64ReinterpretF64,
    .store64 (u32 headerBytes)] ++
  retypeAddressProgram 1 2 3

def unboxPrefixProgram (marker payloadBytes : UInt32)
    (checkHighPadding : Bool) : Wasm.Program :=
  requireHeapAddressProgram ++
  trapUnlessProgram [.localGet 0,
    .load32 (u32 headerFlagsOffset), .const liveFlag, .and,
    .const liveFlag, .eq] ++
  requireHeaderWordProgram headerKindOffset
    ObjectKind.boxed.code ++
  requireHeaderWordProgram headerAux0Offset marker ++
  requireHeaderWordProgram headerAllocationBytesOffset 40 ++
  requireHeaderWordProgram headerAux1Offset payloadBytes ++
  requireHeaderWordProgram headerAux2Offset 0 ++
  requireHeaderWordProgram headerAux3Offset 0 ++
  if checkHighPadding then
    requireHeaderWordProgram (headerBytes + 4) 0
  else
    []

def float32UnboxProgram : Wasm.Program :=
  unboxPrefixProgram BoxedScalarKind.float32.code 4 true ++
  [.localGet 0, .load32 (u32 headerBytes), .f32ReinterpretI32, .ret]

def floatUnboxProgram : Wasm.Program :=
  unboxPrefixProgram BoxedScalarKind.float.code 8 false ++
  [.localGet 0, .load64 (u32 headerBytes), .f64ReinterpretI64, .ret]

private theorem instructions_float32BoxSourceProgram
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {allocatorIndex : Nat} {value address saved result : Lean.FVarId}
    (shape : sourceFunction.body =
      float32BoxSourceProgram value address saved result)
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some 0)
    (addressFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) address =
        some 1)
    (savedFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) saved =
        some 2)
    (resultFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) result =
        some 3) :
    FirTalos.instructions sourceModule sourceFunction [] sourceFunction.body =
      .ok (float32BoxProgram allocatorIndex) := by
  rw [shape]
  set_option maxRecDepth 100000 in
    simp [float32BoxSourceProgram, boxPrefixSource, zeroAllocationSource,
      retypeAddressSource, storeAddress32Source,
      float32BoxProgram, boxPrefixProgram, zeroAllocationProgram,
      boxHeaderWriteProgram,
      retypeAddressProgram, u32, FirTalos.instructions, FirTalos.instruction,
      allocatorFound, valueFound, addressFound, savedFound, resultFound,
      Bind.bind, Except.bind, pure, Except.pure]

private theorem instructions_floatBoxSourceProgram
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {allocatorIndex : Nat} {value address saved result : Lean.FVarId}
    (shape : sourceFunction.body =
      floatBoxSourceProgram value address saved result)
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex)
    (valueFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) value =
        some 0)
    (addressFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) address =
        some 1)
    (savedFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) saved =
        some 2)
    (resultFound : FirTalos.findFVar?
      (sourceFunction.params.toList ++ sourceFunction.locals.toList) result =
        some 3) :
    FirTalos.instructions sourceModule sourceFunction [] sourceFunction.body =
      .ok (floatBoxProgram allocatorIndex) := by
  rw [shape]
  set_option maxRecDepth 100000 in
    simp [floatBoxSourceProgram, boxPrefixSource, zeroAllocationSource,
      retypeAddressSource, storeAddress32Source,
      floatBoxProgram, boxPrefixProgram, zeroAllocationProgram,
      boxHeaderWriteProgram,
      retypeAddressProgram, u32, FirTalos.instructions, FirTalos.instruction,
      allocatorFound, valueFound, addressFound, savedFound, resultFound,
      Bind.bind, Except.bind, pure, Except.pure]

theorem instructions_float32BoxFunction
    {sourceModule : Fir.Wasm.Module} {allocatorIndex : Nat}
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentFloat.float32BoxFunction []
      Fir.Wasm.Emit.ResidentFloat.float32BoxFunction.body =
        .ok (float32BoxProgram allocatorIndex) := by
  apply instructions_float32BoxSourceProgram float32BoxFunction_shape
    allocatorFound
  all_goals native_decide

theorem instructions_floatBoxFunction
    {sourceModule : Fir.Wasm.Module} {allocatorIndex : Nat}
    (allocatorFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
        some allocatorIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentFloat.boxFunction []
      Fir.Wasm.Emit.ResidentFloat.boxFunction.body =
        .ok (floatBoxProgram allocatorIndex) := by
  apply instructions_floatBoxSourceProgram floatBoxFunction_shape allocatorFound
  all_goals native_decide

theorem instructions_float32UnboxFunction
    {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction []
      Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction.body =
        .ok float32UnboxProgram := by
  have objectFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction.params.toList ++
        Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction.locals.toList)
      Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction.params[0]!.1 =
        some 0 := by native_decide
  rw [float32UnboxFunction_shape]
  set_option maxRecDepth 100000 in
    simp [float32UnboxSourceProgram, unboxPrefixSource,
      float32UnboxProgram, unboxPrefixProgram,
      requireHeapAddressSource, requireHeapAddressProgram,
      requireHeaderWordSource, requireHeaderWordProgram,
      trapUnlessSource, trapUnlessProgram, equalsConstSource,
      FirTalos.instructions, FirTalos.instruction, objectFound,
      Bind.bind, Except.bind, pure, Except.pure]

theorem instructions_floatUnboxFunction
    {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentFloat.unboxFunction []
      Fir.Wasm.Emit.ResidentFloat.unboxFunction.body =
        .ok floatUnboxProgram := by
  have objectFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentFloat.unboxFunction.params.toList ++
        Fir.Wasm.Emit.ResidentFloat.unboxFunction.locals.toList)
      Fir.Wasm.Emit.ResidentFloat.unboxFunction.params[0]!.1 = some 0 := by
    native_decide
  rw [floatUnboxFunction_shape]
  set_option maxRecDepth 100000 in
    simp [floatUnboxSourceProgram, unboxPrefixSource,
      floatUnboxProgram, unboxPrefixProgram,
      requireHeapAddressSource, requireHeapAddressProgram,
      requireHeaderWordSource, requireHeaderWordProgram,
      trapUnlessSource, trapUnlessProgram, equalsConstSource,
      FirTalos.instructions, FirTalos.instruction, objectFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Adapter-independent body recovery for one successfully translated source
function.  This is the common installed-helper boundary used by all four
floating exports. -/
theorem adapted_body_eq
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {targetFunction : Wasm.Function} {core : Wasm.Program}
    (adapted : FirTalos.function sourceModule sourceFunction =
      .ok targetFunction)
    (coreAdapted : FirTalos.instructions sourceModule sourceFunction []
      sourceFunction.body = .ok core) :
    targetFunction.body =
      core ++ FirTalos.functionTerminal sourceModule sourceFunction := by
  obtain ⟨targetBody, bodyAdapted, targetBodyEq⟩ :=
    FirTalos.Correctness.function_preserves_body adapted
  rw [coreAdapted] at bodyAdapted
  injection bodyAdapted with targetBodyEqCore
  simpa [targetBodyEqCore] using targetBodyEq

/-- Static adapter, resolver, and target-module evidence for the allocator and
all four production floating scalar exports.  The resolved indices are kept
explicit; no theorem-bearing certificate is added to the compiler. -/
structure Installation (sourceModule : Fir.Wasm.Module)
    (module : Wasm.Module) where
  allocatorTarget : Wasm.Function
  float32BoxTarget : Wasm.Function
  float32UnboxTarget : Wasm.Function
  floatBoxTarget : Wasm.Function
  floatUnboxTarget : Wasm.Function
  allocatorIndex : Nat
  float32BoxIndex : Nat
  float32UnboxIndex : Nat
  floatBoxIndex : Nat
  floatUnboxIndex : Nat
  frontierIndex : Nat
  allocatorAdapted : FirTalos.function sourceModule
    (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
      .ok allocatorTarget
  allocatorCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentAllocator.allocateName) =
      some allocatorIndex
  allocatorNotImport : module.imports[allocatorIndex]? = none
  allocatorInstalled :
    module.funcs[allocatorIndex - module.imports.length]? = some allocatorTarget
  float32BoxAdapted : FirTalos.function sourceModule
    Fir.Wasm.Emit.ResidentFloat.float32BoxFunction = .ok float32BoxTarget
  float32BoxCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentFloat.float32BoxName) =
      some float32BoxIndex
  float32BoxNotImport : module.imports[float32BoxIndex]? = none
  float32BoxInstalled :
    module.funcs[float32BoxIndex - module.imports.length]? =
      some float32BoxTarget
  float32UnboxAdapted : FirTalos.function sourceModule
    Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction = .ok float32UnboxTarget
  float32UnboxCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentFloat.float32UnboxName) =
      some float32UnboxIndex
  float32UnboxNotImport : module.imports[float32UnboxIndex]? = none
  float32UnboxInstalled :
    module.funcs[float32UnboxIndex - module.imports.length]? =
      some float32UnboxTarget
  floatBoxAdapted : FirTalos.function sourceModule
    Fir.Wasm.Emit.ResidentFloat.boxFunction = .ok floatBoxTarget
  floatBoxCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentFloat.boxName) = some floatBoxIndex
  floatBoxNotImport : module.imports[floatBoxIndex]? = none
  floatBoxInstalled :
    module.funcs[floatBoxIndex - module.imports.length]? = some floatBoxTarget
  floatUnboxAdapted : FirTalos.function sourceModule
    Fir.Wasm.Emit.ResidentFloat.unboxFunction = .ok floatUnboxTarget
  floatUnboxCall : FirTalos.callIndex? sourceModule
    (.declaration Fir.Wasm.Emit.ResidentFloat.unboxName) = some floatUnboxIndex
  floatUnboxNotImport : module.imports[floatUnboxIndex]? = none
  floatUnboxInstalled :
    module.funcs[floatUnboxIndex - module.imports.length]? =
      some floatUnboxTarget

theorem Installation.float32Box_signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.float32BoxTarget.params = [.f32] ∧
      installation.float32BoxTarget.locals = [.i32, .i32, .i32] ∧
      installation.float32BoxTarget.results = [.i32] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature
      installation.float32BoxAdapted
  exact ⟨by simpa [Fir.Wasm.Emit.ResidentFloat.float32BoxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using params,
    by simpa [Fir.Wasm.Emit.ResidentFloat.float32BoxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using locals,
    by simpa [Fir.Wasm.Emit.ResidentFloat.float32BoxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
      using results⟩

theorem Installation.floatBox_signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.floatBoxTarget.params = [.f64] ∧
      installation.floatBoxTarget.locals = [.i32, .i32, .i32] ∧
      installation.floatBoxTarget.results = [.i32] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature installation.floatBoxAdapted
  exact ⟨by simpa [Fir.Wasm.Emit.ResidentFloat.boxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using params,
    by simpa [Fir.Wasm.Emit.ResidentFloat.boxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using locals,
    by simpa [Fir.Wasm.Emit.ResidentFloat.boxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
      using results⟩

theorem Installation.float32Unbox_signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.float32UnboxTarget.params = [.i32] ∧
      installation.float32UnboxTarget.locals = [] ∧
      installation.float32UnboxTarget.results = [.f32] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature
      installation.float32UnboxAdapted
  exact ⟨by simpa [Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using params,
    by simpa [Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using locals,
    by simpa [Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
      using results⟩

theorem Installation.floatUnbox_signature
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.floatUnboxTarget.params = [.i32] ∧
      installation.floatUnboxTarget.locals = [] ∧
      installation.floatUnboxTarget.results = [.f64] := by
  obtain ⟨params, locals, results⟩ :=
    FirTalos.Correctness.function_preserves_signature installation.floatUnboxAdapted
  exact ⟨by simpa [Fir.Wasm.Emit.ResidentFloat.unboxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using params,
    by simpa [Fir.Wasm.Emit.ResidentFloat.unboxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType,
      Function.comp_def] using locals,
    by simpa [Fir.Wasm.Emit.ResidentFloat.unboxFunction,
      FirTalos.abiKind, FirTalos.valueType, Fir.Wasm.AbiKind.valueType]
      using results⟩

theorem Installation.float32Box_body
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.float32BoxTarget.body =
      float32BoxProgram installation.allocatorIndex ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentFloat.float32BoxFunction := by
  exact adapted_body_eq installation.float32BoxAdapted
    (instructions_float32BoxFunction installation.allocatorCall)

theorem Installation.floatBox_body
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.floatBoxTarget.body =
      floatBoxProgram installation.allocatorIndex ++
        FirTalos.functionTerminal sourceModule
          Fir.Wasm.Emit.ResidentFloat.boxFunction := by
  exact adapted_body_eq installation.floatBoxAdapted
    (instructions_floatBoxFunction installation.allocatorCall)

theorem Installation.float32Unbox_body
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.float32UnboxTarget.body = float32UnboxProgram ++
      FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentFloat.float32UnboxFunction := by
  exact adapted_body_eq installation.float32UnboxAdapted
    instructions_float32UnboxFunction

theorem Installation.floatUnbox_body
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module) :
    installation.floatUnboxTarget.body = floatUnboxProgram ++
      FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentFloat.unboxFunction := by
  exact adapted_body_eq installation.floatUnboxAdapted
    instructions_floatUnboxFunction

def float32BoxEntry (bits : UInt32) : Wasm.Locals := {
  params := [.f32 bits]
  locals := [.i32 0, .i32 0, .i32 0]
  values := [] }

def floatBoxEntry (bits : UInt64) : Wasm.Locals := {
  params := [.f64 bits]
  locals := [.i32 0, .i32 0, .i32 0]
  values := [] }

def unboxEntry (object : UInt32) : Wasm.Locals := {
  params := [.i32 object]
  locals := []
  values := [] }

/-- Exact physical store after W7's ten explicit zero stores. -/
def zeroAllocationStore (store : Wasm.Store host) (address : UInt32) :
    Wasm.Store host :=
  let store := ResidentMemoryRel.write32Store store (address + u32 0) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 4) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 8) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 12) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 16) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 20) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 24) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 28) 0
  let store := ResidentMemoryRel.write32Store store (address + u32 32) 0
  ResidentMemoryRel.write32Store store (address + u32 36) 0

/-- Exact physical store after the six nonzero or descriptor-dependent
common-header stores shared by both floating boxes. -/
def writeBoxHeaderStore (store : Wasm.Store host)
    (address marker payloadBytes :
    UInt32) : Wasm.Store host :=
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerKindOffset) ObjectKind.boxed.code
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerFlagsOffset) liveFlag
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerRefCountOffset) 1
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAllocationBytesOffset) 40
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAux0Offset) marker
  ResidentMemoryRel.write32Store store
    (address + u32 headerAux1Offset) payloadBytes

/-- Exact physical store after zero initialization and common-header writes. -/
def boxHeaderStore (store : Wasm.Store host) (address marker payloadBytes :
    UInt32) : Wasm.Store host :=
  writeBoxHeaderStore (zeroAllocationStore store address)
    address marker payloadBytes

def float32BoxStore (store : Wasm.Store host) (address bits : UInt32) :
    Wasm.Store host :=
  ResidentMemoryRel.write32Store
    (boxHeaderStore store address BoxedScalarKind.float32.code 4)
    (address + u32 headerBytes) bits

def floatBoxStore (store : Wasm.Store host) (address : UInt32)
    (bits : UInt64) : Wasm.Store host :=
  ResidentMemoryRel.write64Store
    (boxHeaderStore store address BoxedScalarKind.float.code 8)
    (address + u32 headerBytes) bits

@[simp] theorem zeroAllocationStore_pages
    (store : Wasm.Store host) (address : UInt32) :
    (zeroAllocationStore store address).mem.pages = store.mem.pages := by
  unfold zeroAllocationStore
  simp only [ResidentMemoryRel.write32Store_pages]

@[simp] theorem writeBoxHeaderStore_pages
    (store : Wasm.Store host) (address marker payloadBytes : UInt32) :
    (writeBoxHeaderStore store address marker payloadBytes).mem.pages =
      store.mem.pages := by
  unfold writeBoxHeaderStore
  simp only [ResidentMemoryRel.write32Store_pages]

@[simp] theorem boxHeaderStore_pages
    (store : Wasm.Store host) (address marker payloadBytes : UInt32) :
    (boxHeaderStore store address marker payloadBytes).mem.pages =
      store.mem.pages := by
  simp only [boxHeaderStore, writeBoxHeaderStore_pages,
    zeroAllocationStore_pages]

/-- A store of the word already present in one physical lane is a complete
store no-op.  Fresh-allocation proofs use the zero specialization to erase
W7's defensive initialization before comparing canonical W6 headers. -/
theorem write32Store_eq_self_of_read32
    (store : Wasm.Store host) (address value : UInt32)
    (read : store.mem.read32 address = value) :
    ResidentMemoryRel.write32Store store address value = store := by
  unfold ResidentMemoryRel.write32Store
  have memoryEq := ResidentMemoryRel.write32_read32_self store.mem address
  rw [read] at memoryEq
  cases store
  simp_all

set_option linter.unusedSimpArgs false in
/-- On a zero high word, storing a zero-extended 32-bit payload as eight bytes
is exactly the same physical update as storing its low four bytes. -/
theorem write64_toUInt64_eq_write32_of_high_zero
    (memory : Wasm.Mem) (address value : UInt32)
    (nonwrap : address.toNat + 8 ≤ UInt32.size)
    (highZero : memory.read32 (address + u32 4) = 0) :
    memory.write64 address value.toUInt64 = memory.write32 address value := by
  have highAddressToNat : (address + u32 4).toNat = address.toNat + 4 := by
    have fits : address.toNat + 4 < UInt32.size := by omega
    rw [show address + u32 4 = UInt32.ofNat (address.toNat + 4) by
      simp [u32, UInt32.ofNat_add]]
    exact UInt32.toNat_ofNat_of_lt' fits
  unfold Wasm.Mem.read32 at highZero
  simp only [highAddressToNat] at highZero
  have offset5 : address.toNat + 4 + 1 = address.toNat + 5 := by omega
  have offset6 : address.toNat + 4 + 2 = address.toNat + 6 := by omega
  have offset7 : address.toNat + 4 + 3 = address.toNat + 7 := by omega
  rw [offset5, offset6, offset7] at highZero
  have h4 : memory.bytes (address.toNat + 4) = 0 := by bv_decide
  have h5 : memory.bytes (address.toNat + 5) = 0 := by bv_decide
  have h6 : memory.bytes (address.toNat + 6) = 0 := by bv_decide
  have h7 : memory.bytes (address.toNat + 7) = 0 := by bv_decide
  cases memory
  simp only [Wasm.Mem.write64, Wasm.Mem.write32]
  congr 1
  funext other
  by_cases selected0 : other = address.toNat
  · subst other
    simp
  by_cases selected1 : other = address.toNat + 1
  · subst other
    simp [selected0]
    bv_decide
  by_cases selected2 : other = address.toNat + 2
  · subst other
    simp [selected0, selected1]
    bv_decide
  by_cases selected3 : other = address.toNat + 3
  · subst other
    simp [selected0, selected1, selected2]
    bv_decide
  by_cases selected4 : other = address.toNat + 4
  · subst other
    simp [selected0, selected1, selected2, selected3, h4]
    bv_decide
  by_cases selected5 : other = address.toNat + 5
  · subst other
    simp [selected0, selected1, selected2, selected3, selected4, h5]
    bv_decide
  by_cases selected6 : other = address.toNat + 6
  · subst other
    simp [selected0, selected1, selected2, selected3, selected4, selected5,
      h6]
    bv_decide
  by_cases selected7 : other = address.toNat + 7
  · subst other
    simp [selected0, selected1, selected2, selected3, selected4, selected5,
      selected6, h7]
    bv_decide
  simp [selected0, selected1, selected2, selected3, selected4, selected5,
    selected6, selected7]

/-- Width-parametric canonical common-header words for heap scalar boxes. -/
def boxHeaderWords (marker payloadBytes : UInt32) : List UInt32 := [
  ObjectKind.boxed.code, liveFlag, 1, 40, marker, payloadBytes, 0, 0]

/-- W6 header corresponding to `boxHeaderWords`. -/
def canonicalBoxHeader (marker payloadBytes : UInt32) : Header :=
  Header.forAllocation .boxed 40 false marker payloadBytes

/-- Physical eight-word canonical header store. -/
def canonicalBoxHeaderStore (store : Wasm.Store host) (address marker
    payloadBytes : UInt32) : Wasm.Store host :=
  let store := writeBoxHeaderStore store address marker payloadBytes
  let store := ResidentMemoryRel.write32Store store
    (address + u32 headerAux2Offset) 0
  ResidentMemoryRel.write32Store store
    (address + u32 headerAux3Offset) 0

theorem canonicalBoxHeaderStore_eq_words
    (store : Wasm.Store host) (address marker payloadBytes : UInt32) :
    canonicalBoxHeaderStore store address marker payloadBytes =
      ResidentMemoryRel.writeUInt32sStore store address
        (boxHeaderWords marker payloadBytes) := by
  simp [canonicalBoxHeaderStore, writeBoxHeaderStore,
    ResidentMemoryRel.writeUInt32sStore, boxHeaderWords,
    headerKindOffset, headerFlagsOffset, headerRefCountOffset,
    headerAllocationBytesOffset, headerAux0Offset, headerAux1Offset,
    headerAux2Offset, headerAux3Offset]
  ac_rfl

theorem canonicalBoxHeader_words (marker payloadBytes : UInt32) :
    (canonicalBoxHeader marker payloadBytes).words =
      boxHeaderWords marker payloadBytes := by
  simp [canonicalBoxHeader, boxHeaderWords, Header.words,
    Header.forAllocation, Header.flags, liveFlag]

/-- The generic physical scalar header refines the matching W6 header write.
Float32 and Float differ only in marker and payload width. -/
theorem canonicalBoxHeaderStore_refines
    {heap : MemoryState} {store : Wasm.Store host} {frontierIndex : Nat}
    (related : ResidentAllocatorRel heap store frontierIndex)
    {address : Word32} {marker payloadBytes : UInt32}
    {result : LinearMemory}
    (inBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : (canonicalBoxHeader marker payloadBytes).write
      heap.memory address = .ok result) :
    ResidentAllocatorRel { heap with memory := result }
      (canonicalBoxHeaderStore store (UInt32.ofNat address.value)
        marker payloadBytes) frontierIndex := by
  have refined := related.writeHeader inBounds written
  rw [canonicalBoxHeaderStore_eq_words,
    ResidentMemoryRel.writeUInt32sStore_eq,
    ← canonicalBoxHeader_words]
  exact refined

/-- Every complete 32-bit lane inside a fresh raw allocation is still zero
before an object header or payload is installed.  This is the checked W6 fact
behind W7's explicit defensive zero stores. -/
theorem rawAllocation_readUInt32_zero
    {before raw : MemoryState} {requestedBytes offset : Nat}
    {address : Word32}
    (valid : before.FrontierInvariant)
    (allocated : before.allocate requestedBytes = .ok (raw, address))
    (within : offset + 4 ≤ align8 requestedBytes) :
    raw.memory.readUInt32 (address.value + offset) = .ok 0 := by
  have post := MemoryState.allocate_spec before raw requestedBytes address
    allocated
  have cursorAligned : align8 before.heapCursor = before.heapCursor :=
    align8_eq_of_mod_eq_zero before.heapCursor (by
      simpa [target] using valid.cursorAligned)
  have zeroByte (byte : Nat) (afterAddress : address.value ≤ byte)
      (beforeEnd : byte < address.value + align8 requestedBytes) :
      raw.memory[byte]? = some 0 := by
    have afterCursor : before.heapCursor ≤ byte := by
      rw [post.addressValue, cursorAligned] at afterAddress
      exact afterAddress
    have rawInBounds : byte < raw.memory.size :=
      Nat.lt_of_lt_of_le beforeEnd post.endInBounds
    rw [post.memory] at rawInBounds ⊢
    exact LinearMemory.growToFit_zero_from before.memory before.heapCursor
      (align8 before.heapCursor + align8 requestedBytes)
      valid.unusedZero byte afterCursor rawInBounds
  have h0 : raw.memory[address.value + offset]? = some 0 :=
    zeroByte _ (by omega) (by omega)
  have h1 : raw.memory[address.value + offset + 1]? = some 0 :=
    zeroByte _ (by omega) (by omega)
  have h2 : raw.memory[address.value + offset + 2]? = some 0 :=
    zeroByte _ (by omega) (by omega)
  have h3 : raw.memory[address.value + offset + 3]? = some 0 :=
    zeroByte _ (by omega) (by omega)
  unfold LinearMemory.readUInt32 LinearMemory.readByte
  rw [h0, h1, h2, h3]
  rfl

/-- The physical Talos view of every fresh raw-allocation word is zero. -/
theorem rawAllocation_physicalRead32_zero
    {before raw : MemoryState} {store : Wasm.Store host}
    {requestedBytes offset : Nat} {address : Word32}
    (valid : before.FrontierInvariant)
    (allocated : before.allocate requestedBytes = .ok (raw, address))
    (related : ResidentMemoryRel raw store.mem)
    (within : offset + 4 ≤ align8 requestedBytes) :
    store.mem.read32
      (UInt32.ofNat address.value + u32 offset) = 0 := by
  have post := MemoryState.allocate_spec before raw requestedBytes address
    allocated
  have laneInBounds : address.value + offset + 3 < raw.memory.size :=
    Nat.lt_of_lt_of_le (by omega) post.endInBounds
  have transported := related.readUInt32_eq_read32 laneInBounds
  rw [rawAllocation_readUInt32_zero valid allocated within] at transported
  have exactRead := Except.ok.inj transported
  have physicalAddress :
      UInt32.ofNat address.value + u32 offset =
        UInt32.ofNat (address.value + offset) := by
    simp [u32, UInt32.ofNat_add]
  rw [physicalAddress]
  exact exactRead.symm

def allocationWordOffsets : List Nat := [0, 4, 8, 12, 16, 20, 24, 28,
  32, 36]

/-- Ten explicit zero stores disappear when all ten fresh words already read
as zero. -/
theorem zeroAllocationStore_eq_of_words_zero
    (store : Wasm.Store host) (address : UInt32)
    (zero : ∀ offset, offset ∈ allocationWordOffsets →
      store.mem.read32 (address + u32 offset) = 0) :
    zeroAllocationStore store address = store := by
  unfold zeroAllocationStore
  dsimp only
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 0 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 4 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 8 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 12 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 16 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 20 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 24 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 28 (by decide))]
  rw [write32Store_eq_self_of_read32 _ _ _ (zero 32 (by decide))]
  exact write32Store_eq_self_of_read32 _ _ _ (zero 36 (by decide))

/-- The six descriptor-dependent header writes preserve every later common
header lane.  The address-space premise rules out modular wraparound. -/
theorem writeBoxHeaderStore_read32_later
    (store : Wasm.Store host) (address marker payloadBytes : UInt32)
    (readOffset : Nat)
    (nonwrap : address.toNat + 40 ≤ UInt32.size)
    (later : headerAux1Offset + 4 ≤ readOffset)
    (within : readOffset + 4 ≤ 40) :
    (writeBoxHeaderStore store address marker payloadBytes).mem.read32
        (address + u32 readOffset) =
      store.mem.read32 (address + u32 readOffset) := by
  have offsetToNat (offset : Nat) (offsetWithin : offset + 4 ≤ 40) :
      (address + u32 offset).toNat = address.toNat + offset := by
    have fits : address.toNat + offset < UInt32.size := by omega
    rw [show address + u32 offset =
      UInt32.ofNat (address.toNat + offset) by
        simp [u32, UInt32.ofNat_add]]
    exact UInt32.toNat_ofNat_of_lt' fits
  have disjointAt (writtenOffset : Nat)
      (writtenBefore : writtenOffset + 4 ≤ readOffset)
      (writtenWithin : writtenOffset + 4 ≤ 40) :
      (address + u32 writtenOffset).toNat + 3 <
        (address + u32 readOffset).toNat := by
    rw [offsetToNat writtenOffset writtenWithin,
      offsetToNat readOffset within]
    omega
  unfold writeBoxHeaderStore
  simp only [ResidentMemoryRel.write32Store_mem]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerAux1Offset later (by decide)))]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerAux0Offset
      (Nat.le_trans (by decide) later) (by decide)))]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerAllocationBytesOffset
      (Nat.le_trans (by decide) later) (by decide)))]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerRefCountOffset
      (Nat.le_trans (by decide) later) (by decide)))]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerFlagsOffset
      (Nat.le_trans (by decide) later) (by decide)))]
  exact ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerKindOffset
      (Nat.le_trans (by decide) later) (by decide)))

/-- When the two reserved auxiliary lanes are already zero, W7's six header
writes are exactly the canonical eight-word W6 header store. -/
theorem canonicalBoxHeaderStore_eq_writeBoxHeaderStore
    (store : Wasm.Store host) (address marker payloadBytes : UInt32)
    (nonwrap : address.toNat + 40 ≤ UInt32.size)
    (aux2Zero : store.mem.read32 (address + u32 headerAux2Offset) = 0)
    (aux3Zero : store.mem.read32 (address + u32 headerAux3Offset) = 0) :
    canonicalBoxHeaderStore store address marker payloadBytes =
      writeBoxHeaderStore store address marker payloadBytes := by
  let headerStore := writeBoxHeaderStore store address marker payloadBytes
  have aux2After : headerStore.mem.read32
      (address + u32 headerAux2Offset) = 0 := by
    rw [writeBoxHeaderStore_read32_later store address marker payloadBytes
      headerAux2Offset nonwrap (by decide) (by decide)]
    exact aux2Zero
  have aux3After : headerStore.mem.read32
      (address + u32 headerAux3Offset) = 0 := by
    rw [writeBoxHeaderStore_read32_later store address marker payloadBytes
      headerAux3Offset nonwrap (by decide) (by decide)]
    exact aux3Zero
  unfold canonicalBoxHeaderStore
  dsimp only
  change ResidentMemoryRel.write32Store
      (ResidentMemoryRel.write32Store headerStore
        (address + u32 headerAux2Offset) 0)
      (address + u32 headerAux3Offset) 0 = headerStore
  rw [write32Store_eq_self_of_read32 headerStore
    (address + u32 headerAux2Offset) 0 aux2After]
  exact write32Store_eq_self_of_read32 headerStore
    (address + u32 headerAux3Offset) 0 aux3After

/-- The complete canonical header store preserves every later lane, including
the floating payload words. -/
theorem canonicalBoxHeaderStore_read32_later
    (store : Wasm.Store host) (address marker payloadBytes : UInt32)
    (readOffset : Nat)
    (nonwrap : address.toNat + 40 ≤ UInt32.size)
    (later : headerAux3Offset + 4 ≤ readOffset)
    (within : readOffset + 4 ≤ 40) :
    (canonicalBoxHeaderStore store address marker payloadBytes).mem.read32
        (address + u32 readOffset) =
      store.mem.read32 (address + u32 readOffset) := by
  have offsetToNat (offset : Nat) (offsetWithin : offset + 4 ≤ 40) :
      (address + u32 offset).toNat = address.toNat + offset := by
    have fits : address.toNat + offset < UInt32.size := by omega
    rw [show address + u32 offset =
      UInt32.ofNat (address.toNat + offset) by
        simp [u32, UInt32.ofNat_add]]
    exact UInt32.toNat_ofNat_of_lt' fits
  have disjointAt (writtenOffset : Nat)
      (writtenBefore : writtenOffset + 4 ≤ readOffset)
      (writtenWithin : writtenOffset + 4 ≤ 40) :
      (address + u32 writtenOffset).toNat + 3 <
        (address + u32 readOffset).toNat := by
    rw [offsetToNat writtenOffset writtenWithin,
      offsetToNat readOffset within]
    omega
  unfold canonicalBoxHeaderStore
  dsimp only
  simp only [ResidentMemoryRel.write32Store_mem]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerAux3Offset later (by decide)))]
  rw [ResidentMemoryRel.read32_write32_disjoint _ _ _ _
    (.inl (disjointAt headerAux2Offset
      (Nat.le_trans (by decide) later) (by decide)))]
  exact writeBoxHeaderStore_read32_later store address marker payloadBytes
    readOffset nonwrap (Nat.le_trans (by decide) later) within

/-- W7's complete zero-plus-header prefix is the canonical W6 header store
on a fresh zero allocation. -/
theorem boxHeaderStore_eq_canonical
    (store : Wasm.Store host) (address marker payloadBytes : UInt32)
    (nonwrap : address.toNat + 40 ≤ UInt32.size)
    (zeroed : zeroAllocationStore store address = store)
    (aux2Zero : store.mem.read32 (address + u32 headerAux2Offset) = 0)
    (aux3Zero : store.mem.read32 (address + u32 headerAux3Offset) = 0) :
    boxHeaderStore store address marker payloadBytes =
      canonicalBoxHeaderStore store address marker payloadBytes := by
  unfold boxHeaderStore
  rw [zeroed]
  exact (canonicalBoxHeaderStore_eq_writeBoxHeaderStore store address marker
    payloadBytes nonwrap aux2Zero aux3Zero).symm

def float32BoxAllocatedLocals (bits address : UInt32) : Wasm.Locals := {
  params := [.f32 bits]
  locals := [.i32 address, .i32 0, .i32 0]
  values := [] }

def floatBoxAllocatedLocals (bits : UInt64) (address : UInt32) : Wasm.Locals := {
  params := [.f64 bits]
  locals := [.i32 address, .i32 0, .i32 0]
  values := [] }

def float32BoxSavedLocals (bits address saved : UInt32) : Wasm.Locals := {
  params := [.f32 bits]
  locals := [.i32 address, .i32 saved, .i32 0]
  values := [.i32 saved] }

def floatBoxSavedLocals (bits : UInt64) (address saved : UInt32) : Wasm.Locals := {
  params := [.f64 bits]
  locals := [.i32 address, .i32 saved, .i32 0]
  values := [.i32 saved] }

def float32BoxResultLocals (bits address saved : UInt32) : Wasm.Locals := {
  params := [.f32 bits]
  locals := [.i32 address, .i32 saved, .i32 address]
  values := [.i32 address] }

def floatBoxResultLocals (bits : UInt64) (address saved : UInt32) : Wasm.Locals := {
  params := [.f64 bits]
  locals := [.i32 address, .i32 saved, .i32 address]
  values := [.i32 address] }

/-- Execute the ten-word zero initialization against one checked 40-byte
allocation.  The theorem is independent of the shape of the enclosing box
helper and is reusable by later resident constructors. -/
theorem wp_zeroAllocationProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address : UInt32} {addressIndex : Nat}
    {rest : Wasm.Program}
    (addressFound : locals.get addressIndex = some (.i32 address))
    (allocationInBounds : address.toNat + 40 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (zeroAllocationStore store address) locals env) :
    Wasm.wp module (zeroAllocationProgram addressIndex ++ rest) Q store
      locals env := by
  have bound (offset : Nat) (within : offset + 4 ≤ 40) :
      address.toNat + (u32 offset).toNat + 4 ≤
        store.mem.pages * wasmPageBytes := by
    have offsetFits : offset < UInt32.size := by
      unfold UInt32.size
      omega
    rw [show (u32 offset).toNat = offset by
      exact UInt32.toNat_ofNat_of_lt' offsetFits]
    exact Nat.le_trans (by omega) allocationInBounds
  unfold zeroAllocationProgram
  unfold zeroAllocationStore at continued
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (bound 0 (by decide))
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 4 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 8 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 12 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 16 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 20 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 24 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 28 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 32 (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound 36 (by decide)
  simpa [u32] using continued

/-- Execute the six width-independent common-header writes.  Zeroed aux2 and
aux3 lanes are deliberately supplied by `wp_zeroAllocationProgram`. -/
theorem wp_boxHeaderWriteProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address marker payloadBytes : UInt32}
    {addressIndex : Nat} {rest : Wasm.Program}
    (addressFound : locals.get addressIndex = some (.i32 address))
    (allocationInBounds : address.toNat + 40 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (writeBoxHeaderStore store address marker payloadBytes) locals env) :
    Wasm.wp module
      (boxHeaderWriteProgram addressIndex marker payloadBytes ++ rest)
      Q store locals env := by
  have bound (offset : Nat) (within : offset + 4 ≤ 40) :
      address.toNat + (u32 offset).toNat + 4 ≤
        store.mem.pages * wasmPageBytes := by
    have offsetFits : offset < UInt32.size := by
      unfold UInt32.size
      omega
    rw [show (u32 offset).toNat = offset by
      exact UInt32.toNat_ofNat_of_lt' offsetFits]
    exact Nat.le_trans (by omega) allocationInBounds
  unfold boxHeaderWriteProgram
  unfold writeBoxHeaderStore at continued
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (bound headerKindOffset (by decide))
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound headerFlagsOffset (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound headerRefCountOffset (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound headerAllocationBytesOffset (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound headerAux0Offset (by decide)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
  · simpa [u32] using bound headerAux1Offset (by decide)
  simpa [u32] using continued

/-- Execute W7's scratch-slot cast when the allocation address is already in
the raw local.  The temporary word-zero overwrite is restored exactly. -/
theorem wp_retypeAddressProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterSaved afterResult : Wasm.Locals}
    {address : UInt32} {addressIndex savedIndex resultIndex : Nat}
    (pagesPositive : 0 < store.mem.pages)
    (addressNeSaved : addressIndex ≠ savedIndex)
    (savedNeResult : savedIndex ≠ resultIndex)
    (initialValues : initial.values = [])
    (rawSet :
      ({ initial with values := [.i32 address] }).set?
          addressIndex (.i32 address) =
            some { initial with values := [.i32 address] })
    (savedSet :
      ({ initial with values := [.i32 (store.mem.read32 0)] }).set?
          savedIndex (.i32 (store.mem.read32 0)) = some afterSaved)
    (resultSet :
      ({ afterSaved with values := [.i32 address] }).set?
          resultIndex (.i32 address) = some afterResult)
    (returned : Q (.Return store [.i32 address])) :
    Wasm.wp module (retypeAddressProgram addressIndex savedIndex resultIndex)
      Q store initial env := by
  have full := ResidentNat.wp_retypeRawObjectResultProgram
    (module := module) (env := env)
    (initial := initial)
    (afterRaw := { initial with values := [.i32 address] })
    (afterSaved := afterSaved)
    (afterResult := afterResult) (rawValue := address) (tail := [])
    pagesPositive addressNeSaved savedNeResult rawSet savedSet resultSet returned
  unfold ResidentNat.retypeRawObjectResultProgram at full
  simp only [Wasm.wp_localSet_cons, rawSet] at full
  simpa [retypeAddressProgram, initialValues] using full

/-- Exact instruction-level execution of the production Float32 box body.
All forty initialized bytes and the scratch-slot cast are accounted for; the
result store is exposed without yet assuming a particular allocator proof. -/
theorem wp_float32BoxProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store allocatedStore : Wasm.Store host}
    {allocatorIndex : Nat} {bits address : UInt32}
    (allocateRun : Wasm.TerminatesWith env module allocatorIndex store
      [.i32 40]
      (fun final values => final = allocatedStore ∧ values = [.i32 address]))
    (allocationInBounds : address.toNat + 40 ≤
      allocatedStore.mem.pages * wasmPageBytes)
    (returned : Q (.Return (float32BoxStore allocatedStore address bits)
      [.i32 address])) :
    Wasm.wp module (float32BoxProgram allocatorIndex) Q store
      (float32BoxEntry bits) env := by
  have bound (offset bytes : Nat) (within : offset + bytes ≤ 40) :
      address.toNat + (u32 offset).toNat + bytes ≤
        allocatedStore.mem.pages * wasmPageBytes := by
    have offsetFits : offset < UInt32.size := by
      unfold UInt32.size
      omega
    rw [show (u32 offset).toNat = offset by
      exact UInt32.toNat_ofNat_of_lt' offsetFits]
    exact Nat.le_trans (by omega) allocationInBounds
  have pagesPositive : 0 <
      (float32BoxStore allocatedStore address bits).mem.pages := by
    have basePositive : 0 < allocatedStore.mem.pages := by
      unfold wasmPageBytes at allocationInBounds
      omega
    simpa [float32BoxStore, boxHeaderStore, writeBoxHeaderStore,
      zeroAllocationStore, ResidentMemoryRel.write32Store] using basePositive
  have allocatedAddress :
      (float32BoxAllocatedLocals bits address).get 1 =
        some (.i32 address) := by rfl
  unfold float32BoxProgram boxPrefixProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons]
  apply Wasm.wp_call_tw allocateRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply FirTalos.Correctness.wp_localSet_of_set
    (locals := float32BoxEntry bits)
    (updated := float32BoxAllocatedLocals bits address)
    (tail := [])
  · rfl
  · apply wp_zeroAllocationProgram allocatedAddress allocationInBounds
    apply wp_boxHeaderWriteProgram allocatedAddress
    · simpa [zeroAllocationStore, ResidentMemoryRel.write32Store] using
      allocationInBounds
    · change Wasm.wp module
        (.localGet 1 :: .localGet 0 :: .i32ReinterpretF32 ::
          .store32 (u32 headerBytes) :: retypeAddressProgram 1 2 3)
        Q (writeBoxHeaderStore (zeroAllocationStore final address)
          address BoxedScalarKind.float32.code 4)
        (float32BoxAllocatedLocals bits address) env
      simp only [Wasm.wp_localGet_cons, allocatedAddress,
        Wasm.wp_localGet_cons,
        Wasm.wp_i32ReinterpretF32_cons]
      apply ResidentMemoryRel.wp_store32_of_inBounds
      · simpa [boxHeaderStore, writeBoxHeaderStore, zeroAllocationStore,
          ResidentMemoryRel.write32Store] using
          bound headerBytes 4 (by decide)
      · change Wasm.wp module (retypeAddressProgram 1 2 3) Q
          (float32BoxStore final address bits)
          (float32BoxAllocatedLocals bits address) env
        let saved :=
          (float32BoxStore final address bits).mem.read32 0
        apply wp_retypeAddressProgram
          (initial := float32BoxAllocatedLocals bits address)
          (afterSaved := float32BoxSavedLocals bits address saved)
          (afterResult := float32BoxResultLocals bits address saved)
          (address := address) (addressIndex := 1) (savedIndex := 2)
          (resultIndex := 3)
          pagesPositive (by decide) (by decide)
        · rfl
        · simp [float32BoxAllocatedLocals, Wasm.Locals.set?]
        · simp [float32BoxAllocatedLocals, float32BoxSavedLocals,
            Wasm.Locals.set?, saved]
        · simp [float32BoxSavedLocals, float32BoxResultLocals,
            Wasm.Locals.set?, saved]
        · exact returned

/-- Exact instruction-level execution of the production Float box body.
The 64-bit payload lane is stored bit-for-bit, including every NaN payload,
and the scratch-slot cast restores word zero before returning. -/
theorem wp_floatBoxProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store allocatedStore : Wasm.Store host}
    {allocatorIndex : Nat} {bits : UInt64} {address : UInt32}
    (allocateRun : Wasm.TerminatesWith env module allocatorIndex store
      [.i32 40]
      (fun final values => final = allocatedStore ∧ values = [.i32 address]))
    (allocationInBounds : address.toNat + 40 ≤
      allocatedStore.mem.pages * wasmPageBytes)
    (returned : Q (.Return (floatBoxStore allocatedStore address bits)
      [.i32 address])) :
    Wasm.wp module (floatBoxProgram allocatorIndex) Q store
      (floatBoxEntry bits) env := by
  have bound (offset bytes : Nat) (within : offset + bytes ≤ 40) :
      address.toNat + (u32 offset).toNat + bytes ≤
        allocatedStore.mem.pages * wasmPageBytes := by
    have offsetFits : offset < UInt32.size := by
      unfold UInt32.size
      omega
    rw [show (u32 offset).toNat = offset by
      exact UInt32.toNat_ofNat_of_lt' offsetFits]
    exact Nat.le_trans (by omega) allocationInBounds
  have pagesPositive : 0 <
      (floatBoxStore allocatedStore address bits).mem.pages := by
    have basePositive : 0 < allocatedStore.mem.pages := by
      unfold wasmPageBytes at allocationInBounds
      omega
    simpa only [floatBoxStore, ResidentMemoryRel.write64Store_pages,
      boxHeaderStore_pages] using basePositive
  have payloadInBounds :
      address.toNat + (u32 headerBytes).toNat + 8 ≤
        (boxHeaderStore allocatedStore address BoxedScalarKind.float.code 8).mem.pages *
          wasmPageBytes := by
    simpa only [boxHeaderStore_pages] using
      bound headerBytes 8 (by decide)
  have allocatedAddress :
      (floatBoxAllocatedLocals bits address).get 1 =
        some (.i32 address) := by rfl
  have allocatedBits :
      (floatBoxAllocatedLocals bits address).get 0 = some (.f64 bits) := by
    rfl
  have allocatedBits' :
      ({ floatBoxAllocatedLocals bits address with
        values := .i32 address ::
          (floatBoxAllocatedLocals bits address).values }).get 0 =
        some (.f64 bits) := by
    simpa using allocatedBits
  unfold floatBoxProgram boxPrefixProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_const_cons]
  apply Wasm.wp_call_tw allocateRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  apply FirTalos.Correctness.wp_localSet_of_set
    (locals := floatBoxEntry bits)
    (updated := floatBoxAllocatedLocals bits address)
    (tail := [])
  · rfl
  · apply wp_zeroAllocationProgram allocatedAddress allocationInBounds
    apply wp_boxHeaderWriteProgram allocatedAddress
    · simpa [zeroAllocationStore, ResidentMemoryRel.write32Store] using
        allocationInBounds
    · change Wasm.wp module
        (.localGet 1 :: .localGet 0 :: .i64ReinterpretF64 ::
          .store64 (u32 headerBytes) :: retypeAddressProgram 1 2 3)
        Q (writeBoxHeaderStore (zeroAllocationStore final address)
          address BoxedScalarKind.float.code 8)
        (floatBoxAllocatedLocals bits address) env
      simp only [Wasm.wp_localGet_cons, allocatedAddress,
        Wasm.wp_localGet_cons, allocatedBits',
        Wasm.wp_i64ReinterpretF64_cons, Wasm.wp_store64_cons]
      rw [if_neg (Nat.not_lt.mpr (by
        simpa [wasmPageBytes] using payloadInBounds))]
      change Wasm.wp module (retypeAddressProgram 1 2 3) Q
        (floatBoxStore final address bits)
        (floatBoxAllocatedLocals bits address) env
      let saved := (floatBoxStore final address bits).mem.read32 0
      apply wp_retypeAddressProgram
        (initial := floatBoxAllocatedLocals bits address)
        (afterSaved := floatBoxSavedLocals bits address saved)
        (afterResult := floatBoxResultLocals bits address saved)
        (address := address) (addressIndex := 1) (savedIndex := 2)
        (resultIndex := 3)
        pagesPositive (by decide) (by decide)
      · rfl
      · simp [floatBoxAllocatedLocals, Wasm.Locals.set?]
      · simp [floatBoxAllocatedLocals, floatBoxSavedLocals,
          Wasm.Locals.set?, saved]
      · simp [floatBoxSavedLocals, floatBoxResultLocals,
          Wasm.Locals.set?, saved]
      · exact returned

theorem Installation.float32Box_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module)
    (bits : UInt32) (tail : List Wasm.Value) :
    installation.float32BoxTarget.toLocals
        (([Wasm.Value.f32 bits] ++ tail).take
          installation.float32BoxTarget.numParams).reverse =
      float32BoxEntry bits := by
  obtain ⟨params, locals, _⟩ := installation.float32Box_signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    float32BoxEntry, Wasm.ValueType.zero]

theorem Installation.floatBox_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module)
    (bits : UInt64) (tail : List Wasm.Value) :
    installation.floatBoxTarget.toLocals
        (([Wasm.Value.f64 bits] ++ tail).take
          installation.floatBoxTarget.numParams).reverse =
      floatBoxEntry bits := by
  obtain ⟨params, locals, _⟩ := installation.floatBox_signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    floatBoxEntry, Wasm.ValueType.zero]

theorem Installation.float32Unbox_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value) :
    installation.float32UnboxTarget.toLocals
        (([Wasm.Value.i32 object] ++ tail).take
          installation.float32UnboxTarget.numParams).reverse =
      unboxEntry object := by
  obtain ⟨params, locals, _⟩ := installation.float32Unbox_signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    unboxEntry]

theorem Installation.floatUnbox_entry
    {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    (installation : Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value) :
    installation.floatUnboxTarget.toLocals
        (([Wasm.Value.i32 object] ++ tail).take
          installation.floatUnboxTarget.numParams).reverse =
      unboxEntry object := by
  obtain ⟨params, locals, _⟩ := installation.floatUnbox_signature
  simp [Wasm.Function.toLocals, Wasm.Function.numParams, params, locals,
    unboxEntry]

/-- Width-independent checked admission supplied by every successful concrete
heap scalar allocation.  It exposes exactly the lanes read by resident
unboxing, plus the higher-level boxed-object relation used by compiler
refinement. -/
structure HeapBoxAdmission (state : MemoryState) (address : Word32)
    (scalar : BoxedScalar) : Prop where
  valid : state.FrontierInvariant
  object : ∃ header,
    BoxedObjectRel state address scalar.kind scalar header ∧
      header.refCount.toNat = 1 ∧ header.persistent = false
  addressBase : heapBase ≤ address.value
  addressAligned : address.value % target.heapAlignment = 0
  kindRead : state.memory.readUInt32 (address.value + headerKindOffset) =
    .ok ObjectKind.boxed.code
  flagsRead : state.memory.readUInt32 (address.value + headerFlagsOffset) =
    .ok liveFlag
  allocationRead : state.memory.readUInt32
    (address.value + headerAllocationBytesOffset) = .ok 40
  aux0Read : state.memory.readUInt32 (address.value + headerAux0Offset) =
    .ok scalar.kind.code
  aux1Read : state.memory.readUInt32 (address.value + headerAux1Offset) =
    .ok (UInt32.ofNat scalar.kind.payloadBytes)
  aux2Read : state.memory.readUInt32 (address.value + headerAux2Offset) = .ok 0
  aux3Read : state.memory.readUInt32 (address.value + headerAux3Offset) = .ok 0
  payloadRead : state.memory.readUInt64 (address.value + headerBytes) =
    .ok scalar.payload
  payloadLow : state.memory.readUInt32 (address.value + headerBytes) =
    .ok scalar.payload.toUInt32
  payloadHigh : state.memory.readUInt32 (address.value + headerBytes + 4) =
    .ok (scalar.payload >>> (32 : UInt64)).toUInt32

/-- One generic allocation theorem supplies the complete checked header and
payload boundary for both Float32 and Float. -/
theorem allocateBoxedScalar_heapAdmission
    (before after : MemoryState) (scalar : BoxedScalar) (address : Word32)
    (valid : before.FrontierInvariant)
    (frontierBase : heapBase ≤ before.heapCursor)
    (allocated : allocateBoxedScalar before scalar = .ok (after, address)) :
    HeapBoxAdmission after address scalar := by
  obtain ⟨finalValid, header, object, refCount, persistent⟩ :=
    allocateBoxedScalar_objectRel before after scalar address valid allocated
  obtain ⟨middle, objectAllocation, payloadWrite, _⟩ :=
    allocateBoxedScalar_decompose before after scalar address allocated
  have middleValid := valid.allocateObject objectAllocation
  have middleExtent := MemoryState.allocateObject_extent objectAllocation
  have payloadInBounds :
      address.value + headerBytes + 7 < middle.memory.size := by
    have cursorInBounds := middleValid.cursorInBounds
    rw [middleExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  let canonicalHeader := Header.forAllocation .boxed 40 false
    scalar.kind.code (UInt32.ofNat scalar.kind.payloadBytes)
  have initialExact : Header.ExactWords middle.memory address canonicalHeader := by
    simpa [canonicalHeader, target, headerBytes, align8] using
      (Header.ExactWords.ofAllocateObject objectAllocation)
  have finalExact : Header.ExactWords after.memory address canonicalHeader := by
    refine ⟨?_⟩
    intro index word wordAt
    have indexLt := (List.getElem?_eq_some_iff.mp wordAt).1
    have withinHeader : 4 * index + 4 ≤ headerBytes := by
      simp [Header.words] at indexLt
      simp [headerBytes]
      omega
    calc
      after.memory.readUInt32 (address.value + 4 * index) =
          middle.memory.readUInt32 (address.value + 4 * index) :=
        LinearMemory.readUInt32_of_writeUInt64_eq_ok_other middle.memory
          after.memory (address.value + headerBytes)
          (address.value + 4 * index) scalar.payload payloadInBounds
          payloadWrite (by right; omega)
      _ = .ok word := initialExact.wordAt index word wordAt
  have payloadRead := LinearMemory.readUInt64_of_writeUInt64_eq_ok
    middle.memory after.memory (address.value + headerBytes) scalar.payload
      payloadInBounds payloadWrite
  have payloadWords := allocateBoxedScalar_payloadWords before after scalar
    address valid allocated
  obtain ⟨rawState, rawAllocation, _, _, _⟩ :=
    MemoryState.allocateObject_header before middle .boxed
      target.semanticSlotBytes false scalar.kind.code
      (UInt32.ofNat scalar.kind.payloadBytes) 0 0 address objectAllocation
  have allocationPost := MemoryState.allocate_spec before rawState 40 address
    (by simpa [target, headerBytes, align8] using rawAllocation)
  refine {
    valid := finalValid
    object := ⟨header, object, refCount, persistent⟩
    addressBase := by
      rw [allocationPost.addressValue]
      exact Nat.le_trans frontierBase (align8_ge before.heapCursor)
    addressAligned := by
      rw [allocationPost.addressValue]
      change align8 before.heapCursor % 8 = 0
      exact align8_mod before.heapCursor
    kindRead := by
      simpa [canonicalHeader, Header.forAllocation] using finalExact.readKind
    flagsRead := by
      simpa [canonicalHeader, Header.forAllocation, Header.flags, liveFlag] using
        finalExact.readFlags
    allocationRead := by
      simpa [canonicalHeader, Header.forAllocation] using
        finalExact.readAllocationBytes
    aux0Read := by
      simpa [canonicalHeader, Header.forAllocation] using finalExact.readAux0
    aux1Read := by
      simpa [canonicalHeader, Header.forAllocation] using finalExact.readAux1
    aux2Read := by
      simpa [canonicalHeader, Header.forAllocation] using finalExact.readAux2
    aux3Read := by
      simpa [canonicalHeader, Header.forAllocation] using finalExact.readAux3
    payloadRead
    payloadLow := payloadWords.1
    payloadHigh := payloadWords.2 }

abbrev Float32BoxAdmission (state : MemoryState) (address : Word32)
    (bits : UInt32) : Prop :=
  HeapBoxAdmission state address (.float32 bits)

abbrev FloatBoxAdmission (state : MemoryState) (address : Word32)
    (bits : UInt64) : Prop :=
  HeapBoxAdmission state address (.float bits)

theorem allocateBoxedFloat32_admission
    (before after : MemoryState) (bits : UInt32) (address : Word32)
    (valid : before.FrontierInvariant)
    (frontierBase : heapBase ≤ before.heapCursor)
    (allocated : allocateBoxedScalar before (.float32 bits) =
      .ok (after, address)) :
    Float32BoxAdmission after address bits :=
  allocateBoxedScalar_heapAdmission before after (.float32 bits) address valid
    frontierBase allocated

theorem allocateBoxedFloat_admission
    (before after : MemoryState) (bits : UInt64) (address : Word32)
    (valid : before.FrontierInvariant)
    (frontierBase : heapBase ≤ before.heapCursor)
    (allocated : allocateBoxedScalar before (.float bits) =
      .ok (after, address)) :
    FloatBoxAdmission after address bits :=
  allocateBoxedScalar_heapAdmission before after (.float bits) address valid
    frontierBase allocated

theorem Float32BoxAdmission.lowBits
    {state : MemoryState} {address : Word32} {bits : UInt32}
    (admitted : Float32BoxAdmission state address bits) :
    state.memory.readUInt32 (address.value + headerBytes) = .ok bits := by
  simpa [BoxedScalar.payload] using admitted.payloadLow

theorem Float32BoxAdmission.highPadding
    {state : MemoryState} {address : Word32} {bits : UInt32}
    (admitted : Float32BoxAdmission state address bits) :
    state.memory.readUInt32 (address.value + headerBytes + 4) = .ok 0 := by
  have highZero : (bits.toUInt64 >>> (32 : UInt64)).toUInt32 = 0 := by
    bv_decide
  simpa [BoxedScalar.payload, highZero] using admitted.payloadHigh

theorem FloatBoxAdmission.bits
    {state : MemoryState} {address : Word32} {bits : UInt64}
    (admitted : FloatBoxAdmission state address bits) :
    state.memory.readUInt64 (address.value + headerBytes) = .ok bits := by
  simpa [BoxedScalar.payload] using admitted.payloadRead

/-- Physical view of one admitted heap scalar box.  This is the common
transport boundary between W6's checked byte-array memory and the Talos
linear memory read by the production floating unbox helpers. -/
structure PhysicalHeapBoxAdmission {host : Type} (store : Wasm.Store host)
    (object marker payloadBytes : UInt32) (payload : UInt64) : Prop where
  notBelowHeap : ¬object < u32 heapBase
  aligned : u32 (target.heapAlignment - 1) &&& object = 0
  wordInBounds : ∀ offset,
    offset ∈ [headerKindOffset, headerFlagsOffset,
      headerAllocationBytesOffset, headerAux0Offset, headerAux1Offset,
      headerAux2Offset, headerAux3Offset] →
    ¬(object.toNat + (u32 offset).toNat + 4 >
      store.mem.pages * wasmPageBytes)
  kindRead : store.mem.read32 (object + u32 headerKindOffset) =
    ObjectKind.boxed.code
  flagsRead : store.mem.read32 (object + u32 headerFlagsOffset) = liveFlag
  allocationRead : store.mem.read32
    (object + u32 headerAllocationBytesOffset) = 40
  aux0Read : store.mem.read32 (object + u32 headerAux0Offset) = marker
  aux1Read : store.mem.read32 (object + u32 headerAux1Offset) = payloadBytes
  aux2Read : store.mem.read32 (object + u32 headerAux2Offset) = 0
  aux3Read : store.mem.read32 (object + u32 headerAux3Offset) = 0
  payload32InBounds :
    ¬(object.toNat + (u32 headerBytes).toNat + 4 >
      store.mem.pages * wasmPageBytes)
  payload32Read : store.mem.read32 (object + u32 headerBytes) = payload.toUInt32
  payloadHighInBounds :
    ¬(object.toNat + (u32 (headerBytes + 4)).toNat + 4 >
      store.mem.pages * wasmPageBytes)
  payloadHighRead : store.mem.read32 (object + u32 (headerBytes + 4)) =
    (payload >>> (32 : UInt64)).toUInt32
  payload64InBounds :
    ¬(object.toNat + (u32 headerBytes).toNat + 8 >
      store.mem.pages * wasmPageBytes)
  payload64Read : store.mem.read64 (object + u32 headerBytes) = payload

/-- Every semantic heap-box admission exposes the exact physical loads used
by resident unboxing.  All address conversion, extent, and endian reasoning
is discharged once here. -/
theorem HeapBoxAdmission.physical
    {host : Type} {state : MemoryState} {store : Wasm.Store host}
    {address : Word32} {scalar : BoxedScalar}
    (admitted : HeapBoxAdmission state address scalar)
    (related : ResidentMemoryRel state store.mem) :
    PhysicalHeapBoxAdmission store (UInt32.ofNat address.value)
      scalar.kind.code (UInt32.ofNat scalar.kind.payloadBytes)
      scalar.payload := by
  let object := UInt32.ofNat address.value
  have addressFits : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have objectToNat : object.toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' addressFits
  have offsetToNat (offset : Nat) (small : offset < UInt32.size) :
      (u32 offset).toNat = offset :=
    UInt32.toNat_ofNat_of_lt' small
  obtain ⟨header, objectRelated, _, _⟩ := admitted.object
  have allocationBytes : header.allocationBytes.toNat = 40 := by
    simpa [target, headerBytes, align8] using objectRelated.allocationBytes
  have extentInBounds : address.value + 40 ≤ state.memory.size := by
    rw [← allocationBytes]
    exact Nat.le_trans objectRelated.extent admitted.valid.cursorInBounds
  have laneInBounds (offset : Nat) (within : offset + 4 ≤ 40) :
      address.value + offset + 3 < state.memory.size := by omega
  have physicalBound (offset : Nat) (within : offset + 4 ≤ 40) :
      ¬(object.toNat + (u32 offset).toNat + 4 >
        store.mem.pages * wasmPageBytes) := by
    have offsetSmall : offset < UInt32.size := by
      unfold UInt32.size
      omega
    rw [objectToNat, offsetToNat offset offsetSmall, ← related.size_eq]
    omega
  have physicalRead32 (offset : Nat) (value : UInt32)
      (within : offset + 4 ≤ 40)
      (read : state.memory.readUInt32 (address.value + offset) = .ok value) :
      store.mem.read32 (object + u32 offset) = value := by
    have bridge := related.readUInt32_eq_read32 (laneInBounds offset within)
    rw [read] at bridge
    have exactRead := Except.ok.inj bridge
    have physicalAddressEq : object + u32 offset =
        UInt32.ofNat (address.value + offset) := by
      simp [object, u32, UInt32.ofNat_add]
    rw [physicalAddressEq]
    exact exactRead.symm
  have notBelowHeap : ¬object < u32 heapBase := by
    intro below
    have belowNat := UInt32.lt_iff_toNat_lt.mp below
    have baseFits : heapBase < UInt32.size := by decide
    rw [objectToNat, offsetToNat heapBase baseFits] at belowNat
    exact (Nat.not_lt_of_ge admitted.addressBase) belowNat
  have aligned : u32 (target.heapAlignment - 1) &&& object = 0 := by
    have objectAligned := ResidentAllocator.alignedWord_of_mod8 addressFits (by
      simpa [target] using admitted.addressAligned)
    simpa [object, u32, target, UInt32.and_comm] using objectAligned
  have wordInBounds : ∀ offset,
      offset ∈ [headerKindOffset, headerFlagsOffset,
        headerAllocationBytesOffset, headerAux0Offset, headerAux1Offset,
        headerAux2Offset, headerAux3Offset] →
      ¬(object.toNat + (u32 offset).toNat + 4 >
        store.mem.pages * wasmPageBytes) := by
    intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (apply physicalBound; decide)
  have payload64Read : store.mem.read64 (object + u32 headerBytes) =
      scalar.payload := by
    have bridge := related.readUInt64_eq_read64 (by
      have concrete : address.value + 32 + 7 < state.memory.size := by omega
      simpa [headerBytes] using concrete)
    have logicalPayloadRead : state.memory.readUInt64 (address.value + 32) =
        .ok scalar.payload := by
      simpa [headerBytes] using admitted.payloadRead
    rw [logicalPayloadRead] at bridge
    have exactRead := Except.ok.inj bridge
    have physicalAddressEq : object + u32 headerBytes =
        UInt32.ofNat (address.value + headerBytes) := by
      simp [object, u32, UInt32.ofNat_add]
    rw [physicalAddressEq]
    exact exactRead.symm
  refine {
    notBelowHeap
    aligned
    wordInBounds
    kindRead := physicalRead32 headerKindOffset ObjectKind.boxed.code
      (by decide) admitted.kindRead
    flagsRead := physicalRead32 headerFlagsOffset liveFlag
      (by decide) admitted.flagsRead
    allocationRead := physicalRead32 headerAllocationBytesOffset 40
      (by decide) admitted.allocationRead
    aux0Read := physicalRead32 headerAux0Offset scalar.kind.code
      (by decide) admitted.aux0Read
    aux1Read := physicalRead32 headerAux1Offset
      (UInt32.ofNat scalar.kind.payloadBytes) (by decide) admitted.aux1Read
    aux2Read := physicalRead32 headerAux2Offset 0
      (by decide) admitted.aux2Read
    aux3Read := physicalRead32 headerAux3Offset 0
      (by decide) admitted.aux3Read
    payload32InBounds := physicalBound headerBytes (by decide)
    payload32Read := physicalRead32 headerBytes scalar.payload.toUInt32
      (by decide) admitted.payloadLow
    payloadHighInBounds := physicalBound (headerBytes + 4) (by decide)
    payloadHighRead := physicalRead32 (headerBytes + 4)
      (scalar.payload >>> (32 : UInt64)).toUInt32 (by decide)
      admitted.payloadHigh
    payload64InBounds := by
      rw [objectToNat, offsetToNat headerBytes (by decide), ← related.size_eq]
      change ¬(address.value + 32 + 8 > state.memory.size)
      omega
    payload64Read }

/-- The production Float32 box body implements W6's heap-only bit-exact
allocation contract.  W6 writes the zero-extended payload as a doubleword;
the generated helper writes only the low word, and the fresh-zero theorem
proves those physical stores equal. -/
theorem wp_float32BoxProgram_of_allocateBoxedScalar
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {allocatorFunction : Wasm.Function}
    {allocatorIndex frontierIndex : Nat}
    {before after : MemoryState} {store : Wasm.Store host}
    {bits : UInt32} {address : Word32}
    (allocatorAdapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok allocatorFunction)
    (allocatorNotImport : module.imports[allocatorIndex]? = none)
    (allocatorFound :
      module.funcs[allocatorIndex - module.imports.length]? =
        some allocatorFunction)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (allocated : allocateBoxedScalar before (.float32 bits) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      Float32BoxAdmission after address bits ∧
      Wasm.wp module (float32BoxProgram allocatorIndex)
        (fun completion => completion = .Return finalStore
          [.i32 (UInt32.ofNat address.value)]) store
        (float32BoxEntry bits) env := by
  obtain ⟨objectState, objectAllocation, payloadWrite, afterCursor⟩ :=
    allocateBoxedScalar_decompose before after (.float32 bits) address
      allocated
  obtain ⟨rawState, rawAllocation, headerWrite, objectCursor, _⟩ :=
    MemoryState.allocateObject_header before objectState .boxed
      target.semanticSlotBytes false BoxedScalarKind.float32.code 4 0 0 address
        objectAllocation
  have rawAllocation40 : before.allocate 40 = .ok (rawState, address) := by
    simpa [target, headerBytes, align8] using rawAllocation
  have rawStrict : rawState.heapCursor < wordModulus := by
    rw [← objectCursor, ← afterCursor]
    exact strictEnd
  have rawWithinCap :
      (rawState.heapCursor - 1) / wasmPageBytes + 1 ≤
        store.memoryCap module 0 := by
    rw [← objectCursor, ← afterCursor]
    exact withinCap
  obtain ⟨allocatedStore, rawRelated, allocatorRun⟩ :=
    ResidentAllocator.terminatesWith_allocateFunction_of_allocate
      (env := env) allocatorAdapted allocatorNotImport allocatorFound memory32
      valid related
      (requestedAligned := (by decide : 40 % target.heapAlignment = 0))
      rawAllocation40 rawStrict rawWithinCap
  have rawPost := MemoryState.allocate_spec before rawState 40 address
    rawAllocation40
  have headerInBounds : address.value + headerBytes ≤ rawState.memory.size := by
    have endInBounds := rawPost.endInBounds
    simp [headerBytes] at endInBounds ⊢
    omega
  let physicalAddress := UInt32.ofNat address.value
  have addressFits : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have physicalToNat : physicalAddress.toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' addressFits
  have nonwrap : physicalAddress.toNat + 40 ≤ UInt32.size := by
    rw [physicalToNat]
    simpa [wordModulus, UInt32.size] using rawPost.endWithinAddressSpace
  have freshWordZero (offset : Nat)
      (member : offset ∈ allocationWordOffsets) :
      allocatedStore.mem.read32 (physicalAddress + u32 offset) = 0 := by
    have within : offset + 4 ≤ align8 40 := by
      simp [allocationWordOffsets] at member
      simp [align8]
      omega
    exact rawAllocation_physicalRead32_zero valid rawAllocation40
      rawRelated.toResidentMemoryRel within
  have zeroed : zeroAllocationStore allocatedStore physicalAddress =
      allocatedStore :=
    zeroAllocationStore_eq_of_words_zero allocatedStore physicalAddress
      freshWordZero
  have headerStoreEq :
      boxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float32.code 4 =
        canonicalBoxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float32.code 4 := by
    exact boxHeaderStore_eq_canonical allocatedStore physicalAddress
      BoxedScalarKind.float32.code 4 nonwrap zeroed
      (freshWordZero headerAux2Offset (by decide))
      (freshWordZero headerAux3Offset (by decide))
  let headerStore := boxHeaderStore allocatedStore physicalAddress
    BoxedScalarKind.float32.code 4
  have headerHighZero : headerStore.mem.read32
      (physicalAddress + u32 (headerBytes + 4)) = 0 := by
    dsimp only [headerStore]
    rw [headerStoreEq]
    rw [canonicalBoxHeaderStore_read32_later allocatedStore physicalAddress
      BoxedScalarKind.float32.code 4 (headerBytes + 4) nonwrap
      (by decide) (by decide)]
    exact freshWordZero (headerBytes + 4) (by decide)
  let payloadAddress := physicalAddress + u32 headerBytes
  have payloadAddressToNat :
      payloadAddress.toNat = physicalAddress.toNat + headerBytes := by
    have fits : physicalAddress.toNat + headerBytes < UInt32.size := by
      simp [headerBytes] at nonwrap ⊢
      omega
    rw [show payloadAddress =
      UInt32.ofNat (physicalAddress.toNat + headerBytes) by
        simp [payloadAddress, u32, UInt32.ofNat_add]]
    exact UInt32.toNat_ofNat_of_lt' fits
  have payloadNonwrap : payloadAddress.toNat + 8 ≤ UInt32.size := by
    rw [payloadAddressToNat]
    simp [headerBytes] at nonwrap ⊢
    omega
  have payloadHighAddress :
      payloadAddress + u32 4 =
        physicalAddress + u32 (headerBytes + 4) := by
    simp [payloadAddress, u32, UInt32.ofNat_add]
    ac_rfl
  have payloadHighZero : headerStore.mem.read32
      (payloadAddress + u32 4) = 0 := by
    rw [payloadHighAddress]
    exact headerHighZero
  have payloadMemoryEq :
      headerStore.mem.write64 payloadAddress bits.toUInt64 =
        headerStore.mem.write32 payloadAddress bits :=
    write64_toUInt64_eq_write32_of_high_zero headerStore.mem payloadAddress
      bits payloadNonwrap payloadHighZero
  have headerStateEq :
      ({ rawState with memory := objectState.memory } : MemoryState) =
        objectState := by
    cases rawState
    cases objectState
    simp_all only
  have canonicalWrite :
      (canonicalBoxHeader BoxedScalarKind.float32.code 4).write
          rawState.memory address = .ok objectState.memory := by
    simpa [canonicalBoxHeader, target, headerBytes, align8] using headerWrite
  have canonicalRelated :
      ResidentAllocatorRel objectState
        (canonicalBoxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float32.code 4) frontierIndex := by
    have refined := canonicalBoxHeaderStore_refines rawRelated headerInBounds
      canonicalWrite
    rw [headerStateEq] at refined
    simpa only [physicalAddress] using refined
  have headerRelated : ResidentAllocatorRel objectState headerStore
      frontierIndex := by
    dsimp only [headerStore]
    rw [headerStoreEq]
    exact canonicalRelated
  have payloadInBounds :
      address.value + headerBytes + 7 < objectState.memory.size := by
    have objectValid := valid.allocateObject objectAllocation
    have objectExtent := MemoryState.allocateObject_extent objectAllocation
    have cursorInBounds := objectValid.cursorInBounds
    rw [objectExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  let finalStore := float32BoxStore allocatedStore physicalAddress bits
  have payloadRelatedRaw := headerRelated.writeUInt64 payloadInBounds
    payloadWrite
  have payloadPhysicalAddress :
      UInt32.ofNat (address.value + headerBytes) = payloadAddress := by
    simp [payloadAddress, physicalAddress, u32, UInt32.ofNat_add]
  have payloadStoreEq :
      ({ headerStore with mem := (headerStore.mem.write64
        (UInt32.ofNat (address.value + headerBytes)) bits.toUInt64) } :
          Wasm.Store host) = finalStore := by
    rw [payloadPhysicalAddress]
    unfold finalStore float32BoxStore
    change { headerStore with mem :=
        headerStore.mem.write64 payloadAddress bits.toUInt64 } =
      ResidentMemoryRel.write32Store headerStore payloadAddress bits
    unfold ResidentMemoryRel.write32Store
    rw [payloadMemoryEq]
  simp only [BoxedScalar.payload] at payloadRelatedRaw
  rw [payloadStoreEq] at payloadRelatedRaw
  have finalStateEq :
      ({ objectState with memory := after.memory } : MemoryState) = after := by
    cases objectState
    cases after
    simp_all only
  have finalRelated :
      ResidentAllocatorRel after finalStore frontierIndex := by
    rw [← finalStateEq]
    exact payloadRelatedRaw
  have physicalInBounds : physicalAddress.toNat + 40 ≤
      allocatedStore.mem.pages * wasmPageBytes := by
    rw [physicalToNat, ← rawRelated.toResidentMemoryRel.size_eq]
    exact rawPost.endInBounds
  have coreWP : Wasm.wp module (float32BoxProgram allocatorIndex)
      (fun completion => completion = .Return finalStore
        [.i32 physicalAddress]) store (float32BoxEntry bits) env := by
    apply wp_float32BoxProgram allocatorRun physicalInBounds
    rfl
  refine ⟨finalStore, finalRelated, ?_, ?_⟩
  · exact allocateBoxedFloat32_admission before after bits address valid
      related.frontierBase allocated
  · simpa [physicalAddress] using coreWP

/-- The production Float box body implements W6's heap-only 64-bit floating
allocation contract.  The theorem returns the post-allocation runtime
relation, the canonical semantic admission, and exact instruction execution
in one boundary. -/
theorem wp_floatBoxProgram_of_allocateBoxedScalar
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {allocatorFunction : Wasm.Function}
    {allocatorIndex frontierIndex : Nat}
    {before after : MemoryState} {store : Wasm.Store host}
    {bits : UInt64} {address : Word32}
    (allocatorAdapted : FirTalos.function sourceModule
      (Fir.Wasm.Emit.ResidentAllocator.allocateFunction frontierIndex) =
        .ok allocatorFunction)
    (allocatorNotImport : module.imports[allocatorIndex]? = none)
    (allocatorFound :
      module.funcs[allocatorIndex - module.imports.length]? =
        some allocatorFunction)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store frontierIndex)
    (allocated : allocateBoxedScalar before (.float bits) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore frontierIndex ∧
      FloatBoxAdmission after address bits ∧
      Wasm.wp module (floatBoxProgram allocatorIndex)
        (fun completion => completion = .Return finalStore
          [.i32 (UInt32.ofNat address.value)]) store
        (floatBoxEntry bits) env := by
  obtain ⟨objectState, objectAllocation, payloadWrite, afterCursor⟩ :=
    allocateBoxedScalar_decompose before after (.float bits) address allocated
  obtain ⟨rawState, rawAllocation, headerWrite, objectCursor, _⟩ :=
    MemoryState.allocateObject_header before objectState .boxed
      target.semanticSlotBytes false BoxedScalarKind.float.code 8 0 0 address
        objectAllocation
  have rawAllocation40 : before.allocate 40 = .ok (rawState, address) := by
    simpa [target, headerBytes, align8] using rawAllocation
  have rawStrict : rawState.heapCursor < wordModulus := by
    rw [← objectCursor, ← afterCursor]
    exact strictEnd
  have rawWithinCap :
      (rawState.heapCursor - 1) / wasmPageBytes + 1 ≤
        store.memoryCap module 0 := by
    rw [← objectCursor, ← afterCursor]
    exact withinCap
  obtain ⟨allocatedStore, rawRelated, allocatorRun⟩ :=
    ResidentAllocator.terminatesWith_allocateFunction_of_allocate
      (env := env) allocatorAdapted allocatorNotImport allocatorFound memory32
      valid related
      (requestedAligned := (by decide : 40 % target.heapAlignment = 0))
      rawAllocation40 rawStrict rawWithinCap
  have rawPost := MemoryState.allocate_spec before rawState 40 address
    rawAllocation40
  have headerInBounds : address.value + headerBytes ≤ rawState.memory.size := by
    have endInBounds := rawPost.endInBounds
    simp [headerBytes] at endInBounds ⊢
    omega
  let physicalAddress := UInt32.ofNat address.value
  have addressFits : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have physicalToNat : physicalAddress.toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' addressFits
  have nonwrap : physicalAddress.toNat + 40 ≤ UInt32.size := by
    rw [physicalToNat]
    simpa [wordModulus, UInt32.size] using rawPost.endWithinAddressSpace
  have freshWordZero (offset : Nat)
      (member : offset ∈ allocationWordOffsets) :
      allocatedStore.mem.read32 (physicalAddress + u32 offset) = 0 := by
    have within : offset + 4 ≤ align8 40 := by
      simp [allocationWordOffsets] at member
      simp [align8]
      omega
    exact rawAllocation_physicalRead32_zero valid rawAllocation40
      rawRelated.toResidentMemoryRel within
  have zeroed : zeroAllocationStore allocatedStore physicalAddress =
      allocatedStore :=
    zeroAllocationStore_eq_of_words_zero allocatedStore physicalAddress
      freshWordZero
  have headerStoreEq :
      boxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float.code 8 =
        canonicalBoxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float.code 8 := by
    exact boxHeaderStore_eq_canonical allocatedStore physicalAddress
      BoxedScalarKind.float.code 8 nonwrap zeroed
      (freshWordZero headerAux2Offset (by decide))
      (freshWordZero headerAux3Offset (by decide))
  have headerStateEq :
      ({ rawState with memory := objectState.memory } : MemoryState) =
        objectState := by
    cases rawState
    cases objectState
    simp_all only
  have canonicalWrite :
      (canonicalBoxHeader BoxedScalarKind.float.code 8).write
          rawState.memory address = .ok objectState.memory := by
    simpa [canonicalBoxHeader, target, headerBytes, align8] using headerWrite
  have canonicalRelated :
      ResidentAllocatorRel objectState
        (canonicalBoxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float.code 8) frontierIndex := by
    have refined := canonicalBoxHeaderStore_refines rawRelated headerInBounds
      canonicalWrite
    rw [headerStateEq] at refined
    simpa only [physicalAddress] using refined
  have headerRelated :
      ResidentAllocatorRel objectState
        (boxHeaderStore allocatedStore physicalAddress
          BoxedScalarKind.float.code 8) frontierIndex := by
    rw [headerStoreEq]
    exact canonicalRelated
  have payloadInBounds :
      address.value + headerBytes + 7 < objectState.memory.size := by
    have objectValid := valid.allocateObject objectAllocation
    have objectExtent := MemoryState.allocateObject_extent objectAllocation
    have cursorInBounds := objectValid.cursorInBounds
    rw [objectExtent] at cursorInBounds
    simp [target, headerBytes, align8] at cursorInBounds ⊢
    omega
  let finalStore := floatBoxStore allocatedStore physicalAddress bits
  have payloadRelatedRaw := headerRelated.writeUInt64 payloadInBounds
    payloadWrite
  have finalStateEq :
      ({ objectState with memory := after.memory } : MemoryState) = after := by
    cases objectState
    cases after
    simp_all only
  have finalRelated :
      ResidentAllocatorRel after finalStore frontierIndex := by
    rw [← finalStateEq]
    simpa [finalStore, floatBoxStore, ResidentMemoryRel.write64Store,
      physicalAddress, u32,
      UInt32.ofNat_add, BoxedScalar.payload] using payloadRelatedRaw
  have physicalInBounds : physicalAddress.toNat + 40 ≤
      allocatedStore.mem.pages * wasmPageBytes := by
    rw [physicalToNat, ← rawRelated.toResidentMemoryRel.size_eq]
    exact rawPost.endInBounds
  have coreWP : Wasm.wp module (floatBoxProgram allocatorIndex)
      (fun completion => completion = .Return finalStore
        [.i32 physicalAddress]) store (floatBoxEntry bits) env := by
    apply wp_floatBoxProgram allocatorRun physicalInBounds
    rfl
  refine ⟨finalStore, finalRelated, ?_, ?_⟩
  · exact allocateBoxedFloat_admission before after bits address valid
      related.frontierBase allocated
  · simpa [physicalAddress] using coreWP

/-- The shared floating unbox validator is transparent to a caller once all
physical admission reads agree.  The optional final premise is exactly the
Float32 zero-padding invariant; Float's 64-bit path does not need it. -/
theorem wp_unboxPrefixProgram_of_admission
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object marker payloadBytes : UInt32} {payload : UInt64}
    {checkHighPadding : Bool} {rest : Wasm.Program}
    (physical : PhysicalHeapBoxAdmission store object marker payloadBytes payload)
    (paddingZero : checkHighPadding = true →
      (payload >>> (32 : UInt64)).toUInt32 = 0)
    (continued : Wasm.wp module rest Q store (unboxEntry object) env) :
    Wasm.wp module
      (unboxPrefixProgram marker payloadBytes checkHighPadding ++ rest)
      Q store (unboxEntry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxEntry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  have kindBound := physical.wordInBounds headerKindOffset (by simp)
  have flagsBound := physical.wordInBounds headerFlagsOffset (by simp)
  have allocationBound := physical.wordInBounds
    headerAllocationBytesOffset (by simp)
  have aux0Bound := physical.wordInBounds headerAux0Offset (by simp)
  have aux1Bound := physical.wordInBounds headerAux1Offset (by simp)
  have aux2Bound := physical.wordInBounds headerAux2Offset (by simp)
  have aux3Bound := physical.wordInBounds headerAux3Offset (by simp)
  unfold unboxPrefixProgram requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons,
    if_neg physical.notBelowHeap]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_const_cons, Wasm.wp_and_cons,
    physical.aligned, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using flagsBound), physical.flagsRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_and_cons]
  rw [show liveFlag &&& liveFlag = liveFlag by decide]
  simp only [Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using kindBound), physical.kindRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux0Bound), physical.aux0Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using allocationBound),
    physical.allocationRead]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux1Bound), physical.aux1Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux2Bound), physical.aux2Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
  rw [if_neg (by simpa [wasmPageBytes] using aux3Bound), physical.aux3Read]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  by_cases check : checkHighPadding = true
  · simp only [check, if_true, List.cons_append, List.nil_append,
      Wasm.wp_nil, List.take_zero, List.drop_zero,
      Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
    rw [if_neg (by simpa [wasmPageBytes] using physical.payloadHighInBounds),
      physical.payloadHighRead, paddingZero check]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
    simpa only [Wasm.wp_nil, List.take_zero, List.drop_zero,
      List.nil_append] using continued
  · have checkFalse : checkHighPadding = false := Bool.eq_false_of_not_eq_true check
    simpa [checkFalse, unboxEntry] using continued

/-- Canonical Float32 admission makes the production physical unbox program
return the exact IEEE-754 bit pattern, including every NaN payload. -/
theorem wp_float32UnboxProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {state : MemoryState} {store : Wasm.Store host}
    {address : Word32} {bits : UInt32}
    (admitted : Float32BoxAdmission state address bits)
    (related : ResidentMemoryRel state store.mem)
    (returned : Q (.Return store [.f32 bits])) :
    Wasm.wp module float32UnboxProgram Q store
      (unboxEntry (UInt32.ofNat address.value)) env := by
  have physical := admitted.physical related
  have payloadHigh : ((.float32 bits : BoxedScalar).payload >>>
      (32 : UInt64)).toUInt32 = 0 := by
    change (bits.toUInt64 >>> (32 : UInt64)).toUInt32 = 0
    bv_decide
  have payloadLow : (.float32 bits : BoxedScalar).payload.toUInt32 = bits := by
    change bits.toUInt64.toUInt32 = bits
    bv_decide
  unfold float32UnboxProgram
  apply wp_unboxPrefixProgram_of_admission physical
  · intro _
    exact payloadHigh
  · have objectFound (values : List Wasm.Value) :
        ({ unboxEntry (UInt32.ofNat address.value) with values } :
          Wasm.Locals).get 0 = some (.i32 (UInt32.ofNat address.value)) := by
      rfl
    simp only [Wasm.wp_localGet_cons, objectFound, Wasm.wp_load32_cons]
    rw [if_neg (by simpa [wasmPageBytes] using physical.payload32InBounds),
      physical.payload32Read, payloadLow]
    simpa only [Wasm.wp_f32ReinterpretI32_cons, Wasm.wp_ret_cons,
      unboxEntry] using returned

/-- Canonical Float admission makes the production physical unbox program
return the exact 64-bit IEEE-754 payload and leave the resident store intact. -/
theorem wp_floatUnboxProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {state : MemoryState} {store : Wasm.Store host}
    {address : Word32} {bits : UInt64}
    (admitted : FloatBoxAdmission state address bits)
    (related : ResidentMemoryRel state store.mem)
    (returned : Q (.Return store [.f64 bits])) :
    Wasm.wp module floatUnboxProgram Q store
      (unboxEntry (UInt32.ofNat address.value)) env := by
  have physical := admitted.physical related
  unfold floatUnboxProgram
  apply wp_unboxPrefixProgram_of_admission physical
  · simp
  · have objectFound (values : List Wasm.Value) :
        ({ unboxEntry (UInt32.ofNat address.value) with values } :
          Wasm.Locals).get 0 = some (.i32 (UInt32.ofNat address.value)) := by
      rfl
    simp only [Wasm.wp_localGet_cons, objectFound, Wasm.wp_load64_cons]
    rw [if_neg (by simpa [wasmPageBytes] using physical.payload64InBounds),
      physical.payload64Read]
    simpa only [BoxedScalar.payload, Wasm.wp_f64ReinterpretI64_cons,
      Wasm.wp_ret_cons, unboxEntry] using returned

/-- Any word below the resident heap base traps before the first memory load,
independently of floating width and of the caller continuation. -/
theorem wp_unboxPrefixProgram_belowHeap
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object marker payloadBytes : UInt32} {checkHighPadding : Bool}
    {rest : Wasm.Program}
    (below : object < u32 heapBase)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module
      (unboxPrefixProgram marker payloadBytes checkHighPadding ++ rest)
      Q store (unboxEntry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxEntry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  unfold unboxPrefixProgram requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_pos below]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_unreachable_cons] using trapped

/-- A heap-range word that violates object alignment traps before any memory
load, uniformly for Float32 and Float. -/
theorem wp_unboxPrefixProgram_misaligned
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object marker payloadBytes : UInt32} {checkHighPadding : Bool}
    {rest : Wasm.Program}
    (notBelow : ¬object < u32 heapBase)
    (misaligned : u32 (target.heapAlignment - 1) &&& object ≠ 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module
      (unboxPrefixProgram marker payloadBytes checkHighPadding ++ rest)
      Q store (unboxEntry object) env := by
  have objectFound (values : List Wasm.Value) :
      ({ unboxEntry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  unfold unboxPrefixProgram requireHeapAddressProgram
    requireHeaderWordProgram trapUnlessProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    objectFound, Wasm.wp_const_cons, Wasm.wp_ltU_cons, if_neg notBelow]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, objectFound, Wasm.wp_const_cons, Wasm.wp_and_cons,
    Wasm.wp_eq_cons, if_neg misaligned]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_unreachable_cons] using trapped

/-- Every low-bit tagged immediate is rejected before a floating unbox can
read memory.  Small tags fail the heap-base guard; larger tags fail alignment. -/
theorem wp_unboxPrefixProgram_tagged
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object marker payloadBytes : UInt32} {checkHighPadding : Bool}
    {rest : Wasm.Program}
    (tagged : (1 : UInt32) &&& object ≠ 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module
      (unboxPrefixProgram marker payloadBytes checkHighPadding ++ rest)
      Q store (unboxEntry object) env := by
  by_cases below : object < u32 heapBase
  · exact wp_unboxPrefixProgram_belowHeap below trapped
  · apply wp_unboxPrefixProgram_misaligned below
    · intro aligned
      apply tagged
      have lowMask : (1 : UInt32) &&& 7 = 1 := by decide
      calc
        (1 : UInt32) &&& object = ((1 : UInt32) &&& 7) &&& object := by
          rw [lowMask]
        _ = (1 : UInt32) &&& (7 &&& object) := UInt32.and_assoc _ _ _
        _ = 0 := by
          have aligned' : (7 : UInt32) &&& object = 0 := by
            simpa [u32, target] using aligned
          rw [aligned']
          simp
    · exact trapped

/-- A Float32-shaped physical object with nonzero high payload padding is
rejected after the common header checks and before the payload is returned. -/
theorem wp_float32UnboxProgram_nonzeroPadding
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object : UInt32} {payload : UInt64}
    (physical : PhysicalHeapBoxAdmission store object
      BoxedScalarKind.float32.code 4 payload)
    (nonzero : (payload >>> (32 : UInt64)).toUInt32 ≠ 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module float32UnboxProgram Q store (unboxEntry object) env := by
  let paddingProgram := requireHeaderWordProgram (headerBytes + 4) 0
  let payloadProgram : Wasm.Program :=
    [.localGet 0, .load32 (u32 headerBytes), .f32ReinterpretI32, .ret]
  have objectFound (values : List Wasm.Value) :
      ({ unboxEntry object with values } : Wasm.Locals).get 0 =
        some (.i32 object) := by rfl
  have paddingWP : Wasm.wp module (paddingProgram ++ payloadProgram) Q store
      (unboxEntry object) env := by
    unfold paddingProgram requireHeaderWordProgram trapUnlessProgram
    simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
      objectFound, Wasm.wp_load32_cons]
    rw [if_neg (by simpa [wasmPageBytes] using physical.payloadHighInBounds),
      physical.payloadHighRead]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_neg nonzero]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simpa only [Wasm.wp_unreachable_cons] using trapped
  have commonWP := wp_unboxPrefixProgram_of_admission
    (checkHighPadding := false) physical (by simp) paddingWP
  simpa [float32UnboxProgram, unboxPrefixProgram, paddingProgram,
    payloadProgram, List.append_assoc] using commonWP

/-- Lift the exact Float32 box core through the adapter's terminal suffix. -/
theorem Installation.wp_float32Box_body
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {Q : Wasm.Assertion host}
    (installation : Installation sourceModule module)
    (noFallthrough : ∀ final finalLocals, ¬Q (.Fallthrough final finalLocals))
    (coreWP : Wasm.wp module
      (float32BoxProgram installation.allocatorIndex) Q store locals env) :
    Wasm.wp module installation.float32BoxTarget.body Q store locals env := by
  rw [installation.float32Box_body]
  exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough coreWP

/-- Lift the exact Float box core through the adapter's terminal suffix. -/
theorem Installation.wp_floatBox_body
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {Q : Wasm.Assertion host}
    (installation : Installation sourceModule module)
    (noFallthrough : ∀ final finalLocals, ¬Q (.Fallthrough final finalLocals))
    (coreWP : Wasm.wp module
      (floatBoxProgram installation.allocatorIndex) Q store locals env) :
    Wasm.wp module installation.floatBoxTarget.body Q store locals env := by
  rw [installation.floatBox_body]
  exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough coreWP

/-- The installed Float32 box export realizes the complete W6 allocation
contract while preserving arbitrary caller operand slack. -/
theorem Installation.terminatesWith_float32Box_of_allocateBoxedScalar
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {before after : MemoryState}
    {store : Wasm.Store host} {bits : UInt32} {address : Word32}
    (installation : Installation sourceModule module)
    (tail : List Wasm.Value)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store installation.frontierIndex)
    (allocated : allocateBoxedScalar before (.float32 bits) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore installation.frontierIndex ∧
      Float32BoxAdmission after address bits ∧
      Wasm.TerminatesWith env module installation.float32BoxIndex store
        ([.f32 bits] ++ tail)
        (fun final values => final = finalStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail) := by
  obtain ⟨finalStore, finalRelated, admitted, coreWP⟩ :=
    wp_float32BoxProgram_of_allocateBoxedScalar
      installation.allocatorAdapted installation.allocatorNotImport
      installation.allocatorInstalled memory32 valid related allocated
      strictEnd withinCap
  have bodyWP : Wasm.wp module installation.float32BoxTarget.body
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (float32BoxEntry bits) env := by
    apply installation.wp_float32Box_body (by intros; simp)
    exact coreWP
  refine ⟨finalStore, finalRelated, admitted, ?_⟩
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.float32BoxNotImport installation.float32BoxInstalled
  rw [installation.float32Box_entry bits tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.float32Box_signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- The installed Float box export realizes the complete W6 allocation
contract while preserving every 64-bit payload pattern and caller tail. -/
theorem Installation.terminatesWith_floatBox_of_allocateBoxedScalar
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {before after : MemoryState}
    {store : Wasm.Store host} {bits : UInt64} {address : Word32}
    (installation : Installation sourceModule module)
    (tail : List Wasm.Value)
    (memory32 : module.memIs64 = false)
    (valid : before.FrontierInvariant)
    (related : ResidentAllocatorRel before store installation.frontierIndex)
    (allocated : allocateBoxedScalar before (.float bits) =
      .ok (after, address))
    (strictEnd : after.heapCursor < wordModulus)
    (withinCap : (after.heapCursor - 1) / wasmPageBytes + 1 ≤
      store.memoryCap module 0) :
    ∃ finalStore,
      ResidentAllocatorRel after finalStore installation.frontierIndex ∧
      FloatBoxAdmission after address bits ∧
      Wasm.TerminatesWith env module installation.floatBoxIndex store
        ([.f64 bits] ++ tail)
        (fun final values => final = finalStore ∧
          values = .i32 (UInt32.ofNat address.value) :: tail) := by
  obtain ⟨finalStore, finalRelated, admitted, coreWP⟩ :=
    wp_floatBoxProgram_of_allocateBoxedScalar
      installation.allocatorAdapted installation.allocatorNotImport
      installation.allocatorInstalled memory32 valid related allocated
      strictEnd withinCap
  have bodyWP : Wasm.wp module installation.floatBoxTarget.body
      (fun completion => completion = .Return finalStore
        [.i32 (UInt32.ofNat address.value)]) store
      (floatBoxEntry bits) env := by
    apply installation.wp_floatBox_body (by intros; simp)
    exact coreWP
  refine ⟨finalStore, finalRelated, admitted, ?_⟩
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.floatBoxNotImport installation.floatBoxInstalled
  rw [installation.floatBox_entry bits tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.floatBox_signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- Lift the exact Float32 unbox core through the adapter's terminal suffix. -/
theorem Installation.wp_float32Unbox_body
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {Q : Wasm.Assertion host}
    (installation : Installation sourceModule module)
    (noFallthrough : ∀ final finalLocals, ¬Q (.Fallthrough final finalLocals))
    (coreWP : Wasm.wp module float32UnboxProgram Q store locals env) :
    Wasm.wp module installation.float32UnboxTarget.body Q store locals env := by
  rw [installation.float32Unbox_body]
  exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough coreWP

/-- Lift the exact Float unbox core through the adapter's terminal suffix. -/
theorem Installation.wp_floatUnbox_body
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {Q : Wasm.Assertion host}
    (installation : Installation sourceModule module)
    (noFallthrough : ∀ final finalLocals, ¬Q (.Fallthrough final finalLocals))
    (coreWP : Wasm.wp module floatUnboxProgram Q store locals env) :
    Wasm.wp module installation.floatUnboxTarget.body Q store locals env := by
  rw [installation.floatUnbox_body]
  exact FirTalos.Correctness.Wasm.wp_append_of_no_fallthrough
    noFallthrough coreWP

/-- The installed production Float32 unbox call returns every admitted bit
pattern exactly and preserves both the complete store and caller stack tail. -/
theorem Installation.terminatesWith_float32Unbox
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {state : MemoryState}
    {store : Wasm.Store host} {address : Word32} {bits : UInt32}
    (installation : Installation sourceModule module)
    (tail : List Wasm.Value)
    (admitted : Float32BoxAdmission state address bits)
    (related : ResidentMemoryRel state store.mem) :
    Wasm.TerminatesWith env module installation.float32UnboxIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values => final = store ∧ values = .f32 bits :: tail) := by
  have coreWP : Wasm.wp module float32UnboxProgram
      (fun completion => completion = .Return store [.f32 bits]) store
      (unboxEntry (UInt32.ofNat address.value)) env := by
    exact wp_float32UnboxProgram admitted related rfl
  have bodyWP : Wasm.wp module installation.float32UnboxTarget.body
      (fun completion => completion = .Return store [.f32 bits]) store
      (unboxEntry (UInt32.ofNat address.value)) env := by
    exact installation.wp_float32Unbox_body (by intros; simp) coreWP
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.float32UnboxNotImport installation.float32UnboxInstalled
  rw [installation.float32Unbox_entry (UInt32.ofNat address.value) tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.float32Unbox_signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- The installed production Float unbox call returns every admitted 64-bit
pattern exactly and preserves both the complete store and caller stack tail. -/
theorem Installation.terminatesWith_floatUnbox
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {state : MemoryState}
    {store : Wasm.Store host} {address : Word32} {bits : UInt64}
    (installation : Installation sourceModule module)
    (tail : List Wasm.Value)
    (admitted : FloatBoxAdmission state address bits)
    (related : ResidentMemoryRel state store.mem) :
    Wasm.TerminatesWith env module installation.floatUnboxIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values => final = store ∧ values = .f64 bits :: tail) := by
  have coreWP : Wasm.wp module floatUnboxProgram
      (fun completion => completion = .Return store [.f64 bits]) store
      (unboxEntry (UInt32.ofNat address.value)) env := by
    exact wp_floatUnboxProgram admitted related rfl
  have bodyWP : Wasm.wp module installation.floatUnboxTarget.body
      (fun completion => completion = .Return store [.f64 bits]) store
      (unboxEntry (UInt32.ofNat address.value)) env := by
    exact installation.wp_floatUnbox_body (by intros; simp) coreWP
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    installation.floatUnboxNotImport installation.floatUnboxInstalled
  rw [installation.floatUnbox_entry (UInt32.ofNat address.value) tail]
  apply Wasm.wp.conseq _ bodyWP
  intro completion completed
  subst completion
  obtain ⟨params, _locals, results⟩ := installation.floatUnbox_signature
  simp [FirTalos.Correctness.FunctionBodyPost, Wasm.Function.numParams,
    params, results]

/-- A body-level trap proof for the installed Float32 unbox helper is an
exact fuel-eventual statement about its public call. -/
theorem Installation.run_float32Unbox_eq_trap_of_body_wp
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store final : Wasm.Store host}
    {message : String}
    (installation : Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value)
    (bodyWP : Wasm.wp module installation.float32UnboxTarget.body
      (fun completion => completion = .Trap final message) store
      (unboxEntry object) env) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.float32UnboxIndex store
        ([.i32 object] ++ tail) env = .Trap final message := by
  unfold Wasm.wp at bodyWP
  obtain ⟨bound, bodyWP⟩ := bodyWP
  refine ⟨bound, ?_⟩
  intro fuel enoughFuel
  have trapped := bodyWP fuel enoughFuel
  rw [Wasm.run_eq installation.float32UnboxNotImport]
  simp only [installation.float32UnboxInstalled]
  rw [installation.float32Unbox_entry object tail]
  cases execution : Wasm.exec fuel module store (unboxEntry object)
      installation.float32UnboxTarget.body env <;> simp_all

/-- A body-level trap proof for the installed Float unbox helper is an exact
fuel-eventual statement about its public call. -/
theorem Installation.run_floatUnbox_eq_trap_of_body_wp
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store final : Wasm.Store host}
    {message : String}
    (installation : Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value)
    (bodyWP : Wasm.wp module installation.floatUnboxTarget.body
      (fun completion => completion = .Trap final message) store
      (unboxEntry object) env) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.floatUnboxIndex store
        ([.i32 object] ++ tail) env = .Trap final message := by
  unfold Wasm.wp at bodyWP
  obtain ⟨bound, bodyWP⟩ := bodyWP
  refine ⟨bound, ?_⟩
  intro fuel enoughFuel
  have trapped := bodyWP fuel enoughFuel
  rw [Wasm.run_eq installation.floatUnboxNotImport]
  simp only [installation.floatUnboxInstalled]
  rw [installation.floatUnbox_entry object tail]
  cases execution : Wasm.exec fuel module store (unboxEntry object)
      installation.floatUnboxTarget.body env <;> simp_all

/-- The installed Float32 unbox helper rejects every tagged immediate before
accessing resident memory. -/
theorem Installation.run_float32Unbox_tagged_eq_trap
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    (installation : Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value)
    (tagged : (1 : UInt32) &&& object ≠ 0) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.float32UnboxIndex store
        ([.i32 object] ++ tail) env = .Trap store "unreachable" := by
  apply installation.run_float32Unbox_eq_trap_of_body_wp object tail
  apply installation.wp_float32Unbox_body (by intros; simp)
  unfold float32UnboxProgram
  exact wp_unboxPrefixProgram_tagged tagged rfl

/-- The installed Float unbox helper rejects every tagged immediate before
accessing resident memory. -/
theorem Installation.run_floatUnbox_tagged_eq_trap
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    (installation : Installation sourceModule module)
    (object : UInt32) (tail : List Wasm.Value)
    (tagged : (1 : UInt32) &&& object ≠ 0) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.floatUnboxIndex store
        ([.i32 object] ++ tail) env = .Trap store "unreachable" := by
  apply installation.run_floatUnbox_eq_trap_of_body_wp object tail
  apply installation.wp_floatUnbox_body (by intros; simp)
  unfold floatUnboxProgram
  exact wp_unboxPrefixProgram_tagged tagged rfl

/-- The installed Float32 unbox helper enforces canonical zero high padding. -/
theorem Installation.run_float32Unbox_nonzeroPadding_eq_trap
    {host : Type} {sourceModule : Fir.Wasm.Module} {module : Wasm.Module}
    {env : Wasm.HostEnv host} {store : Wasm.Store host}
    (installation : Installation sourceModule module)
    (object : UInt32) (payload : UInt64) (tail : List Wasm.Value)
    (physical : PhysicalHeapBoxAdmission store object
      BoxedScalarKind.float32.code 4 payload)
    (nonzero : (payload >>> (32 : UInt64)).toUInt32 ≠ 0) :
    ∃ bound, ∀ fuel ≥ bound,
      Wasm.run fuel module installation.float32UnboxIndex store
        ([.i32 object] ++ tail) env = .Trap store "unreachable" := by
  apply installation.run_float32Unbox_eq_trap_of_body_wp object tail
  apply installation.wp_float32Unbox_body (by intros; simp)
  exact wp_float32UnboxProgram_nonzeroPadding physical nonzero rfl

end ResidentFloat

end FirTalos.Concrete
