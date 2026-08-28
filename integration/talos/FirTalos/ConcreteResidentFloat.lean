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

/-- Physical Talos prefix common to both floating box helpers. -/
def boxPrefixProgram (allocatorIndex address : Nat)
    (marker payloadBytes : UInt32) : Wasm.Program :=
  [.const 40, .call allocatorIndex, .localSet address] ++
  zeroAllocationProgram address ++
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
