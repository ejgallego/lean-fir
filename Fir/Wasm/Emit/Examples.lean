import Fir.Wasm.Emit.Binary
import Fir.Wasm.Emit.Manifest
import Fir.Wasm.Examples

namespace Fir.Wasm.Emit.Examples

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples
open Lean.Compiler

structure CorpusFixture where
  name : String
  program : Fir.LeanIR.ImpureProgram
  args : Array Value := #[]
  externals : ExternalImpl := rejectExternals

def abiDirectLiteralProgram (type : Lean.Expr) (literal : LCNF.LitValue) :
    Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] type (.code <|
      .let (letDecl x type (.lit literal)) (.return x))] }

def abiUInt8MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram u8Type (.uint8 255)

def abiUInt16MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram LCNF.ImpureType.uint16 (.uint16 65535)

def abiUInt32MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram LCNF.ImpureType.uint32 (.uint32 4294967295)

def abiUInt64MaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram u64Type (.uint64 18446744073709551615)

def abiUSizeMaxProgram : Fir.LeanIR.ImpureProgram :=
  abiDirectLiteralProgram usizeType (.usize 18446744073709551615)

def abiIdentityProgram (type : Lean.Expr) : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x type] type (.code (.return x))] }

def abiFirstTaggedArgumentProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[param x tobjectType, param y tobjectType]
      tobjectType (.code (.return x))] }

def abiStringHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.str "reachable"))) (.return x))] }

def abiNaturalHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat (maxTaggedPayload + 1)))) (.return x))] }

def abiNestedHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.str "reachable"))) <|
      .let (letDecl y tobjectType (.lit (.nat (maxTaggedPayload + 1)))) <|
      .let (letDecl p tobjectType (.ctor pairInfo #[.fvar x, .fvar y])) <|
      .return p)] }

def abiObjectProjectionFaultProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 7))) <|
      .let (letDecl y tobjectType (.lit (.nat 8))) <|
      .let (letDecl p objType (.ctor pairInfo #[.fvar x, .fvar y])) <|
      .let (letDecl r tobjectType (.oproj 2 p)) <|
      .return r)] }

/-- Ownership artifact that stays inside the proved constructor fragment: one
increment and decrement restore the freshly allocated object to uniqueness. -/
def abiConstructorReferenceCountingProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code <|
      .let (letDecl x tobjectType (.lit (.nat 17))) <|
      .let (letDecl p objType
        (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .inc p 1 false false <|
      .dec p 1 false false (some 1) <|
      .let (letDecl r u8Type (.isShared p)) <|
      .return r)] }

/-- Checked decrement releases an owned constructor graph before continuing
with an independent immediate result. -/
def abiConstructorGraphReleaseProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl x tobjectType (.lit (.nat 10))) <|
      .let (letDecl p objType
        (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .let (letDecl y objType
        (.ctor { pairInfo with size := 1 } #[.fvar p])) <|
      .dec y 1 true false (some 1) <|
      .let (letDecl r tobjectType (.lit (.nat 12))) <|
      .return r)] }

/-- Positive packed-layout artifact using the absolute `USize` and scalar slot
indices emitted by Lean 4.33 after one object and one `USize` slot. -/
def abiCompilerShapedMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl x tobjectType (.lit (.nat 1))) <|
      .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
      .let (letDecl u usizeType (.lit (.usize 55))) <|
      .uset p 1 u <|
      .let (letDecl s u64Type (.lit (.uint64 66))) <|
      .sset p 2 0 s u64Type <|
      .let (letDecl r u64Type (.sproj 2 0 p)) <|
      .return r)] }

/-- Compiler-shaped packed-scalar mutation/readback at the first scalar slot
after one object and one `USize` field. This parameterized fixture keeps the
three wasm32 integer widths on the same lowering path as the UInt64 corpus
case above. -/
def abiPackedScalarMutationProgram (type : Lean.Expr)
    (literal : LCNF.LitValue) : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] type (.code <|
      .let (letDecl x tobjectType (.lit (.nat 1))) <|
      .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
      .let (letDecl s type (.lit literal)) <|
      .sset p 2 0 s type <|
      .let (letDecl r type (.sproj 2 0 p)) <|
      .return r)] }

def abiUInt8MutationProgram : Fir.LeanIR.ImpureProgram :=
  abiPackedScalarMutationProgram u8Type (.uint8 255)

def abiUInt16MutationProgram : Fir.LeanIR.ImpureProgram :=
  abiPackedScalarMutationProgram LCNF.ImpureType.uint16 (.uint16 65535)

def abiUInt32MutationProgram : Fir.LeanIR.ImpureProgram :=
  abiPackedScalarMutationProgram LCNF.ImpureType.uint32 (.uint32 4294967295)

def abiCachedConstructorDecl : LCNF.Decl .impure :=
  decl `abiCachedConstructor #[] objType (.code <|
    .let (letDecl x tobjectType (.lit (.nat 42))) <|
    .let (letDecl p objType
      (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
    .return p)

/-- A concrete cache miss publishes a recursively persistent constructor;
the second generated call observes the Wasm flag/value globals and reuses it. -/
def abiCachedConstructorProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[abiCachedConstructorDecl,
      decl `main #[] tobjectType (.code <|
        .let (letDecl p objType (.fap `abiCachedConstructor #[])) <|
        .let (letDecl y objType (.fap `abiCachedConstructor #[])) <|
        .let (letDecl r tobjectType (.oproj 0 y)) <|
        .return r)] }

def abiMaxUInt64BoxRoundtripProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl s u64Type (.lit (.uint64 18446744073709551615))) <|
      .let (letDecl boxed tobjectType (.box u64Type s)) <|
      .let (letDecl r u64Type (.unbox boxed)) <|
      .return r)] }

def abiMaxUInt64HeapBoxProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] tobjectType (.code <|
      .let (letDecl s u64Type (.lit (.uint64 18446744073709551615))) <|
      .let (letDecl boxed tobjectType (.box u64Type s)) <|
      .return boxed)] }

/-- Delete-fault artifact independent of the still-gated concrete string
representation. The subsequent checked read must report logical location 0. -/
def abiConstructorDeleteFaultProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code <|
      .let (letDecl x tobjectType (.lit (.nat 18))) <|
      .let (letDecl p objType
        (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .del p <|
      .let (letDecl r u8Type (.isShared p)) <|
      .return r)] }

def abiCachedExternalProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[
      decl `cachedBinaryExternal #[] u64Type (.extern { entries := [] }),
      decl `main #[] u64Type (.code <|
        .let (letDecl x u64Type
          (.fap `cachedBinaryExternal #[])) <|
        .let (letDecl y u64Type
          (.fap `cachedBinaryExternal #[])) <|
        .return y)] }

def cachedBinaryExternalImpl : ExternalImpl where
  call _ runtime := .ok {
    value := .scalar (.uint64 91)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world + 1 }

def initialFixtures : List CorpusFixture := [
  { name := "literal", program := abiLiteralProgram },
  { name := "erased", program := abiErasedProgram },
  { name := "uint8-max", program := abiUInt8MaxProgram },
  { name := "uint16-max", program := abiUInt16MaxProgram },
  { name := "uint32-max", program := abiUInt32MaxProgram },
  { name := "uint64-max", program := abiUInt64MaxProgram },
  { name := "usize-max", program := abiUSizeMaxProgram },
  { name := "arg-erased", program := abiIdentityProgram erasedType, args := #[.erased] },
  { name := "arg-tagged-first", program := abiFirstTaggedArgumentProgram,
    args := #[.object (.tagged 11), .object (.tagged 22)] },
  { name := "arg-uint8-max", program := abiIdentityProgram u8Type,
    args := #[.scalar (.uint8 255)] },
  { name := "arg-uint16-max", program := abiIdentityProgram LCNF.ImpureType.uint16,
    args := #[.scalar (.uint16 65535)] },
  { name := "arg-uint32-max", program := abiIdentityProgram LCNF.ImpureType.uint32,
    args := #[.scalar (.uint32 4294967295)] },
  { name := "arg-uint64-max", program := abiIdentityProgram u64Type,
    args := #[.scalar (.uint64 18446744073709551615)] },
  { name := "arg-usize-max", program := abiIdentityProgram usizeType,
    args := #[.usize 18446744073709551615] },
  { name := "ctor-projection", program := abiCtorProjectionProgram },
  { name := "case", program := abiCaseProgram },
  { name := "default-case", program := abiDefaultCaseProgram },
  { name := "mutation", program := abiMutationProgram },
  { name := "object-mutation", program := abiObjectMutationProgram },
  { name := "tag-mutation", program := abiTagMutationProgram },
  { name := "reference-counting", program := rcProgram },
  { name := "constructor-reference-counting",
    program := abiConstructorReferenceCountingProgram },
  { name := "constructor-graph-release",
    program := abiConstructorGraphReleaseProgram },
  { name := "compiler-shaped-mutation", program := abiCompilerShapedMutationProgram },
  { name := "scalar-uint8-mutation", program := abiUInt8MutationProgram },
  { name := "scalar-uint16-mutation", program := abiUInt16MutationProgram },
  { name := "scalar-uint32-mutation", program := abiUInt32MutationProgram },
  { name := "cached-constructor", program := abiCachedConstructorProgram },
  { name := "box-roundtrip", program := abiMaxUInt64BoxRoundtripProgram },
  { name := "box-heap", program := abiMaxUInt64HeapBoxProgram },
  { name := "reset-reuse", program := abiResetReuseProgram },
  { name := "shared-reset-reuse", program := abiSharedResetProgram },
  { name := "delete-fault", program := deletedProgram },
  { name := "constructor-delete-fault", program := abiConstructorDeleteFaultProgram },
  { name := "direct-call", program := Fir.Wasm.abiDirectCallProgram },
  { name := "closure-call", program := Fir.Wasm.abiClosureCallProgram },
  { name := "closure-underapply", program := Fir.Wasm.abiClosureUnderApplyProgram },
  { name := "recursive-call", program := Fir.Wasm.abiRecursiveCallProgram },
  { name := "external-echo", program := externalProgram, externals := echoExternal },
  { name := "cached-external", program := abiCachedExternalProgram,
    externals := cachedBinaryExternalImpl },
  { name := "string-heap", program := abiStringHeapProgram },
  { name := "natural-heap", program := abiNaturalHeapProgram },
  { name := "nested-heap", program := abiNestedHeapProgram },
  { name := "projection-fault", program := abiObjectProjectionFaultProgram }]

def initialCorpus : Array Fir.LeanIR.ImpureProgram :=
  initialFixtures.toArray.map (·.program)

#guard
  let names := initialFixtures.map (·.name)
  names.eraseDups.length == names.length

def encodeProgram (program : Fir.LeanIR.ImpureProgram) : Except String ByteArray := do
  let module ←
    match lowerSupported program with
    | .ok module => pure module
    | .error error => throw s!"lowering failed: {repr error}"
  match encode module with
  | .ok bytes => pure bytes
  | .error error => throw s!"encoding failed: {repr error}"

#guard initialCorpus.all fun program => (encodeProgram program).isOk

#guard match encodeProgram abiCaseProgram, encodeProgram abiCaseProgram with
  | .ok first, .ok second => first == second
  | _, _ => false

#guard match encodeProgram abiLiteralProgram with
  | .ok bytes => bytes.data.extract 0 header.size == header
  | .error _ => false

/- Global section plus `global.get`/`global.set` opcodes encode as a complete
standard Wasm module for the lazy-cache path. -/
#guard (encodeProgram abiCachedExternalProgram).isOk

#guard (encodeProgram Fir.Wasm.abiDirectCallProgram).isOk
#guard (encodeProgram Fir.Wasm.abiClosureCallProgram).isOk
#guard (encodeProgram Fir.Wasm.abiClosureUnderApplyProgram).isOk
#guard (encodeProgram Fir.Wasm.abiRecursiveCallProgram).isOk
#guard (Fir.Wasm.Emit.encode Fir.Wasm.floatMachineModule).isOk

def residentAddress : Lean.FVarId := ⟨`residentAddress⟩

def residentBitsFunction : Function := {
  name := `residentBits
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [
    .i32Const .uint32 7,
    .i32Const .uint32 1,
    .i32And,
    .i32Const .uint32 1,
    .i32ShrU,
    .ret] }

def residentLoadFunction : Function := {
  name := `residentLoad
  params := #[(residentAddress, .tobject)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet residentAddress,
    .i64Load .uint64 32,
    .i32WrapI64 .uint32,
    .ret] }

def residentLoad8Function : Function := {
  name := `residentLoad8
  params := #[(residentAddress, .tobject)]
  results := #[.uint8]
  locals := #[]
  body := [
    .localGet residentAddress,
    .i32Load8U .uint8 32,
    .ret] }

def residentValue32 : Lean.FVarId := ⟨`residentValue32⟩
def residentValue64 : Lean.FVarId := ⟨`residentValue64⟩

def residentArithmeticFunction : Function := {
  name := `residentArithmetic
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [
    .i32Const .uint32 7,
    .i32Const .uint32 5,
    .i32Add,
    .i32Const .uint32 3,
    .i32Sub,
    .i32Const .uint32 4,
    .i32RemU,
    .i32Const .uint32 10,
    .i32LtU,
    .ret] }

def residentStore8Function : Function := {
  name := `residentStore8
  params := #[(residentAddress, .uint32), (residentValue32, .uint8)]
  results := #[.uint8]
  locals := #[]
  body := [
    .localGet residentAddress,
    .localGet residentValue32,
    .i32Store8 .uint8 0,
    .localGet residentAddress,
    .i32Load8U .uint8 0,
    .ret] }

def residentStore16Function : Function := {
  name := `residentStore16
  params := #[(residentAddress, .uint32), (residentValue32, .uint16)]
  results := #[.uint16]
  locals := #[]
  body := [
    .localGet residentAddress,
    .localGet residentValue32,
    .i32Store16 .uint16 0,
    .localGet residentAddress,
    .i32Load16U .uint16 0,
    .ret] }

def residentStore32Function : Function := {
  name := `residentStore32
  params := #[(residentAddress, .uint32), (residentValue32, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [
    .localGet residentAddress,
    .localGet residentValue32,
    .i32Store .uint32 0,
    .localGet residentAddress,
    .i32Load .uint32 0,
    .ret] }

def residentStore64Function : Function := {
  name := `residentStore64
  params := #[(residentAddress, .uint32), (residentValue64, .uint64)]
  results := #[.uint64]
  locals := #[]
  body := [
    .localGet residentAddress,
    .localGet residentValue64,
    .i64Store .uint64 0,
    .localGet residentAddress,
    .i64Load .uint64 0,
    .ret] }

def residentMemorySizeFunction : Function := {
  name := `residentMemorySize
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [.memorySize, .ret] }

def residentMemoryGrowFunction : Function := {
  name := `residentMemoryGrow
  params := #[(residentValue32, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [.localGet residentValue32, .memoryGrow, .ret] }

def residentLoop : Lean.FVarId := ⟨`residentLoop⟩

/-- Encoding witness for the structured loop surface consumed by resident
runtime walkers. The zero arm returns; every nonzero arm decrements and
branches to the loop header without growing the Wasm call stack. -/
def residentLoopFunction : Function := {
  name := `residentLoop
  params := #[(residentValue32, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [
    .loop residentLoop [
      .localGet residentValue32,
      .i32Const .uint32 0,
      .i32Eq,
      .ifElse [.localGet residentValue32, .ret] [],
      .localGet residentValue32,
      .i32Const .uint32 1,
      .i32Sub,
      .localSet residentValue32,
      .br residentLoop]] }

/-- W7 shared-surface guard. Existing modules omit memory; a resident-runtime
module may define/export it and use checked physical memory instructions. -/
def residentMemorySurfaceModule : Module := {
  imports := #[]
  functions := #[
    residentBitsFunction,
    residentLoadFunction,
    residentLoad8Function,
    residentArithmeticFunction,
    residentStore8Function,
    residentStore16Function,
    residentStore32Function,
    residentStore64Function,
    residentMemorySizeFunction,
    residentMemoryGrowFunction,
    residentLoopFunction]
  exports := #[
    `residentBits,
    `residentLoad,
    `residentLoad8,
    `residentArithmetic,
    `residentStore8,
    `residentStore16,
    `residentStore32,
    `residentStore64,
    `residentMemorySize,
    `residentMemoryGrow]
  initializers := #[]
  runtimeOperations := #[]
  memory := some { pagesMin := 1, exportName := some "memory" }
  dataSegments := #[{
    offset := 2048
    bytes := #[0xde, 0xad, 0xbe, 0xef] }] }

#guard validateModule residentMemorySurfaceModule |>.isOk
#guard encode residentMemorySurfaceModule |>.isOk

def residentGlobalFunction : Function := {
  name := `residentGlobal
  params := #[]
  results := #[.uint32]
  locals := #[]
  body := [.globalGet 0 .uint32, .ret] }

def residentGlobalValue : Lean.FVarId := ⟨`residentGlobalValue⟩

def residentGlobalSetFunction : Function := {
  name := `residentGlobalSet
  params := #[(residentGlobalValue, .uint32)]
  results := #[]
  locals := #[]
  body := [
    .localGet residentGlobalValue,
    .globalSet 0 .uint32,
    .ret] }

/-- Shared W7 surface: resident globals retain typed nonzero initialization. -/
def residentGlobalSurfaceModule : Module := {
  imports := #[]
  functions := #[residentGlobalFunction, residentGlobalSetFunction]
  exports := #[`residentGlobal, `residentGlobalSet]
  initializers := #[]
  runtimeOperations := #[]
  globals := #[{ kind := .uint32, init := .i32 1024 }] }

#guard residentGlobalSurfaceModule.globalKinds == #[.uint32]
#guard validateModule residentGlobalSurfaceModule |>.isOk
#guard encode residentGlobalSurfaceModule |>.isOk

#guard match validateModule {
    residentGlobalSurfaceModule with
    globals := #[{ kind := .uint32, init := .i64 1024 }] } with
  | .error (.invalidGlobalInitializer 0) => true
  | _ => false

#guard match validateModule {
    residentMemorySurfaceModule with memory := none, dataSegments := #[] } with
  | .error (.memoryInstructionWithoutMemory `residentLoad) => true
  | _ => false

#guard match validateModule {
    residentMemorySurfaceModule with
    memory := some { pagesMin := 65537 } } with
  | .error .invalidMemoryLimits => true
  | _ => false

#guard match validateModule {
    residentMemorySurfaceModule with memory := none } with
  | .error (.dataSegmentWithoutMemory 0) => true
  | _ => false

#guard match validateModule {
    residentMemorySurfaceModule with
    dataSegments := #[{ offset := 65535, bytes := #[0, 1] }] } with
  | .error (.dataSegmentOutOfBounds 0) => true
  | _ => false

def w5ManifestOperations : Array RuntimeOp := #[
  .usizeProj 0,
  .scalarProj 4 0 .uint32,
  .cacheSet `cached .uint64,
  .partialApply `callee 2 1 #[.tobject] .tobject,
  .closureMatches `callee 2 1,
  .closureProj `callee 2 1 0 .tobject,
  .box .uint32 .tobject,
  .unbox .uint32,
  .isShared,
  .reset 2,
  .reuse pairInfo true #[.tobject, .tobject] .object,
  .objectSet 0 .tobject,
  .usizeSet 0,
  .scalarSet 4 0 .uint32,
  .setTag 1,
  .inc 1 false,
  .dec 1 false (some 2),
  .delete]

#guard w5ManifestOperations.all fun operation =>
  (Fir.Wasm.Emit.Manifest.operationJson operation).isOk

#guard match Fir.Wasm.Emit.Manifest.operationJson
    (.closureApply #[.tobject] #[.tobject]) with
  | .error _ => true
  | .ok _ => false

#guard (Fir.Wasm.Emit.Manifest.heapObjectJson (.integer (-2147483649))).isOk
#guard (Fir.Wasm.Emit.Manifest.heapObjectJson (.byteArray #[0, 127, 128, 255])).isOk
#guard (Fir.Wasm.Emit.Manifest.heapObjectJson
  (.boxed LCNF.ImpureType.uint64 (.scalar (.uint64 0xffffffffffffffff)))).isOk
#guard match Fir.Wasm.Emit.Manifest.heapObjectJson
    (.boxed LCNF.ImpureType.uint8 (.scalar (.uint16 1))) with
  | .error _ => true
  | .ok _ => false

private def float32NaNPayloadJson : Lean.Json :=
  Lean.Json.mkObj [("kind", "float32"), ("value", "2143289345")]

private def float64NegativeZeroJson : Lean.Json :=
  Lean.Json.mkObj [("kind", "float"), ("value", "9223372036854775808")]

private def float32NaNPayloadArgumentJson : Lean.Json :=
  Lean.Json.mkObj [
    ("kind", "scalar"),
    ("scalarKind", "float32"),
    ("value", "2143289345")]

private def float64NegativeZeroArgumentJson : Lean.Json :=
  Lean.Json.mkObj [
    ("kind", "scalar"),
    ("scalarKind", "float"),
    ("value", "9223372036854775808")]

private def isExpectedJson (expected : Lean.Json) : Except String Lean.Json → Bool
  | .ok actual => actual == expected
  | .error _ => false

private def isManifestError : Except String Lean.Json → Bool
  | .ok _ => false
  | .error _ => true

#guard Fir.Wasm.Emit.Manifest.scalarValueJson
  (.float32Bits 0x7fc00001) == float32NaNPayloadJson
#guard Fir.Wasm.Emit.Manifest.scalarValueJson
  (.float64Bits 0x8000000000000000) == float64NegativeZeroJson

#guard isExpectedJson float32NaNPayloadArgumentJson <|
  Fir.Wasm.Emit.Manifest.argumentJson .float32
    (.scalar (.float32Bits 0x7fc00001))
#guard isExpectedJson float64NegativeZeroArgumentJson <|
  Fir.Wasm.Emit.Manifest.argumentJson .float
    (.scalar (.float64Bits 0x8000000000000000))
#guard isExpectedJson float32NaNPayloadArgumentJson <|
  Fir.Wasm.Emit.Manifest.argumentJsonWithRuntime {} .float32
    (.scalar (.float32Bits 0x7fc00001))
#guard isExpectedJson float64NegativeZeroArgumentJson <|
  Fir.Wasm.Emit.Manifest.argumentJsonWithRuntime {} .float
    (.scalar (.float64Bits 0x8000000000000000))

#guard isManifestError <| Fir.Wasm.Emit.Manifest.argumentJson .float32
  (.scalar (.float64Bits 0x7ff8000000000001))
#guard isManifestError <| Fir.Wasm.Emit.Manifest.argumentJson .float
  (.scalar (.float32Bits 0x80000000))
#guard isManifestError <| Fir.Wasm.Emit.Manifest.argumentJsonWithRuntime {} .float32
  (.scalar (.float64Bits 0x7ff8000000000001))
#guard isManifestError <| Fir.Wasm.Emit.Manifest.argumentJsonWithRuntime {} .float
  (.scalar (.float32Bits 0x80000000))

/-! ## Complete scalar Wasm instruction surface

This fixture deliberately mentions every typed scalar constructor.  It keeps
symbolic validation and binary encoding exhaustive as the resident runtime
moves away from synthesized machine arithmetic.  The Talos side imports the
same module and checks adaptation independently.
-/

private def surfaceLeft : Lean.FVarId := ⟨`surfaceLeft⟩
private def surfaceRight : Lean.FVarId := ⟨`surfaceRight⟩

private def unarySurfaceFunction (name : Lean.Name) (param result : AbiKind)
    (instruction : Instruction) : Function := {
  name
  params := #[(surfaceLeft, param)]
  results := #[result]
  locals := #[]
  body := [.localGet surfaceLeft, instruction, .ret] }

private def binarySurfaceFunction (name : Lean.Name) (param result : AbiKind)
    (instruction : Instruction) : Function := {
  name
  params := #[(surfaceLeft, param), (surfaceRight, param)]
  results := #[result]
  locals := #[]
  body := [.localGet surfaceLeft, .localGet surfaceRight, instruction, .ret] }

private def constantSurfaceFunction (name : Lean.Name) (result : AbiKind)
    (instruction : Instruction) : Function := {
  name
  params := #[]
  results := #[result]
  locals := #[]
  body := [instruction, .ret] }

private def loadSurfaceFunction (name : Lean.Name) (result : AbiKind)
    (instruction : Instruction) : Function := {
  name
  params := #[(surfaceLeft, .uint32)]
  results := #[result]
  locals := #[]
  body := [.localGet surfaceLeft, instruction, .ret] }

private def storeSurfaceFunction (name : Lean.Name) (value : AbiKind)
    (instruction : Instruction) : Function := {
  name
  params := #[(surfaceLeft, .uint32), (surfaceRight, value)]
  results := #[]
  locals := #[]
  body := [.localGet surfaceLeft, .localGet surfaceRight, instruction, .ret] }

def i32UnarySurfaceFunctions : Array Function := #[
  unarySurfaceFunction `surfaceI32Eqz .uint32 .uint32 .i32Eqz,
  unarySurfaceFunction `surfaceI32Clz .uint32 .uint32 .i32Clz,
  unarySurfaceFunction `surfaceI32Ctz .uint32 .uint32 .i32Ctz,
  unarySurfaceFunction `surfaceI32Popcnt .uint32 .uint32 .i32Popcnt]

def i32BinarySurfaceFunctions : Array Function := #[
  binarySurfaceFunction `surfaceI32Eq .uint32 .uint32 .i32Eq,
  binarySurfaceFunction `surfaceI32Ne .uint32 .uint32 .i32Ne,
  binarySurfaceFunction `surfaceI32LtS .uint32 .uint32 .i32LtS,
  binarySurfaceFunction `surfaceI32LtU .uint32 .uint32 .i32LtU,
  binarySurfaceFunction `surfaceI32GtS .uint32 .uint32 .i32GtS,
  binarySurfaceFunction `surfaceI32GtU .uint32 .uint32 .i32GtU,
  binarySurfaceFunction `surfaceI32LeS .uint32 .uint32 .i32LeS,
  binarySurfaceFunction `surfaceI32LeU .uint32 .uint32 .i32LeU,
  binarySurfaceFunction `surfaceI32GeS .uint32 .uint32 .i32GeS,
  binarySurfaceFunction `surfaceI32GeU .uint32 .uint32 .i32GeU,
  binarySurfaceFunction `surfaceI32Add .uint32 .uint32 .i32Add,
  binarySurfaceFunction `surfaceI32Sub .uint32 .uint32 .i32Sub,
  binarySurfaceFunction `surfaceI32Mul .uint32 .uint32 .i32Mul,
  binarySurfaceFunction `surfaceI32DivS .uint32 .uint32 .i32DivS,
  binarySurfaceFunction `surfaceI32DivU .uint32 .uint32 .i32DivU,
  binarySurfaceFunction `surfaceI32RemS .uint32 .uint32 .i32RemS,
  binarySurfaceFunction `surfaceI32RemU .uint32 .uint32 .i32RemU,
  binarySurfaceFunction `surfaceI32And .uint32 .uint32 .i32And,
  binarySurfaceFunction `surfaceI32Or .uint32 .uint32 .i32Or,
  binarySurfaceFunction `surfaceI32Xor .uint32 .uint32 .i32Xor,
  binarySurfaceFunction `surfaceI32Shl .uint32 .uint32 .i32Shl,
  binarySurfaceFunction `surfaceI32ShrS .uint32 .uint32 .i32ShrS,
  binarySurfaceFunction `surfaceI32ShrU .uint32 .uint32 .i32ShrU,
  binarySurfaceFunction `surfaceI32Rotl .uint32 .uint32 .i32Rotl,
  binarySurfaceFunction `surfaceI32Rotr .uint32 .uint32 .i32Rotr]

def i64UnarySurfaceFunctions : Array Function := #[
  unarySurfaceFunction `surfaceI64Eqz .uint64 .uint32 .i64Eqz,
  unarySurfaceFunction `surfaceI64Clz .uint64 .uint64 .i64Clz,
  unarySurfaceFunction `surfaceI64Ctz .uint64 .uint64 .i64Ctz,
  unarySurfaceFunction `surfaceI64Popcnt .uint64 .uint64 .i64Popcnt]

def i64BinarySurfaceFunctions : Array Function := #[
  binarySurfaceFunction `surfaceI64Eq .uint64 .uint32 .i64Eq,
  binarySurfaceFunction `surfaceI64Ne .uint64 .uint32 .i64Ne,
  binarySurfaceFunction `surfaceI64LtS .uint64 .uint32 .i64LtS,
  binarySurfaceFunction `surfaceI64LtU .uint64 .uint32 .i64LtU,
  binarySurfaceFunction `surfaceI64GtS .uint64 .uint32 .i64GtS,
  binarySurfaceFunction `surfaceI64GtU .uint64 .uint32 .i64GtU,
  binarySurfaceFunction `surfaceI64LeS .uint64 .uint32 .i64LeS,
  binarySurfaceFunction `surfaceI64LeU .uint64 .uint32 .i64LeU,
  binarySurfaceFunction `surfaceI64GeS .uint64 .uint32 .i64GeS,
  binarySurfaceFunction `surfaceI64GeU .uint64 .uint32 .i64GeU,
  binarySurfaceFunction `surfaceI64Add .uint64 .uint64 .i64Add,
  binarySurfaceFunction `surfaceI64Sub .uint64 .uint64 .i64Sub,
  binarySurfaceFunction `surfaceI64Mul .uint64 .uint64 .i64Mul,
  binarySurfaceFunction `surfaceI64DivS .uint64 .uint64 .i64DivS,
  binarySurfaceFunction `surfaceI64DivU .uint64 .uint64 .i64DivU,
  binarySurfaceFunction `surfaceI64RemS .uint64 .uint64 .i64RemS,
  binarySurfaceFunction `surfaceI64RemU .uint64 .uint64 .i64RemU,
  binarySurfaceFunction `surfaceI64And .uint64 .uint64 .i64And,
  binarySurfaceFunction `surfaceI64Or .uint64 .uint64 .i64Or,
  binarySurfaceFunction `surfaceI64Xor .uint64 .uint64 .i64Xor,
  binarySurfaceFunction `surfaceI64Shl .uint64 .uint64 .i64Shl,
  binarySurfaceFunction `surfaceI64ShrS .uint64 .uint64 .i64ShrS,
  binarySurfaceFunction `surfaceI64ShrU .uint64 .uint64 .i64ShrU,
  binarySurfaceFunction `surfaceI64Rotl .uint64 .uint64 .i64Rotl,
  binarySurfaceFunction `surfaceI64Rotr .uint64 .uint64 .i64Rotr]

def f32UnarySurfaceFunctions : Array Function := #[
  unarySurfaceFunction `surfaceF32Abs .float32 .float32 .f32Abs,
  unarySurfaceFunction `surfaceF32Neg .float32 .float32 .f32Neg,
  unarySurfaceFunction `surfaceF32Ceil .float32 .float32 .f32Ceil,
  unarySurfaceFunction `surfaceF32Floor .float32 .float32 .f32Floor,
  unarySurfaceFunction `surfaceF32Trunc .float32 .float32 .f32Trunc,
  unarySurfaceFunction `surfaceF32Nearest .float32 .float32 .f32Nearest,
  unarySurfaceFunction `surfaceF32Sqrt .float32 .float32 .f32Sqrt]

def f32BinarySurfaceFunctions : Array Function := #[
  binarySurfaceFunction `surfaceF32Eq .float32 .uint32 .f32Eq,
  binarySurfaceFunction `surfaceF32Ne .float32 .uint32 .f32Ne,
  binarySurfaceFunction `surfaceF32Lt .float32 .uint32 .f32Lt,
  binarySurfaceFunction `surfaceF32Gt .float32 .uint32 .f32Gt,
  binarySurfaceFunction `surfaceF32Le .float32 .uint32 .f32Le,
  binarySurfaceFunction `surfaceF32Ge .float32 .uint32 .f32Ge,
  binarySurfaceFunction `surfaceF32Add .float32 .float32 .f32Add,
  binarySurfaceFunction `surfaceF32Sub .float32 .float32 .f32Sub,
  binarySurfaceFunction `surfaceF32Mul .float32 .float32 .f32Mul,
  binarySurfaceFunction `surfaceF32Div .float32 .float32 .f32Div,
  binarySurfaceFunction `surfaceF32Min .float32 .float32 .f32Min,
  binarySurfaceFunction `surfaceF32Max .float32 .float32 .f32Max,
  binarySurfaceFunction `surfaceF32Copysign .float32 .float32 .f32Copysign]

def f64UnarySurfaceFunctions : Array Function := #[
  unarySurfaceFunction `surfaceF64Abs .float .float .f64Abs,
  unarySurfaceFunction `surfaceF64Neg .float .float .f64Neg,
  unarySurfaceFunction `surfaceF64Ceil .float .float .f64Ceil,
  unarySurfaceFunction `surfaceF64Floor .float .float .f64Floor,
  unarySurfaceFunction `surfaceF64Trunc .float .float .f64Trunc,
  unarySurfaceFunction `surfaceF64Nearest .float .float .f64Nearest,
  unarySurfaceFunction `surfaceF64Sqrt .float .float .f64Sqrt]

def f64BinarySurfaceFunctions : Array Function := #[
  binarySurfaceFunction `surfaceF64Eq .float .uint32 .f64Eq,
  binarySurfaceFunction `surfaceF64Ne .float .uint32 .f64Ne,
  binarySurfaceFunction `surfaceF64Lt .float .uint32 .f64Lt,
  binarySurfaceFunction `surfaceF64Gt .float .uint32 .f64Gt,
  binarySurfaceFunction `surfaceF64Le .float .uint32 .f64Le,
  binarySurfaceFunction `surfaceF64Ge .float .uint32 .f64Ge,
  binarySurfaceFunction `surfaceF64Add .float .float .f64Add,
  binarySurfaceFunction `surfaceF64Sub .float .float .f64Sub,
  binarySurfaceFunction `surfaceF64Mul .float .float .f64Mul,
  binarySurfaceFunction `surfaceF64Div .float .float .f64Div,
  binarySurfaceFunction `surfaceF64Min .float .float .f64Min,
  binarySurfaceFunction `surfaceF64Max .float .float .f64Max,
  binarySurfaceFunction `surfaceF64Copysign .float .float .f64Copysign]

def conversionSurfaceFunctions : Array Function := #[
  unarySurfaceFunction `surfaceI32WrapI64 .uint64 .uint32 (.i32WrapI64 .uint32),
  unarySurfaceFunction `surfaceI64ExtendI32S .uint32 .uint64 (.i64ExtendI32S .uint64),
  unarySurfaceFunction `surfaceI64ExtendI32U .uint32 .uint64 (.i64ExtendI32U .uint64),
  unarySurfaceFunction `surfaceI32Extend8S .uint32 .uint32 (.i32Extend8S .uint32),
  unarySurfaceFunction `surfaceI32Extend16S .uint32 .uint32 (.i32Extend16S .uint32),
  unarySurfaceFunction `surfaceI64Extend8S .uint64 .uint64 (.i64Extend8S .uint64),
  unarySurfaceFunction `surfaceI64Extend16S .uint64 .uint64 (.i64Extend16S .uint64),
  unarySurfaceFunction `surfaceI64Extend32S .uint64 .uint64 (.i64Extend32S .uint64),
  unarySurfaceFunction `surfaceF32ConvertI32S .uint32 .float32 .f32ConvertI32S,
  unarySurfaceFunction `surfaceF32ConvertI32U .uint32 .float32 .f32ConvertI32U,
  unarySurfaceFunction `surfaceF32ConvertI64S .uint64 .float32 .f32ConvertI64S,
  unarySurfaceFunction `surfaceF32ConvertI64U .uint64 .float32 .f32ConvertI64U,
  unarySurfaceFunction `surfaceF64ConvertI32S .uint32 .float .f64ConvertI32S,
  unarySurfaceFunction `surfaceF64ConvertI32U .uint32 .float .f64ConvertI32U,
  unarySurfaceFunction `surfaceF64ConvertI64S .uint64 .float .f64ConvertI64S,
  unarySurfaceFunction `surfaceF64ConvertI64U .uint64 .float .f64ConvertI64U,
  unarySurfaceFunction `surfaceI32TruncF32S .float32 .uint32 (.i32TruncF32S .uint32),
  unarySurfaceFunction `surfaceI32TruncF32U .float32 .uint32 (.i32TruncF32U .uint32),
  unarySurfaceFunction `surfaceI32TruncF64S .float .uint32 (.i32TruncF64S .uint32),
  unarySurfaceFunction `surfaceI32TruncF64U .float .uint32 (.i32TruncF64U .uint32),
  unarySurfaceFunction `surfaceI64TruncF32S .float32 .uint64 (.i64TruncF32S .uint64),
  unarySurfaceFunction `surfaceI64TruncF32U .float32 .uint64 (.i64TruncF32U .uint64),
  unarySurfaceFunction `surfaceI64TruncF64S .float .uint64 (.i64TruncF64S .uint64),
  unarySurfaceFunction `surfaceI64TruncF64U .float .uint64 (.i64TruncF64U .uint64),
  unarySurfaceFunction `surfaceI32TruncSatF32S .float32 .uint32 (.i32TruncSatF32S .uint32),
  unarySurfaceFunction `surfaceI32TruncSatF32U .float32 .uint32 (.i32TruncSatF32U .uint32),
  unarySurfaceFunction `surfaceI32TruncSatF64S .float .uint32 (.i32TruncSatF64S .uint32),
  unarySurfaceFunction `surfaceI32TruncSatF64U .float .uint32 (.i32TruncSatF64U .uint32),
  unarySurfaceFunction `surfaceI64TruncSatF32S .float32 .uint64 (.i64TruncSatF32S .uint64),
  unarySurfaceFunction `surfaceI64TruncSatF32U .float32 .uint64 (.i64TruncSatF32U .uint64),
  unarySurfaceFunction `surfaceI64TruncSatF64S .float .uint64 (.i64TruncSatF64S .uint64),
  unarySurfaceFunction `surfaceI64TruncSatF64U .float .uint64 (.i64TruncSatF64U .uint64),
  unarySurfaceFunction `surfaceF32DemoteF64 .float .float32 .f32DemoteF64,
  unarySurfaceFunction `surfaceF64PromoteF32 .float32 .float .f64PromoteF32,
  unarySurfaceFunction `surfaceI32ReinterpretF32 .float32 .uint32 (.i32ReinterpretF32 .uint32),
  unarySurfaceFunction `surfaceI64ReinterpretF64 .float .uint64 (.i64ReinterpretF64 .uint64),
  unarySurfaceFunction `surfaceF32ReinterpretI32 .uint32 .float32 (.f32ReinterpretI32 .float32),
  unarySurfaceFunction `surfaceF64ReinterpretI64 .uint64 .float (.f64ReinterpretI64 .float)]

def memorySurfaceFunctions : Array Function := #[
  loadSurfaceFunction `surfaceI32Load .uint32 (.i32Load .uint32 0),
  loadSurfaceFunction `surfaceI32Load8S .uint32 (.i32Load8S .uint32 0),
  loadSurfaceFunction `surfaceI32Load8U .uint32 (.i32Load8U .uint32 0),
  loadSurfaceFunction `surfaceI32Load16S .uint32 (.i32Load16S .uint32 0),
  loadSurfaceFunction `surfaceI32Load16U .uint32 (.i32Load16U .uint32 0),
  loadSurfaceFunction `surfaceI64Load .uint64 (.i64Load .uint64 0),
  loadSurfaceFunction `surfaceI64Load8S .uint64 (.i64Load8S .uint64 0),
  loadSurfaceFunction `surfaceI64Load8U .uint64 (.i64Load8U .uint64 0),
  loadSurfaceFunction `surfaceI64Load16S .uint64 (.i64Load16S .uint64 0),
  loadSurfaceFunction `surfaceI64Load16U .uint64 (.i64Load16U .uint64 0),
  loadSurfaceFunction `surfaceI64Load32S .uint64 (.i64Load32S .uint64 0),
  loadSurfaceFunction `surfaceI64Load32U .uint64 (.i64Load32U .uint64 0),
  loadSurfaceFunction `surfaceF32Load .float32 (.f32Load 0),
  loadSurfaceFunction `surfaceF64Load .float (.f64Load 0),
  storeSurfaceFunction `surfaceI32Store .uint32 (.i32Store .uint32 0),
  storeSurfaceFunction `surfaceI32Store8 .uint32 (.i32Store8 .uint32 0),
  storeSurfaceFunction `surfaceI32Store16 .uint32 (.i32Store16 .uint32 0),
  storeSurfaceFunction `surfaceI64Store .uint64 (.i64Store .uint64 0),
  storeSurfaceFunction `surfaceI64Store8 .uint64 (.i64Store8 .uint64 0),
  storeSurfaceFunction `surfaceI64Store16 .uint64 (.i64Store16 .uint64 0),
  storeSurfaceFunction `surfaceI64Store32 .uint64 (.i64Store32 .uint64 0),
  storeSurfaceFunction `surfaceF32Store .float32 (.f32Store 0),
  storeSurfaceFunction `surfaceF64Store .float (.f64Store 0),
  unarySurfaceFunction `surfaceMemoryGrow .uint32 .uint32 .memoryGrow,
  constantSurfaceFunction `surfaceMemorySize .uint32 .memorySize]

def scalarSurfaceFunctions : Array Function :=
  #[constantSurfaceFunction `surfaceF32Const .float32 (.f32Const 0x3f800000),
    constantSurfaceFunction `surfaceF64Const .float (.f64Const 0x3ff0000000000000)] ++
  i32UnarySurfaceFunctions ++ i32BinarySurfaceFunctions ++
  i64UnarySurfaceFunctions ++ i64BinarySurfaceFunctions ++
  f32UnarySurfaceFunctions ++ f32BinarySurfaceFunctions ++
  f64UnarySurfaceFunctions ++ f64BinarySurfaceFunctions ++
  conversionSurfaceFunctions ++ memorySurfaceFunctions

def scalarSurfaceModule : Module := {
  imports := #[]
  functions := scalarSurfaceFunctions
  exports := scalarSurfaceFunctions.map (·.name)
  initializers := #[]
  runtimeOperations := #[]
  memory := some { pagesMin := 1, exportName := some "memory" } }

#guard scalarSurfaceFunctions.size == 163
#guard validateModule scalarSurfaceModule |>.isOk
#guard encode scalarSurfaceModule |>.isOk

end Fir.Wasm.Emit.Examples
