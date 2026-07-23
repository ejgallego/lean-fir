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
indices emitted by Lean 4.32 after one object and one `USize` slot. -/
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

end Fir.Wasm.Emit.Examples
