import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

private def emptyHostStore : Wasm.Store Host :=
  ({ funcs := [] } : Wasm.Module).initialStore

-- The executable concrete host decodes immediate object words without any
-- semantic handle table.
#guard match getTagStep emptyHostStore [.i32 15] with
  | .Return [.i32 tag] store =>
      tag == 7 && store.host.failure?.isNone
  | _ => false

-- ABI arity failures are retained separately from checked heap failures.
#guard match getTagStep emptyHostStore [] with
  | .Trap store _ =>
      store.host.failure? == some (.arityMismatch 1 0)
  | _ => false

-- A correctly sized call with the wrong physical lane has its own diagnosis.
#guard match getTagStep emptyHostStore [.i64 0] with
  | .Trap store _ =>
      store.host.failure? == some (.laneMismatch 0 .i32)
  | _ => false

private def projectionInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.projection
  cidx := 3
  size := 1
  usize := 0
  ssize := 0 }

private def objectProjectionFixture :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let field := Word32.encodeImmediate 11 (by decide)
  let (heap, object) ← allocateConstructor MemoryState.initial projectionInfo
    #[field]
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, object)

-- The concrete Talos host projects the exact word stored in an eight-byte
-- semantic object slot and leaves its failure channel clear.
#guard match objectProjectionFixture with
  | .ok (store, object) =>
      match objectProjStep 0 store [.i32 (UInt32.ofNat object.value)] with
      | .Return [.i32 field] next =>
          field == 23 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

private def usizeProjectionInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.usizeProjection
  cidx := 4
  size := 0
  usize := 1
  ssize := 0 }

private def usizeProjectionFixture :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let (heap, object) ← allocateConstructor MemoryState.initial
    usizeProjectionInfo #[]
  let heap ← writeUSizeField heap object 0 18446744073709551615
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, object)

-- USize projection preserves the full Lean64 payload in an i64 lane.
#guard match usizeProjectionFixture with
  | .ok (store, object) =>
      match usizeProjStep 0 store [.i32 (UInt32.ofNat object.value)] with
      | .Return [.i64 value] next =>
          value == 18446744073709551615 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

private def scalarProjectionInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.scalarProjection
  cidx := 5
  size := 0
  usize := 0
  ssize := 8 }

private def scalarProjectionFixture :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let (heap, object) ← allocateConstructor MemoryState.initial
    scalarProjectionInfo #[]
  let heap ← writeScalarUInt64Field heap object 0 0 18446744073709551615
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, object)

-- The packed-scalar dispatcher preserves a 64-bit field and lane exactly.
#guard match scalarProjectionFixture with
  | .ok (store, object) =>
      match scalarProjStep 0 0 .uint64 store
          [.i32 (UInt32.ofNat object.value)] with
      | .Return [.i64 value] next =>
          value == 18446744073709551615 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

-- Float scalar kinds remain an explicit structured fragment gate.
#guard match scalarProjStep 0 0 .float32 emptyHostStore [.i32 1] with
  | .Trap store _ =>
      store.host.failure? == some (.unsupportedScalarKind .float32)
  | _ => false

-- Small naturals stay immediate and do not move the concrete heap frontier.
#guard match naturalLiteralStep 42 emptyHostStore [] with
  | .Return [.i32 word] store =>
      word == 85 && store.host.runtime.heap.heapCursor == heapBase &&
        store.host.failure?.isNone
  | _ => false

-- Large naturals allocate their complete little-endian limb representation.
#guard match naturalLiteralStep (UInt64.size + 5) emptyHostStore [] with
  | .Return [.i32 bits] store =>
      let word := Word32.ofUInt32 bits
      match readNatural store.host.runtime.heap word with
      | .ok value => value == UInt64.size + 5 && store.host.failure?.isNone
      | .error _ => false
  | _ => false

private def emptyConstructorInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.emptyConstructor
  cidx := 7
  size := 0
  usize := 0
  ssize := 0 }

-- Empty constructor allocation uses the exact tagged wasm32 representation
-- and does not allocate when the tag is immediate.
#guard match allocCtorStep emptyConstructorInfo #[] .tagged emptyHostStore [] with
  | .Return [.i32 word] store =>
      word == 15 && store.host.runtime.heap.heapCursor == heapBase &&
        store.host.failure?.isNone
  | _ => false

private def unaryConstructorInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.unaryConstructor
  cidx := 8
  size := 1
  usize := 0
  ssize := 0 }

-- Nonempty constructor allocation writes the exact supplied object word into
-- its semantic slot and exposes the checked tag through the concrete decoder.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 bits] store =>
      let object := Word32.ofUInt32 bits
      match readTag store.host.runtime.heap object,
          readObjectField store.host.runtime.heap object 0 with
      | .ok tag, .ok field =>
          tag == 8 && field.value == 23 && store.host.failure?.isNone
      | _, _ => false
  | _ => false

-- Ordinary objects update only their checked header reference count.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match incrementStep 2 true store [.i32 object] with
      | .Return [] next =>
          match next.host.runtime.heap.readLiveHeader (Word32.ofUInt32 object) with
          | .ok header =>
              header.refCount == 3 && next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | _ => false

-- A tagged value promoted past wasm32's immediate range remains a checked
-- no-op even though its concrete word is a heap address.
#guard match naturalLiteralStep 2147483648 emptyHostStore [] with
  | .Return [.i32 object] store =>
      let cursor := store.host.runtime.heap.heapCursor
      match incrementStep 7 true store [.i32 object] with
      | .Return [] next =>
          match readTag next.host.runtime.heap (Word32.ofUInt32 object) with
          | .ok tag =>
              tag.toNat == 2147483648 &&
                next.host.runtime.heap.heapCursor == cursor &&
                next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | _ => false

-- Constructor-tag mutation rewrites only the checked header: the new tag is
-- visible while the existing object payload remains byte-for-byte decodable.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match setTagStep 19 store [.i32 object] with
      | .Return [] next =>
          match readTag next.host.runtime.heap (Word32.ofUInt32 object),
              readObjectField next.host.runtime.heap (Word32.ofUInt32 object) 0 with
          | .ok tag, .ok field =>
              tag == 19 && field.value == 23 && next.host.failure?.isNone
          | _, _ => false
      | _ => false
  | _ => false

private def cacheDeclaration : Lean.Name := `FirTalos.Concrete.cachedValue

private def cacheStore : Wasm.Store Host := {
  emptyHostStore with
  host := { emptyHostStore.host with
    runtime := { emptyHostStore.host.runtime with
      globals := ConcreteGlobals.declare [(cacheDeclaration, .uint64)] } } }

-- Cache writes preserve the full i64 lane and return it unchanged for the
-- generated Wasm value-global update.
#guard match cacheSetStep cacheDeclaration .uint64 cacheStore
    [.i64 18446744073709551615] with
  | .Return [.i64 returned] store =>
      match store.host.runtime.readGlobal cacheDeclaration .uint64 with
      | .ok (.word64 cached) =>
          returned == 18446744073709551615 && cached == returned &&
            store.host.failure?.isNone
      | _ => false
  | _ => false

private def closureTarget : Lean.Name := `FirTalos.Concrete.closureTarget

private def closureStore : Wasm.Store Host := {
  emptyHostStore with
  host := { emptyHostStore.host with
    closureDispatch := #[closureTarget]
    closureDescriptors := #[#[.uint64]] } }

-- Partial application stores the exact typed capture and returns a concrete
-- heap address; no semantic closure or handle table participates at runtime.
#guard match partialApplyStep closureTarget 2 1 #[.uint64] .object closureStore
    [.i64 18446744073709551615] with
  | .Return [.i32 bits] store =>
      let object := Word32.ofUInt32 bits
      match projectClosureCapture store.host.runtime.heap
          store.host.closureDispatch store.host.closureDescriptors object
          closureTarget 2 1 0 .uint64 with
      | .ok (.word64 captured) =>
          captured == 18446744073709551615 && store.host.failure?.isNone
      | _ => false
  | _ => false

-- The generated trampoline's concrete metadata test and typed projection
-- recover the just-allocated closure without consulting semantic handles.
#guard match partialApplyStep closureTarget 2 1 #[.uint64] .object closureStore
    [.i64 18446744073709551615] with
  | .Return [.i32 object] store =>
      match closureMatchesStep closureTarget 2 1 store [.i32 object],
          closureMatchesStep `FirTalos.Concrete.otherTarget 2 1 store
            [.i32 object],
          closureProjStep closureTarget 2 1 0 .uint64 store [.i32 object] with
      | .Return [.i32 matched] matchedStore,
          .Return [.i32 mismatch] mismatchedStore,
          .Return [.i64 captured] projectedStore =>
          matched == 1 && mismatch == 0 &&
            captured == 18446744073709551615 &&
            matchedStore.host.failure?.isNone &&
            mismatchedStore.host.failure?.isNone &&
            projectedStore.host.failure?.isNone
      | _, _, _ => false
  | _ => false

end FirTalos.Concrete
