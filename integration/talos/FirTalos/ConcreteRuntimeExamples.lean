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

end FirTalos.Concrete
