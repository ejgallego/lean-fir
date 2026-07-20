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

end FirTalos.Concrete
