import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

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

end FirTalos.Concrete
