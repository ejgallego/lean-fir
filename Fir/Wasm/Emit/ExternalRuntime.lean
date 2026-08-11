import Fir.Wasm.ABI

namespace Fir.Wasm.Emit.ExternalRuntime

open Lean

/--
Standard Lean 4.32 numeric externals supplied by the separately compiled
Wasm math runtime.  Source capture retains these declarations at the same
opaque boundary used by Lean's native compiler; package linking validates
their exact imported signatures before producing a zero-import module.
-/
def mathDeclarations : Array Name := #[
  `Float.ofNat,
  `Float.ofScientific,
  `UInt64.toFloat,
  `Float.add,
  `Float.sub,
  `Float.mul,
  `Float.div,
  `Float.neg,
  `Float.beq,
  `Float.decLt,
  `Float.decLe,
  `Float.abs,
  `Float.sqrt,
  `Float.sin,
  `Float.cos,
  `Float.acos,
  `Float.atan2,
  `Float.cbrt,
  `Float.floor]

end Fir.Wasm.Emit.ExternalRuntime
