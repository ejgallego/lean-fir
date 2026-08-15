import Fir.Wasm.ABI

namespace Fir.Wasm.Emit.ExternalRuntime

open Lean

/-- Externals whose semantics are exactly one core Wasm scalar operation. -/
def coreScalarDeclarations : Array Name := #[
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
  `Float.floor]

/-- Externals that still require decimal/Natural logic or libm. -/
def compiledDeclarations : Array Name := #[
  `Float.ofNat,
  `Float.ofScientific,
  `Float.sin,
  `Float.cos,
  `Float.acos,
  `Float.atan2,
  `Float.cbrt,
  `Float.log2]

/--
Standard numeric externals retained at the same opaque boundary used by Lean's
native compiler. Resident linking first consumes `coreScalarDeclarations`; the
separately compiled math runtime then supplies only `compiledDeclarations`
before producing a zero-import module.
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
  `Float.log2,
  `Float.floor]

#guard mathDeclarations.contains `Float.log2
#guard coreScalarDeclarations.all fun declaration =>
  mathDeclarations.contains declaration && !compiledDeclarations.contains declaration
#guard compiledDeclarations.all fun declaration =>
  mathDeclarations.contains declaration && !coreScalarDeclarations.contains declaration
#guard mathDeclarations.all fun declaration =>
  coreScalarDeclarations.contains declaration || compiledDeclarations.contains declaration
#guard mathDeclarations.size ==
  coreScalarDeclarations.size + compiledDeclarations.size

end Fir.Wasm.Emit.ExternalRuntime
