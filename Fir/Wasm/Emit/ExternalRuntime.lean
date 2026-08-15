import Fir.Wasm.ABI

namespace Fir.Wasm.Emit.ExternalRuntime

open Lean

/-- Standard conversions whose exposed Lean bodies are compiled through final LCNF. -/
def sourceDeclarations : Array Name := #[
  `Float.ofNat,
  `Float.ofScientific]

/-- Externals whose semantics are exactly one core Wasm scalar operation. -/
def coreScalarDeclarations : Array Name := #[
  `UInt64.toFloat,
  `Float.ofModel,
  `Float.ofBits,
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

/-- Genuine libm externals supplied by the separately compiled runtime. -/
def compiledDeclarations : Array Name := #[
  `Float.sin,
  `Float.cos,
  `Float.acos,
  `Float.atan2,
  `Float.cbrt,
  `Float.log2]

/--
Standard numeric externals retained at the same opaque boundary used by Lean's
native compiler. `Float.ofNat` and `Float.ofScientific` are deliberately absent:
FIR compiles their real exposed Lean bodies. Resident linking first consumes
`coreScalarDeclarations`; the separately compiled math runtime then supplies
only `compiledDeclarations` before producing a zero-import module.
-/
def mathDeclarations : Array Name := #[
  `UInt64.toFloat,
  `Float.ofModel,
  `Float.ofBits,
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

/-- Complete standard Float inventory, including source-compiled conversions. -/
def allDeclarations : Array Name := sourceDeclarations ++ mathDeclarations

#guard mathDeclarations.contains `Float.log2
#guard sourceDeclarations.contains `Float.ofNat
#guard sourceDeclarations.contains `Float.ofScientific
#guard sourceDeclarations.all fun declaration =>
  !mathDeclarations.contains declaration
#guard coreScalarDeclarations.all fun declaration =>
  mathDeclarations.contains declaration && !compiledDeclarations.contains declaration
#guard compiledDeclarations.all fun declaration =>
  mathDeclarations.contains declaration && !coreScalarDeclarations.contains declaration
#guard mathDeclarations.all fun declaration =>
  coreScalarDeclarations.contains declaration || compiledDeclarations.contains declaration
#guard mathDeclarations.size ==
  coreScalarDeclarations.size + compiledDeclarations.size
#guard allDeclarations.size ==
  sourceDeclarations.size + coreScalarDeclarations.size + compiledDeclarations.size

end Fir.Wasm.Emit.ExternalRuntime
