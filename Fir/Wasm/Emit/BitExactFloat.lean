import Fir.Wasm.Validate

namespace Fir.Wasm.Emit.BitExactFloat

open Lean
open Fir.Wasm

/--
The integer physical lane used by the browser-safe entry facade. Non-floating
ABI kinds retain their existing physical representation.
-/
def transportKind : AbiKind → AbiKind
  | .float32 => .uint32
  | .float => .uint64
  | kind => kind

def requiresTransport (kind : AbiKind) : Bool :=
  kind == .float32 || kind == .float

/-- Stable low-level export name for the raw-bit entry facade. -/
def facadeName (entry : Name) : Name :=
  Name.str entry "_fir_bit_exact"

structure Descriptor where
  entry : Name
  params : Array AbiKind
  result : AbiKind
  deriving Inhabited, BEq, Repr

private def entryResultKind (entry : Name) (function : Function) : Except String AbiKind := do
  match function.results.toList with
  | [kind] => return kind
  | results =>
      throw s!"entry {entry} must return exactly one ABI value, got {results.length}"

private def parameterCode (parameter : FVarId × AbiKind) : List Instruction :=
  let (fvarId, kind) := parameter
  [.localGet fvarId] ++
    match kind with
    | .float32 => [.f32ReinterpretI32 .float32]
    | .float => [.f64ReinterpretI64 .float]
    | _ => []

private def resultCode : AbiKind → List Instruction
  | .float32 => [.i32ReinterpretF32 .uint32]
  | .float => [.i64ReinterpretF64 .uint64]
  | _ => []

private def expectedFacade (source : Function) : Except String Function := do
  let result ← entryResultKind source.name source
  return {
    name := facadeName source.name
    params := source.params.map fun (fvarId, kind) => (fvarId, transportKind kind)
    results := #[transportKind result]
    locals := #[]
    body := source.params.toList.flatMap parameterCode ++
      [.call (.declaration source.name)] ++ resultCode result ++ [.ret] }

private def sourceFunction (module : Module) (entry : Name) : Except String Function := do
  unless module.exports.contains entry do
    throw s!"entry {entry} is not exported"
  let some function := module.functions.toList.find? (·.name == entry) |
    throw s!"entry {entry} is not a lowered function"
  return function

private def hasNameCollision (module : Module) (name : Name) : Bool :=
  module.functions.any (·.name == name) ||
    module.imports.any (·.declaration? == some name) ||
    module.exports.contains name

/--
Install an integer-lane wrapper only when the selected source signature
contains an `f32` or `f64` parameter/result. Reinterpret instructions execute
inside Wasm, so JavaScript never coerces a signaling NaN through `number`.
-/
def install (module : Module) (entry : Name) : Except String Module := do
  let source ← sourceFunction module entry
  let result ← entryResultKind entry source
  unless source.params.any (requiresTransport ·.snd) || requiresTransport result do
    return module
  let facade ← expectedFacade source
  if hasNameCollision module facade.name then
    throw s!"bit-exact float facade name is already reserved: {facade.name}"
  let module := {
    module with
    functions := module.functions.push facade
    exports := module.exports.push facade.name }
  match Fir.Wasm.validateModule module with
  | .ok () => return module
  | .error error =>
      throw s!"bit-exact float facade failed symbolic validation: {repr error}"

/--
Recover and verify the generated facade. Manifest emission fails closed if the
export exists with a signature or body other than the canonical wrapper.
-/
def descriptor? (module : Module) (entry : Name) : Except String (Option Descriptor) := do
  let source ← sourceFunction module entry
  let result ← entryResultKind entry source
  unless source.params.any (requiresTransport ·.snd) || requiresTransport result do
    return none
  let expected ← expectedFacade source
  unless module.exports.contains expected.name do
    throw s!"bit-exact float facade {expected.name} is not exported"
  let some actual := module.functions.toList.find? (·.name == expected.name) |
    throw s!"bit-exact float facade {expected.name} is not a lowered function"
  unless actual == expected do
    throw s!"bit-exact float facade {expected.name} does not match its source signature"
  return some {
    entry := expected.name
    params := expected.params.map (·.snd)
    result := expected.results[0]! }

end Fir.Wasm.Emit.BitExactFloat
