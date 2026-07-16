import Fir.Wasm.Emit.Examples

open Fir.Wasm
open Fir.Wasm.Emit
open Fir.Wasm.Emit.Examples
open Fir.LeanIR.Impure
open Lean

def fixtures : List CorpusFixture := initialFixtures

def findFixture? (name : String) : Option CorpusFixture :=
  fixtures.find? (·.name == name)

def abiKindName : AbiKind → String
  | .object => "object"
  | .tagged => "tagged"
  | .tobject => "tobject"
  | .erased => "erased"
  | .reuseToken => "reuseToken"
  | .uint8 => "uint8"
  | .uint16 => "uint16"
  | .uint32 => "uint32"
  | .uint64 => "uint64"
  | .usize => "usize"
  | .float32 => "float32"
  | .float => "float"

def operationJson : RuntimeOp → Except String Json
  | .literal (.nat value) result =>
      return Json.mkObj [
        ("kind", "naturalLiteral"),
        ("value", s!"{value}"),
        ("result", abiKindName result)]
  | .literal (.str value) result =>
      return Json.mkObj [
        ("kind", "stringLiteral"),
        ("value", value),
        ("result", abiKindName result)]
  | .allocCtor info fields result =>
      return Json.mkObj [
        ("kind", "allocCtor"),
        ("name", info.name.toString),
        ("tag", s!"{info.cidx}"),
        ("size", info.size),
        ("usize", info.usize),
        ("ssize", info.ssize),
        ("fields", Json.arr (fields.map fun kind => abiKindName kind)),
        ("result", abiKindName result)]
  | .objectProj index result =>
      return Json.mkObj [
        ("kind", "objectProj"),
        ("index", index),
        ("result", abiKindName result)]
  | .getTag => return Json.mkObj [("kind", "getTag")]
  | operation => throw s!"unsupported A0 host operation: {operation.stem}"

def importJson (import_ : Fir.Wasm.Import) : Except String Json := do
  let some operation := import_.operation? |
    throw s!"external import is outside A0: {import_.moduleName}.{import_.itemName}"
  return Json.mkObj [
    ("module", import_.moduleName),
    ("name", import_.itemName),
    ("operation", ← operationJson operation)]

def argumentJson (kind : AbiKind) (value : Value) : Except String Json := do
  unless kind.acceptsValue value do
    throw s!"argument {repr value} does not match ABI kind {repr kind}"
  match value with
  | .object (.tagged payload) =>
      return Json.mkObj [("kind", "tagged"), ("payload", s!"{payload}")]
  | .object (.heap _) => throw "heap-backed arguments require an explicit initial runtime"
  | .usize value => return Json.mkObj [("kind", "usize"), ("value", s!"{value}")]
  | .scalar (.uint8 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint8"), ("value", s!"{value}")]
  | .scalar (.uint16 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint16"), ("value", s!"{value}")]
  | .scalar (.uint32 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint32"), ("value", s!"{value}")]
  | .scalar (.uint64 value) =>
      return Json.mkObj [("kind", "scalar"), ("scalarKind", "uint64"), ("value", s!"{value}")]
  | .erased => return Json.mkObj [("kind", "erased")]
  | .reuseToken none =>
      return Json.mkObj [("kind", "reuseToken"), ("location", Json.null)]
  | .reuseToken (some _) => throw "heap-backed arguments require an explicit initial runtime"

def entryFunction (module : Fir.Wasm.Module) (entry : Name) : Except String Fir.Wasm.Function := do
  unless module.exports.contains entry do
    throw s!"entry {entry} is not exported"
  let some function := module.functions.toList.find? (·.name == entry) |
    throw s!"entry {entry} is not a lowered function"
  return function

def entryResultKind (entry : Name) (function : Fir.Wasm.Function) : Except String AbiKind := do
  match function.results.toList with
  | [kind] => pure kind
  | results => throw s!"entry {entry} must return exactly one ABI value, got {results.length}"

def manifestJson (fixture : CorpusFixture) (module : Fir.Wasm.Module) : Except String Json := do
  let entry := `main
  let function ← entryFunction module entry
  let result ← entryResultKind entry function
  let params := function.params.map (·.snd)
  unless params.size == fixture.args.size do
    throw s!"entry {entry} expects {params.size} arguments, got {fixture.args.size}"
  let arguments ← (params.toList.zip fixture.args.toList).mapM fun (kind, value) =>
    argumentJson kind value
  let imports ← module.imports.toList.mapM importJson
  return Json.mkObj [
    ("fixture", fixture.name),
    ("entry", entry.toString),
    ("result", abiKindName result),
    ("params", Json.arr (params.map fun kind => (abiKindName kind : Json))),
    ("arguments", Json.arr arguments.toArray),
    ("imports", Json.arr imports.toArray)]

def prepareFixture (fixture : CorpusFixture) : Except String (ByteArray × String) := do
  let module ←
    match lowerSupported fixture.program with
    | .ok module => pure module
    | .error error => throw s!"lowering failed for {fixture.name}: {repr error}"
  let bytes ←
    match encode module with
    | .ok bytes => pure bytes
    | .error error => throw s!"encoding failed for {fixture.name}: {repr error}"
  return (bytes, (← manifestJson fixture module).compress)

def emitFixture (fixture : CorpusFixture) (path : System.FilePath) : IO Unit := do
  let (bytes, manifest) ← IO.ofExcept (prepareFixture fixture)
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath manifest
  IO.println s!"{fixture.name}: wrote {bytes.size} bytes to {path} and {manifestPath}"

def usage : String :=
  let names := String.intercalate "|" (fixtures.map (·.name))
  s!"usage: fir-wasm-artifact <{names}> <output.wasm>\n" ++
    "       fir-wasm-artifact all <output-directory>"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["all", outputDirectory] =>
        let outputDirectory : System.FilePath := outputDirectory
        for fixture in fixtures do
          emitFixture fixture (outputDirectory / s!"{fixture.name}.wasm")
        return 0
    | [name, output] =>
        let some fixture := findFixture? name | throw (IO.userError s!"unknown fixture: {name}")
        emitFixture fixture output
        return 0
    | _ =>
        IO.eprintln usage
        return 2
  catch error =>
    IO.eprintln error.toString
    return 1
