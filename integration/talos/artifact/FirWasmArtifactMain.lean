import Fir.Wasm.Emit.Examples

open Fir.Wasm
open Fir.Wasm.Emit
open Fir.Wasm.Emit.Examples
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

def manifestJson (fixture : CorpusFixture) (module : Fir.Wasm.Module) : Except String Json := do
  let imports ← module.imports.toList.mapM importJson
  return Json.mkObj [
    ("fixture", fixture.name),
    ("entry", "main"),
    ("result", "tobject"),
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
  "usage: fir-wasm-artifact <literal|ctor-projection|case|default-case> <output.wasm>\n" ++
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
