import Fir.Wasm.Emit.Examples
import Fir.Wasm.Emit.Manifest

open Fir.Wasm
open Fir.Wasm.Emit
open Fir.Wasm.Emit.Examples
open Fir.LeanIR.Impure
open Lean

def fixtures : List CorpusFixture := initialFixtures

def findFixture? (name : String) : Option CorpusFixture :=
  fixtures.find? (·.name == name)

def manifestJson (fixture : CorpusFixture) (module : Fir.Wasm.Module) : Except String Json := do
  Fir.Wasm.Emit.Manifest.artifactJson fixture.name `main `main module fixture.args

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
