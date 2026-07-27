import Fir.Wasm.Emit.Examples
import Fir.Wasm.Emit.Manifest
import Fir.Wasm.Emit.ResidentAllocator
import Fir.Wasm.Emit.ResidentConstructor
import Fir.Wasm.Emit.ResidentLiteral
import Fir.Wasm.Emit.ResidentRuntime

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

def emitResidentGetTag (path : System.FilePath) : IO Unit := do
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode
    Fir.Wasm.Emit.ResidentRuntime.getTagModule).mapError fun error =>
      s!"resident getTag encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath
    Fir.Wasm.Emit.ResidentRuntime.getTagManifest.compress
  IO.println s!"resident-get-tag: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentGlobal (path : System.FilePath) : IO Unit := do
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode
    Fir.Wasm.Emit.Examples.residentGlobalSurfaceModule).mapError fun error =>
      s!"resident global encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  IO.println s!"resident-global: wrote {bytes.size} bytes to {path}"

def emitResidentMemorySurface (path : System.FilePath) : IO Unit := do
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode
    Fir.Wasm.Emit.Examples.residentMemorySurfaceModule).mapError fun error =>
      s!"resident memory-surface encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  IO.println s!"resident-memory-surface: wrote {bytes.size} bytes to {path}"

def emitResidentAllocator (path : System.FilePath) : IO Unit := do
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode
    Fir.Wasm.Emit.ResidentAllocator.allocatorModule).mapError fun error =>
      s!"resident allocator encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath
    Fir.Wasm.Emit.ResidentAllocator.manifest.compress
  IO.println s!"resident-allocator: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentConstructors (path : System.FilePath) : IO Unit := do
  let module ← IO.ofExcept <|
    Fir.Wasm.Emit.ResidentConstructor.residentExampleModule
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode module).mapError fun error =>
    s!"resident constructor encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath <|
    Fir.Wasm.Emit.ResidentConstructor.manifest
      Fir.Wasm.Emit.ResidentConstructor.exampleOperations |>.compress
  IO.println
    s!"resident-constructors: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentLiterals (path : System.FilePath) : IO Unit := do
  let module ← IO.ofExcept <|
    Fir.Wasm.Emit.ResidentLiteral.residentExampleModule
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode module).mapError fun error =>
    s!"resident literal encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath <|
    Fir.Wasm.Emit.ResidentLiteral.manifest.compress
  IO.println
    s!"resident-literals: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentIsShared (path : System.FilePath) : IO Unit := do
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode
    Fir.Wasm.Emit.ResidentRuntime.isSharedModule).mapError fun error =>
      s!"resident isShared encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath
    Fir.Wasm.Emit.ResidentRuntime.isSharedManifest.compress
  IO.println s!"resident-is-shared: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentReadProjections (path : System.FilePath) : IO Unit := do
  let module ← IO.ofExcept <|
    Fir.Wasm.Emit.ResidentRuntime.prettyFormatReadProjectionModule.mapError fun error =>
      s!"resident read-projection linking failed: {repr error}"
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode module).mapError fun error =>
    s!"resident read-projection encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath
    Fir.Wasm.Emit.ResidentRuntime.prettyFormatReadProjectionManifest.compress
  IO.println s!"resident-read-projections: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentClosureProjections (path : System.FilePath) : IO Unit := do
  let module ← IO.ofExcept <|
    Fir.Wasm.Emit.ResidentRuntime.prettyFormatClosureProjectionModule.mapError fun error =>
      s!"resident closure-projection linking failed: {repr error}"
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode module).mapError fun error =>
    s!"resident closure-projection encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath
    Fir.Wasm.Emit.ResidentRuntime.prettyFormatClosureProjectionManifest.compress
  IO.println s!"resident-closure-projections: wrote {bytes.size} bytes to {path} and {manifestPath}"

def emitResidentClosureMatches (path : System.FilePath) : IO Unit := do
  let module ← IO.ofExcept <|
    Fir.Wasm.Emit.ResidentRuntime.closureMatchExampleModule.mapError fun error =>
      s!"resident closure-match linking failed: {repr error}"
  let bytes ← IO.ofExcept <| (Fir.Wasm.Emit.encode module).mapError fun error =>
    s!"resident closure-match encoding failed: {repr error}"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  let manifestPath : System.FilePath := path.toString ++ ".json"
  IO.FS.writeFile manifestPath
    Fir.Wasm.Emit.ResidentRuntime.closureMatchExampleManifest.compress
  IO.println s!"resident-closure-matches: wrote {bytes.size} bytes to {path} and {manifestPath}"

def usage : String :=
  let names := String.intercalate "|" (fixtures.map (·.name))
  s!"usage: fir-wasm-artifact <{names}> <output.wasm>\n" ++
    "       fir-wasm-artifact resident-get-tag <output.wasm>\n" ++
    "       fir-wasm-artifact resident-global <output.wasm>\n" ++
    "       fir-wasm-artifact resident-memory-surface <output.wasm>\n" ++
    "       fir-wasm-artifact resident-allocator <output.wasm>\n" ++
    "       fir-wasm-artifact resident-constructors <output.wasm>\n" ++
    "       fir-wasm-artifact resident-literals <output.wasm>\n" ++
    "       fir-wasm-artifact resident-is-shared <output.wasm>\n" ++
    "       fir-wasm-artifact resident-read-projections <output.wasm>\n" ++
    "       fir-wasm-artifact resident-closure-projections <output.wasm>\n" ++
    "       fir-wasm-artifact resident-closure-matches <output.wasm>\n" ++
    "       fir-wasm-artifact all <output-directory>"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["all", outputDirectory] =>
        let outputDirectory : System.FilePath := outputDirectory
        for fixture in fixtures do
          emitFixture fixture (outputDirectory / s!"{fixture.name}.wasm")
        return 0
    | ["resident-get-tag", output] =>
        emitResidentGetTag output
        return 0
    | ["resident-global", output] =>
        emitResidentGlobal output
        return 0
    | ["resident-memory-surface", output] =>
        emitResidentMemorySurface output
        return 0
    | ["resident-allocator", output] =>
        emitResidentAllocator output
        return 0
    | ["resident-constructors", output] =>
        emitResidentConstructors output
        return 0
    | ["resident-literals", output] =>
        emitResidentLiterals output
        return 0
    | ["resident-is-shared", output] =>
        emitResidentIsShared output
        return 0
    | ["resident-read-projections", output] =>
        emitResidentReadProjections output
        return 0
    | ["resident-closure-projections", output] =>
        emitResidentClosureProjections output
        return 0
    | ["resident-closure-matches", output] =>
        emitResidentClosureMatches output
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
