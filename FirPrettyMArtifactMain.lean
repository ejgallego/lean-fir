import Fir.Wasm.Emit.ResidentPrettyFormat
import Lean.Elab.Frontend

open Lean

namespace Fir.PrettyMArtifact

private unsafe def compileArtifact (sourcePath : System.FilePath) (moduleName entry : Name) :
    IO Fir.Wasm.Emit.Source.ModuleArtifact := do
  let started ← IO.monoMsNow
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let input ← IO.FS.readFile sourcePath
  let options := maxHeartbeats.set ({} : Options) 0
  let some env ← Lean.Elab.runFrontend input options sourcePath.toString moduleName
    | throw <| IO.userError s!"failed to elaborate {sourcePath}"
  let elaborated ← IO.monoMsNow
  let (result, _) ← Lean.Core.CoreM.toIO
    (ctx := { fileName := sourcePath.toString, fileMap := default, options })
    (s := { env }) <|
    Fir.Wasm.Emit.ResidentPrettyFormat.compileModule entry
  let artifact ← IO.ofExcept <| result.mapError fun error => s!"{repr error}"
  let compiled ← IO.monoMsNow
  IO.println s!"prettyM phases: frontend={elaborated - started}ms compile={compiled - elaborated}ms"
  return artifact

private def usage : String :=
  "usage: fir-prettyM-artifact [--instruction-origins <origins.json>] " ++
  "<fixture.lean> <output.wasm>\n" ++
  "   or: fir-prettyM-artifact [--instruction-origins <origins.json>] " ++
  "<fixture.lean> <module> <entry> <output.wasm>"

unsafe def run (args : List String) : IO UInt32 := do
  try
    let (originOutput?, positional) : Option System.FilePath × List String :=
      match args with
      | "--instruction-origins" :: originOutput :: rest =>
          (some originOutput, rest)
      | _ => (none, args)
    let (source, moduleName, entry, output) ← match positional with
      | [source, output] =>
          pure (source, `FirWasmPrettyTraceExample,
            `Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw, output)
      | [source, moduleName, entry, output] =>
          pure (source, moduleName.toName, entry.toName, output)
      | _ => do
          IO.eprintln usage
          return 2
    let artifact ← compileArtifact source moduleName entry
    IO.ofExcept <| (← artifact.write output).mapError fun error => s!"{repr error}"
    if let some originOutput := originOutput? then
      let originsStarted ← IO.monoMsNow
      IO.ofExcept <| (← artifact.writeInstructionOrigins originOutput).mapError
        fun error => s!"{repr error}"
      let originsFinished ← IO.monoMsNow
      IO.println <| s!"prettyM: wrote instruction origins to {originOutput} " ++
        s!"in {originsFinished - originsStarted}ms"
    IO.println s!"prettyM: wrote {artifact.bytes.size} bytes to {output}"
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1

end Fir.PrettyMArtifact

unsafe def main (args : List String) : IO UInt32 :=
  Fir.PrettyMArtifact.run args
