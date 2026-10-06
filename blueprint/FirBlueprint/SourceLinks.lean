import VersoBlueprint.PreviewManifest

/-! Source links are assigned by the package option before rendering. This hook
only emits source snapshots; it does not change proof associations or statuses.
Snapshots are captured before rendering and checked again before emission. The
ordinary fresh Lake build remains responsible for imported-module freshness. -/

namespace FirBlueprint.SourceLinks

open Lean Informal Informal.PreviewManifest Verso.Genre.Manual

structure Reference where
  declaration : String
  firstLine : Nat
  lastLine : Nat
deriving ToJson

structure SourceFile where
  moduleName : String
  path : String
  text : String
  references : Array Reference := #[]
deriving ToJson

structure Snapshot where
  root : String
  revision : String
  workingTreeChanges : Bool
  files : Array SourceFile
deriving ToJson

/-- Capture only files referenced by the document's typed Lean associations. -/
def capture (model : RenderModel) : IO Snapshot := do
  let rootResult ← IO.Process.output { cmd := "git", args := #["rev-parse", "--show-toplevel"] }
  unless rootResult.exitCode == 0 do
    throw <| IO.userError "source snapshots require a FIR checkout"
  let root := rootResult.stdout.trimAscii.toString
  let revision ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  let status ← IO.Process.output { cmd := "git", args := #["status", "--porcelain"] }
  unless revision.exitCode == 0 && status.exitCode == 0 do
    throw <| IO.userError "unable to identify the documentation checkout"
  let mut files : Array SourceFile := #[]
  for node in model.nodes do
    for ref in node.externalRefs do
      unless ref.present do
        throw <| IO.userError s!"associated declaration is missing: {ref.canonical}"
      let some moduleName := ref.provenance.moduleName?
        | throw <| IO.userError s!"associated declaration has no source module: {ref.canonical}"
      let some path := ref.provenance.sourcePath?
        | throw <| IO.userError s!"associated declaration has no source path: {ref.canonical}"
      let some range := ref.range?
        | throw <| IO.userError s!"associated declaration has no source range: {ref.canonical}"
      let reference : Reference := {
        declaration := ref.canonical.toString
        firstLine := range.pos.line
        lastLine := range.endPos.line }
      let moduleName := moduleName.toString
      if let some previous := files.find? (·.moduleName == moduleName) then
        unless previous.path == path do
          throw <| IO.userError s!"ambiguous source module: {moduleName}"
        files := files.map fun file =>
          if file.moduleName == moduleName then
            { file with references := file.references.push reference }
          else file
      else
        files := files.push {
          moduleName, path, text := ← IO.FS.readFile path, references := #[reference] }
  return {
    root, revision := revision.stdout.trimAscii.toString,
    workingTreeChanges := !status.stdout.isEmpty, files }

/-- Emit after native pages and preview exports, through the public VBP hook. -/
def Snapshot.emit (snapshot : Snapshot) : BlueprintExtraStep := fun prepared => do
  let modeDir := match prepared.mode with
    | .single => "html-single"
    | .multi => "html-multi"
  let output := prepared.config.destination / modeDir
  let result ← IO.Process.output {
    cmd := "python3"
    args := #[(System.FilePath.mk snapshot.root / "blueprint" / "source-links.py").toString,
      "--output", output.toString] }
    (some (toJson snapshot).compress)
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source snapshot emission failed: {result.stderr.trimAscii}"

end FirBlueprint.SourceLinks
