import Fir.Wasm.Emit.ModuleSource

open Lean Lean.Compiler.LCNF Fir.Wasm.Emit.ModuleSource

/-! Bounded provider for verified bootstrap-derived inputs, not release setup
recovery. The JS driver verifies pinned source/configuration and file digests;
this frontend verifies current Lean identity, source/artifact imports, module
ownership paths, and the derived options before calling the unchanged provider.
No Lake setup JSON, target self-import, or independent generated-name rebuild. -/

namespace InstalledInputs

def get [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

def verify (inputs row : Json) : IO (System.FilePath × ModuleSetup) := do
  unless (← get inputs "revision" : String) == Lean.githash do
    throw <| IO.userError "installed capture revision mismatch"
  unless (← get inputs "kind" : String) == "pinned-bootstrap-derived-capture-inputs/v1" do
    throw <| IO.userError "not derived capture inputs"
  let name := (← get row "name" : String).toName
  let sysroot : System.FilePath := ← get inputs "prefix"
  unless (← IO.FS.realPath sysroot) == (← IO.FS.realPath (← Lean.getBuildDir)) do
    throw <| IO.userError "installed capture toolchain prefix mismatch"
  let dependencies : Array Json := ← get inputs "dependencies"
  for dep in dependencies do
    let depName := (← get dep "name" : String).toName
    let expected := sysroot / "lib/lean" / (depName.toString.replace "." "/" ++ ".olean")
    unless (← IO.FS.realPath (← Lean.findOLean depName)) == (← IO.FS.realPath expected) do
      throw <| IO.userError s!"installed dependency shadowed: {depName}"
  let relative := name.toString.replace "." "/"
  let source : System.FilePath := ← get row "source"
  unless (← IO.FS.realPath source) == (← IO.FS.realPath (sysroot / "src/lean" / (relative ++ ".lean"))) do
    throw <| IO.userError "installed source/module mismatch"
  let ctx := Parser.mkInputContext (← IO.FS.readFile source) source.toString
  let (header, _, messages) ← Parser.parseHeader ctx
  unless !messages.hasErrors && Elab.HeaderSyntax.isModule header do
    throw <| IO.userError "installed source module header rejected"
  let olean := sysroot / "lib/lean" / (relative ++ ".olean")
  unless (← IO.FS.realPath (← Lean.findOLean name)) == (← IO.FS.realPath olean) do
    throw <| IO.userError "installed module shadowed on Lean search path"
  let (data, _region) ← Lean.readModuleData olean
  let imports := Elab.HeaderSyntax.imports header
  unless data.isModule && data.imports == imports do
    throw <| IO.userError "installed source/artifact import mismatch"
  unless (← get row "imports" : Array Import) == imports do
    throw <| IO.userError "recorded import provenance mismatch"
  let options : LeanOptions := ← get inputs "options"
  let expected := LeanOptions.ofArray #[
    ⟨`interpreter.prefer_native, false⟩, ⟨`pp.rawOnError, true⟩, ⟨`linter.coreInternal, true⟩]
  unless (toJson options).compress == (toJson expected).compress do
    throw <| IO.userError "unreviewed bootstrap capture options"
  -- The bootstrap package has no native symbol prefix. Original source headers
  -- and ordinary installed-artifact resolution remain authoritative.
  return (source, { name, isModule := true, options })

end InstalledInputs
