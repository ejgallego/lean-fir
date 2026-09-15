import Fir.Wasm.Emit.ResidentLinker
import Fir.Wasm.Emit.ModuleSource
import Fir.Wasm.Emit.NativeSymbol
import Vir.HostMetadata

open Lean Fir.Wasm.Emit

private def importJson (i : Fir.Wasm.Import) : Json :=
  match Manifest.importJson i with
  | .ok row => row
  | .error error => Json.mkObj [("manifestError", toJson error)]

private def exportedProviderRows (env : Environment) (imports : Array Fir.Wasm.Import) :
    CoreM (Array Json) := do
  let exports := env.constants.toList.toArray.filterMap fun (name, _) =>
    (getExportNameFor? env name).map fun symbol => (symbol.toString, name)
  let mut rows := #[]
  for i in imports do
    let some declaration := i.declaration? | continue
    let some symbol := getExternNameFor env `c declaration | continue
    for (_, provider) in exports.filter (·.1 == symbol) do
      let before ← Lean.Compiler.LCNF.getImpureSignature? declaration
      let after ← Lean.Compiler.LCNF.getImpureSignature? provider
      let signatures := match before, after with
        | some a, some b => Json.mkObj [
          ("type", toJson (a.type == b.type)), ("safe", toJson (a.safe == b.safe)),
          ("levels", toJson (a.levelParams == b.levelParams)),
          ("params", toJson (a.params.map (fun p => (p.type, p.borrow)) ==
            b.params.map (fun p => (p.type, p.borrow))))]
        | _, _ => Json.mkObj [("missingSignature", toJson true)]
      rows := rows.push <| Json.mkObj [
        ("declaration", toJson declaration.toString), ("symbol", toJson symbol),
        ("provider", toJson provider.toString), ("signatures", signatures)]
  return rows

/-- The launcher verifies this local same-toolchain Artifact before decoding.
No source reconstruction: the only new capture supplies the actual renderer
frontend context used by the normal FIR lowerer. -/
def main (args : List String) : IO Unit := do
  let [source, setupFile, productFile, metadataFile, out] := args |
    throw <| IO.userError "usage: LowerModuleProduct source setup product metadata out"
  unsafe enableInitializersExecution
  let captured ← ModuleSource.compile source (← ModuleSetup.load setupFile)
  let .ok c := captured | throw <| IO.userError "renderer context capture failed"
  let (a, _region) ← unsafe CompactedRegion.read (α := Fir.Compiler.Lcnf.Artifact) productFile #[]
  let original ← c.artifact a.entry
  for d in original.program.decls do
    if let .extern _ := d.value then continue
    unless a.program.decls.any (· == d) do
      throw <| IO.userError s!"closed artifact changed renderer body: {d.name}"
  let metadata ← IO.ofExcept <| Json.parse (← IO.FS.readFile metadataFile)
  let links : Array Json ← IO.ofExcept <| metadata.getObjValAs? (Array Json) "nativeLinks"
  let exports := NativeSymbol.exportIndex c.environment
  let mut providers := #[]
  for row in links do
    let name : String ← IO.ofExcept <| row.getObjValAs? String "declaration"
    let some decl := a.program.decls.find? (·.name == name.toName) |
      throw <| IO.userError s!"native-link declaration missing: {name}"
    let some p ← (NativeSymbol.resolve exports decl).toIO'
        { fileName := source, fileMap := default, options := c.options } { env := c.environment } |
      throw <| IO.userError s!"native-link metadata no longer resolves: {name}"
    for (field, expected) in [("provider", p.name.toString), ("symbol", p.symbol),
        ("owner", p.owner.toString)] do
      let actual : String ← IO.ofExcept <| row.getObjValAs? String field
      unless actual == expected do throw <| IO.userError s!"native-link {field} changed: {name}"
    let some body := a.program.decls.find? (·.name == p.name) |
      throw <| IO.userError s!"native provider body missing: {p.name}"
    IO.ofExcept <| NativeSymbol.checkBody p p.owner body
    providers := providers.push p
  let frontier : Array Json ← IO.ofExcept <| metadata.getObjValAs? (Array Json) "frontier"
  let mut hosts := #[]
  let mut hostRows := #[]
  for row in frontier do
    let targets : Array String ← IO.ofExcept <| row.getObjValAs? (Array String) "virTargets"
    if !targets.isEmpty then
      let name : String ← IO.ofExcept <| row.getObjValAs? String "name"
      hosts := hosts.push name.toName
      let some decl := a.program.decls.find? (·.name == name.toName) |
        throw <| IO.userError s!"host signature missing: {name}"
      let some symbol := getExternNameFor c.environment `c decl.name |
        throw <| IO.userError s!"host extern metadata missing: {name}"
      let some host := Vir.HostMetadata.decodeExternSymbol? symbol |
        throw <| IO.userError s!"host extern metadata not recognized by VIR: {name}"
      unless targets == #[host.target] do
        throw <| IO.userError s!"host target provenance mismatch: {name}"
      let imported ← IO.ofExcept <| (Fir.Wasm.externalImport decl).mapError reprStr
      hostRows := hostRows.push <| Json.mkObj [
        ("declaration", toJson name), ("target", toJson host.target),
        ("marker", toJson host.marker.attributeName.toString),
        ("borrowedParameters", toJson (decl.params.map (·.borrow))),
        ("physicalImport", importJson imported)]
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/host-boundary.json") <| (Json.mkObj [
    ("schema", "fir.vir-host-boundary-audit/v1"),
    ("admitted", toJson false), ("executed", toJson false),
    ("imports", toJson hostRows)]).pretty
  let result ← (Source.compileModuleArtifactWithExports a #[a.entry]
    (fun m => (NativeSymbol.link providers m).mapError Source.CompileError.manifest)).toIO'
    { fileName := source, fileMap := default, options := c.options } { env := c.environment }
  match result with
  | .error error =>
    IO.FS.writeFile (out ++ "/result.json") <| (Json.mkObj [
      ("stage", "lowering"), ("success", toJson false), ("error", toJson (reprStr error))]).pretty
    IO.println s!"LOWERING STOP: {repr error}"
  | .ok base =>
    IO.ofExcept ((← base.write (out ++ "/renderer-base.wasm")).mapError reprStr)
    match ResidentLinker.linkArtifact {
        ResidentLinker.closedApplicationAvailablePolicy base.module #[a.entry] with
        allowedExternalImports := some hosts
        requireZeroImports := false } base with
    | .error error =>
      -- Inspection only: retain the failed admission verdict and never publish
      -- this open diagnostic module as an accepted artifact or host fallback.
      let inspection := ResidentLinker.linkModule {
        ResidentLinker.closedApplicationAvailablePolicy base.module #[a.entry] with
        allowedExternalImports := none
        requireZeroImports := false
        requireNoRuntimeOperations := false } base.module
      let frontier ← match inspection with
        | .ok module => do
          let remainingProviders ← (exportedProviderRows c.environment module.imports).toIO'
            { fileName := source, fileMap := default, options := c.options } { env := c.environment }
          pure <| Json.mkObj [("imports", toJson (module.imports.map importJson)),
            ("leanExportProviders", toJson remainingProviders)]
        | .error err => pure <| Json.mkObj [("inspectionError", toJson (reprStr err))]
      IO.FS.writeFile (out ++ "/result.json") <| (Json.mkObj [
        ("stage", "resident-link"), ("success", toJson false), ("error", toJson (reprStr error)),
        ("diagnosticFrontier", frontier),
        ("baseBytes", toJson base.bytes.size)]).pretty
      IO.println s!"LINK STOP: {repr error}"
    | .ok linked =>
      IO.ofExcept ((← linked.write (out ++ "/renderer.wasm")).mapError reprStr)
      IO.FS.writeFile (out ++ "/result.json") <| (Json.mkObj [
        ("stage", "resident-link"), ("success", toJson true), ("bytes", toJson linked.bytes.size),
        ("imports", toJson (linked.module.imports.map fun i => Json.mkObj [
          ("module", toJson i.moduleName), ("name", toJson i.itemName),
          ("params", Manifest.abiKindsJson i.signature.params),
          ("results", Manifest.abiKindsJson i.signature.results)])),
        ("exports", toJson (linked.module.exports.map (·.toString)))]).pretty
      IO.println s!"LINKED: {linked.bytes.size} bytes, {linked.module.imports.size} imports"
