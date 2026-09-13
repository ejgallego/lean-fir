import Probe
import Lean.Elab.Command

open Lean Elab Command

private def namesJson (names : Array Name) : Json :=
  Json.arr (names.map fun name => toJson name.toString)

private def importJson (item : Fir.Wasm.Import) : Json := Json.mkObj [
  ("module", item.moduleName), ("name", item.itemName),
  ("params", Fir.Wasm.Emit.Manifest.abiKindsJson item.signature.params),
  ("results", Fir.Wasm.Emit.Manifest.abiKindsJson item.signature.results)]

set_option maxHeartbeats 0 in
run_cmd do
  let out := "../../.deps/native-session-probe/output/"
  IO.FS.createDirAll out
  logInfo "NativeSession: capture begin"
  let (source, hosts) ← liftCoreM NativeSessionProbe.capture
  IO.FS.writeFile (out ++ "captured.lcnf") (← liftCoreM source.format)
  IO.FS.writeFile (out ++ "capture.json") <| (Json.mkObj [
    ("entries", namesJson NativeSessionProbe.entries),
    ("declarations", namesJson (source.program.decls.map (·.name))),
    ("externals", namesJson source.externalNames),
    ("hostDeclarations", namesJson hosts)]).pretty ++ "\n"
  logInfo m!"NativeSession: captured {source.program.decls.size} declarations, {hosts.size} VIR host imports"
  let base ← match ← liftCoreM <|
      Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source NativeSessionProbe.entries .ok with
    | .ok base => pure base
    | .error error => throwError "NativeSession lowering: {repr error}"
  match ← base.write (out ++ "native-session-base.wasm") with
  | .ok () => pure ()
  | .error error => throwError "NativeSession base encoding: {repr error}"
  logInfo "NativeSession: resident link begin"
  let linked ← match NativeSessionProbe.link base hosts with
    | .ok linked => pure linked
    | .error error => throwError "NativeSession resident link: {repr error}"
  match ← linked.write (out ++ "native-session.wasm") with
  | .ok () => pure ()
  | .error error => throwError "NativeSession encoding: {repr error}"
  IO.FS.writeFile (out ++ "linked.json") <| (Json.mkObj [
    ("exports", namesJson linked.module.exports),
    ("functions", namesJson (linked.module.functions.map (·.name))),
    ("imports", Json.arr (linked.module.imports.map importJson)),
    ("runtimeOperations", linked.module.runtimeOperations.size),
    ("bytes", linked.bytes.size)]).pretty ++ "\n"
  logInfo m!"NativeSession: emitted {linked.bytes.size} bytes; {linked.module.imports.size} remaining imports"
