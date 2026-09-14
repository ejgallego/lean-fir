import Probe
import Lean.Elab.Command

open Lean Elab Command

private def namesJson (names : Array Name) : Json :=
  Json.arr (names.map fun name => toJson name.toString)

private def captureOnly : CoreM Unit := do
  let out := "../../.deps/native-session-probe/capture/"
  IO.FS.createDirAll out
  IO.println "Renderer: ordinary-source capture begin"
  let (source, hosts) ← NativeSessionProbe.capture
  IO.FS.writeFile (out ++ "captured.lcnf") (← source.format)
  let hostRows ← hosts.mapM fun name => do
    let some decl := source.program.decls.find? (·.name == name) |
      throwError "captured host declaration missing: {name}"
    let params := decl.params.map fun param => Json.mkObj [
      ("name", param.binderName.toString),
      ("lcnfType", toString param.type),
      ("leanBorrow", param.borrow)]
    return Json.mkObj [
      ("name", name.toString),
      ("target", toJson (NativeSessionProbe.hostTarget? (← getEnv) name)),
      ("params", Json.arr params),
      ("resultLcnfType", toString decl.type)]
  IO.FS.writeFile (out ++ "capture.json") <| (Json.mkObj [
    ("entries", namesJson NativeSessionProbe.entries),
    ("declarations", namesJson (source.program.decls.map (·.name))),
    ("externals", namesJson source.externalNames),
    ("hosts", Json.arr hostRows),
    ("bindingProfile", "fir.wasm-host-binding/render-core/v0"),
    ("profileVerdict", "unreviewed"),
    ("postponeCompile", (← getOptions).getBool `compiler.postponeCompile true)]).pretty ++ "\n"
  IO.println s!"Renderer: captured {source.program.decls.size} declarations, {source.externalNames.size} externals, {hosts.size} VIR hosts"

-- Validate the driver in Beam without executing capture or writing evidence.
-- The batch command explicitly opts into the sole side-effecting action.
set_option maxHeartbeats 0 in
set_option compiler.postponeCompile false in
run_cmd do
  if (← IO.getEnv "FIR_RENDERER_CAPTURE") == some "1" then
    liftCoreM captureOnly
