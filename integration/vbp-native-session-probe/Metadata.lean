import Probe
import Lean.Elab.Command

open Lean Elab Command
open Lean.Compiler.LCNF

private def exprQuery (action : CoreM Expr) : CoreM Json := withoutModifyingEnv do
  try
    return Json.mkObj [("ok", true), ("value", toString (← action))]
  catch error =>
    return Json.mkObj [("ok", false), ("error", ← error.toMessageData.toString)]

private def layoutQuery (name : Name) : CoreM Json := withoutModifyingEnv do
  try
    let layout ← getCtorLayout name
    return Json.mkObj [("ok", true), ("tag", layout.ctorInfo.cidx),
      ("objects", layout.ctorInfo.size), ("usize", layout.ctorInfo.usize),
      ("scalarBytes", layout.ctorInfo.ssize)]
  catch error =>
    return Json.mkObj [("ok", false), ("error", ← error.toMessageData.toString)]

private def snapshot : CoreM Json := do
  let env ← getEnv
  let rows ← #[`Int, `Int.ofNat].mapM fun name => do
    let moduleName := env.getModuleIdxFor? name |>.map fun idx =>
      env.header.moduleNames[idx]!.toString
    let impure ← if name == `Int then exprQuery (nameToImpureType name) else pure Json.null
    let layout ← if name == `Int.ofNat then layoutQuery name else pure Json.null
    return Json.mkObj [
      ("name", name.toString), ("module", toJson moduleName),
      ("constantPresent", (env.find? name).isSome),
      ("nativeIRPresent", (Lean.IR.findEnvDecl env name).isSome),
      ("getOtherDeclBaseType", ← exprQuery (getOtherDeclBaseType name [])),
      ("getOtherDeclMonoType", ← exprQuery (getOtherDeclMonoType name)),
      ("nameToImpureType", impure), ("getCtorLayout", layout)]
  return Json.arr rows

private def diagnose : CoreM Unit := do
  let out := "../../.deps/native-session-probe/metadata/"
  IO.FS.createDirAll out
  let initial ← snapshot
  IO.FS.writeFile (out ++ "imported.json") (initial.pretty ++ "\n")
  IO.println s!"Imported metadata: {initial.compress}"
  let (artifact, _) ← NativeSessionProbe.captureBeforeFinal
  let beforeFinal ← snapshot
  let result := Json.mkObj [
    ("imported", initial), ("beforeFinalDependencies", beforeFinal),
    ("preFinalDeclarations", Json.arr (artifact.program.decls.map fun d => toJson d.name.toString)),
    ("preFinalExternals", Json.arr (artifact.externalNames.map fun n => toJson n.toString))]
  IO.FS.writeFile (out ++ "comparison.json") (result.pretty ++ "\n")
  IO.println s!"Before final dependencies: {beforeFinal.compress}"
  IO.println s!"Pre-final artifact: {artifact.program.decls.size} declarations, {artifact.externalNames.size} externals (not a completed closure)"

set_option maxHeartbeats 0 in
set_option compiler.postponeCompile false in
run_cmd do
  if (← IO.getEnv "FIR_RENDERER_METADATA") == some "1" then
    liftCoreM diagnose
