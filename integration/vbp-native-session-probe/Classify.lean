import Fir.Wasm.Emit.Source
import Lean.Elab.Command

open Lean Elab Command

-- Read ordinary module products without rebuilding or capturing the renderer.
run_cmd do
  let moduleName := `VersoBlueprintVir.Preview.Renderer
  let entry := `VersoBlueprint.Experimental.VirPreview.Renderer.render
  let env ← importModules #[{ module := moduleName, importAll := true, isMeta := true }]
    (← getOptions) (loadExts := false)
  let result ← liftCoreM <| withoutModifyingEnv do
    setEnv env
    let some idx := env.getModuleIdxFor? entry | throwError "renderer entry has no module"
    let signature ← Compiler.LCNF.getImpureSignature? entry
    let groups := Compiler.LCNF.postponedCompileDeclsExt.getModuleEntries env idx
    let sourceConst := env.header.moduleData[idx]!.constNames.contains entry
    let nativeDecl := Lean.IR.findEnvDecl env entry
    return Json.mkObj [
      ("entry", entry.toString),
      ("module", env.header.moduleNames[idx]!.toString),
      ("isSourceConstant", sourceConst),
      ("hasImpureSignature", signature.isSome),
      ("deferredGroups", groups.size),
      ("hasNativeIR", nativeDecl.isSome)]
  logInfo result.pretty
