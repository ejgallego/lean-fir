import Fir.Compiler.LCNF.Checkpoint
import Fir.Compiler.LCNF.Reify

namespace Fir.Compiler.Lcnf.CheckpointReadback

open Lean

private def verify (moduleName key entry reference : Name) : CoreM Unit := do
  let some artifact ← Checkpoint.getModule? moduleName key
    | throwError "missing checkpoint {moduleName}/{key}"
  unless artifact.entry == entry && artifact.program.contains entry do
    throwError "checkpoint entry identity changed"
  let .defnInfo expected ← getConstInfo reference
    | throwError "checkpoint reference is not a checked definition"
  unless (Reify.quoteProgram artifact.program).toOption == some expected.value do
    throwError "checkpoint program fields differ from the captured reference"
  unless artifact.forms == collectForms artifact.program do
    throwError "checkpoint form metadata changed"
  let externals := artifact.program.decls.filterMap fun decl =>
    match decl.value with
    | .extern _ => some decl.name
    | .code _ => none
  unless artifact.externalNames == externals do
    throwError "checkpoint external metadata changed"

/- No producer import and no compileEntry call: each invocation reads only
the producer's built olean, just as a narrow native consumer will do. -/
unsafe def run : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    for loadExts in [false, true] do
      enableInitializersExecution
      let env ← importModules #[{ module := `Fir.Compiler.LCNF.CheckpointShadowExamples }]
        {} (loadExts := loadExts)
      let (_, _) ← Core.CoreM.toIO
          (ctx := { fileName := "CheckpointReadback.lean", fileMap := default })
          (s := { env }) do
        verify `Fir.Compiler.LCNF.CheckpointExamples `alpha
          `Fir.Compiler.Lcnf.CheckpointExamples.identityNat
          `Fir.Compiler.Lcnf.CheckpointExamples.expectedIdentity
        verify `Fir.Compiler.LCNF.CheckpointExamples `zeta
          `Fir.Compiler.Lcnf.CheckpointExamples.addTwo
          `Fir.Compiler.Lcnf.CheckpointExamples.expectedAdd
        verify `Fir.Compiler.LCNF.CheckpointShadowExamples `alpha
          `Fir.Compiler.Lcnf.CheckpointExamples.addTwo
          `Fir.Compiler.Lcnf.CheckpointExamples.expectedAdd
        let some index := env.getModuleIdx? `Fir.Compiler.LCNF.CheckpointExamples
          | throwError "producer module index missing"
        let keys := (Checkpoint.capturedArtifactExt.getModuleEntries env index).map (·.key)
        unless keys == #[`alpha, `zeta] do
          throwError "checkpoint export order changed"
        for (moduleName, key) in #[
            (`MissingCheckpointModule, `alpha),
            (`Fir.Compiler.LCNF.Checkpoint, `alpha),
            (`Fir.Compiler.LCNF.CheckpointExamples, `missing),
            (`Fir.Compiler.LCNF.CheckpointShadowExamples, `zeta)] do
          if (← Checkpoint.getModule? moduleName key).isSome then
            throwError "wrong module/key unexpectedly resolved: {moduleName}/{key}"
        if env.header.moduleNames.any (fun name =>
            (`Fir.Validation).isPrefixOf name || (`Fir.Wasm).isPrefixOf name || name == `Fir) then
          throwError "compiler checkpoint imported unrelated validation/backend umbrellas"
      IO.println s!"PASS checkpoint readback (loadExts={loadExts}): exact programs, metadata, sorted keys, owning-module isolation and four negative lookups"
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1

end Fir.Compiler.Lcnf.CheckpointReadback
