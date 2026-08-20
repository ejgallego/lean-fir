import IlluminateFirHitScene.Compile
import Lean.Elab.Command
import Lean.Compiler.LCNF.PrettyPrinter

open Lean Elab Command

run_cmd do
  let source ← liftCoreM IlluminateFirHitScene.Compile.captureSourceIndividual
  let unsupported := source.program.decls.filter fun declaration =>
    !Fir.Wasm.supportedDecl source.program declaration
  unless unsupported.isEmpty do
    let formatted ← unsupported.mapM fun declaration => do
      let rendered ← liftCoreM <| Lean.Compiler.LCNF.ppDecl' declaration .impure
      pure rendered.pretty
    let lowering := match Fir.Wasm.lower source.program with
      | .ok _ => "lowering unexpectedly succeeded"
      | .error error => toString (repr error)
    throwError "individual HitScene capture retained unsupported declarations:\n{String.intercalate "\n\n" formatted.toList}\n\nfirst lowering result: {lowering}"
  match Fir.Wasm.validateSupported source.program with
  | .error error =>
      throwError "individual HitScene capture failed admission: {repr error}"
  | .ok _ => pure ()
  let result ← liftCoreM <| Fir.Wasm.Emit.Source.compileModuleArtifact source
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "individual HitScene capture failed lowering: {repr error}"
  logInfo m!"individual HitScene capture passed ({source.program.decls.size} declarations, {source.externalNames.size} externals, {artifact.module.functions.size} functions)"
