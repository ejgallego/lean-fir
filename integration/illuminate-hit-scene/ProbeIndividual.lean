import IlluminateFirHitScene.Compile
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let source ← liftCoreM IlluminateFirHitScene.Compile.captureSourceIndividual
  let unsupported := source.program.decls.filter fun declaration =>
    !Fir.Wasm.supportedDecl source.program declaration
  let arrayLoop := Lean.Name.mkStr
    (Lean.Name.mkStr
      (Lean.Name.mkStr
        (Lean.Name.mkStr (Lean.Name.mkNum `_private.Init.Data.Array.Basic 0)
          "Array")
        "forIn'Unsafe")
      "loop")
    "_redArg"
  unless unsupported.any (·.name == arrayLoop) do
    throwError "individual HitScene capture no longer reproduces {arrayLoop}"
  match Fir.Wasm.lower source.program with
  | .error (.malformed message) =>
      unless message.contains
          "Illuminate.Vec2.east._closed_1 result is incompatible with its let ABI" do
        throwError "individual HitScene capture changed failure: {message}"
  | .error error =>
      throwError "individual HitScene capture changed failure: {repr error}"
  | .ok _ =>
      throwError "individual HitScene capture unexpectedly lowered"
  logInfo m!"confirmed individual HitScene capture ABI drift ({unsupported.size} unsupported declarations)"
