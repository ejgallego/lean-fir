import Probe
import Lean.Elab.Command

open Lean Elab Command

elab "runtimeClosure%" : term => do
  let env ← getEnv
  let some (name, _) := env.constants.toList.find? fun (name, _) =>
    privateToUserName? name == some `Fir.Wasm.Emit.Source.sourceRuntimeValueClosure
    | throwError "runtime source closure function not found"
  return mkConst name

run_cmd liftCoreM do
  let env ← getEnv
  let root := "_private.Verso.Doc.0.Verso.Doc.Block.toJson".toName
  let some logical := env.find? root | throwError "missing imported root"
  let some executable ← Lean.Compiler.LCNF.getDeclInfo? root | throwError "missing executable root"
  unless logical.name != executable.name do
    throwError "regression requires an imported partial definition"
  let logicalRefs := logical.value? (allowOpaque := true) |>.map Expr.getUsedConstants |>.getD #[]
  let executableRefs := executable.value? (allowOpaque := true) |>.map Expr.getUsedConstants |>.getD #[]
  let runtimeOnly ← executableRefs.filterM fun name => do
    if logicalRefs.contains name || !env.constants.contains name || isExtern env name then return false
    return ← Fir.Wasm.Emit.Source.sourceDeclarationIsCompilable env name
  unless !runtimeOnly.isEmpty do throwError "missing executable-only regression dependencies"
  let names ← runtimeClosure% env [root]
  let missing := runtimeOnly.filter (!names.contains ·)
  unless missing.isEmpty do
    throwError "runtime source closure missed executable partial-body dependencies: {missing}"
  logInfo "Runtime source closure follows the executable partial body"
