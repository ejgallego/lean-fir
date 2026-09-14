import Fir.Wasm.Emit.CompilerPrivate
import Lean.Compiler.LCNF
import Lean.Elab.Command

open Lean Elab Command
open Lean.Compiler.LCNF

-- Constructors/types have persisted compiler metadata in their defining module.
-- Clearing source-body caches must not turn those declarations into fresh locals.
run_cmd do
  liftCoreM <| withoutModifyingEnv do
    let env ← getEnv
    let types := #[`Int, `Nat, `Option]
    let mut constructors := #[]
    for name in types do
      let .inductInfo info ← getConstInfo name | throwError "expected inductive {name}"
      constructors := constructors ++ info.ctors.toArray
    let ordinary := `List.length
    let roots := types ++ constructors ++ #[ordinary]
    let indices := roots.foldl (init := #[]) fun indices name =>
      match env.getModuleIdxFor? name with
      | none => indices
      | some idx => if indices.contains idx then indices else indices.push idx
    for name in roots do
      unless (env.getModuleIdxFor? name).isSome do
        throwError "regression requires imported root {name}"
    let reset := Fir.Wasm.Emit.CompilerPrivate.forgetGeneratedCompilerModuleMappings
      env indices roots
    let lost := (types ++ constructors).filter fun name =>
      (reset.getModuleIdxFor? name).isNone
    unless lost.isEmpty do
      throwError "source reset hid inductive metadata owners: {lost}"
    unless (reset.getModuleIdxFor? ordinary).isNone do
      throwError "ordinary function cache was not reset"
    setEnv reset
    for name in types do
      let _ ← getOtherDeclMonoType name
      let _ ← nameToImpureType name
    for name in constructors do
      let _ ← getOtherDeclMonoType name
      let _ ← getCtorLayout name
    logInfo m!"Preserved {types.size} inductive and {constructors.size} constructor metadata owners; ordinary function reset retained"
