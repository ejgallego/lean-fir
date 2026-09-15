import Probe
import Lean.Elab.Command

open Lean Elab Command Lean.Compiler.LCNF

-- This is a diagnostic of imported metadata, not a source compilation unit or
-- a manually seeded renderer dependency. These are the observed caller/reader
-- identities of one real shared imported specialization.
private def checkSharedImport : CoreM Unit := withoutModifyingEnv do
  let env ← getEnv
  let owner := "_private.Verso.Doc.0.Verso.Doc.ListItem.toJson".toName
  let reader := "_private.Verso.Doc.0.Verso.Doc.DescItem.toJson".toName
  let helper := "_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map._at_._private.Verso.Doc.0.Verso.Doc.ListItem.toJson.spec_0".toName
  let some moduleIndex := env.getModuleIdxFor? owner |
    throwError "observed specialization owner is unavailable"
  unless (← getBaseDecl? helper).isSome && (env.find? helper).isNone do
    throwError "expected an imported compiler-only helper"
  let some before ← getBaseDecl? reader | throwError "imported reader absent"
  let reset := Fir.Wasm.Emit.CompilerPrivate.forgetGeneratedCompilerModuleMappings
    env #[moduleIndex] #[owner]
  setEnv reset
  unless (← getBaseDecl? helper).isNone do
    throwError "diagnostic changed: helper remains resolvable after reset"
  let some after ← getBaseDecl? reader |
    throwError "diagnostic changed: dependent imported reader was invalidated"
  for decl in #[before, after] do
    let found ← IO.mkRef false
    decl.value.forCodeM fun code => code.forM fun c => do
      let .let { value := .const name .., .. } .. := c | return
      if name == helper then found.set true
    unless ← found.get do throwError "diagnostic changed: imported reader edge absent"
  logInfo "Confirmed: root-local reset hides shared helper but retains dependent imported base body"

run_cmd liftCoreM checkSharedImport
