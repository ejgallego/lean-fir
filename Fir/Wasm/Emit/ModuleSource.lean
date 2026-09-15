import Fir.Compiler.LCNF
import Lean.Elab.Frontend

/-!
Final-LCNF capture in the owning ordinary module's real frontend environment.
This provider does not import the target into itself, reset compiler mappings,
reconstruct source roots, or combine source declarations into a new SCC.
-/

namespace Fir.Wasm.Emit.ModuleSource

open Lean Lean.Elab Lean.Compiler.LCNF

structure CapturedModule where
  moduleName : Name
  sourceFile : System.FilePath
  environment : Environment
  options : Options
  groups : Array (Array (Decl .impure))

/-- Observe without consuming: upstream's native handoff must still run for
ordinary compile-time execution. This does not make native IR FIR's input. -/
private def recordPass (groups : IO.Ref (Array (Array (Decl .impure)))) : Pass where
  phase := .impure
  name := `firObserveOrdinaryFinalLCNF
  run decls := do
    groups.modify (·.push decls)
    return decls

private def installRecorder (env : Environment)
    (groups : IO.Ref (Array (Array (Decl .impure)))) : Environment :=
  let (installers, manager) := passManagerExt.getState env
  passManagerExt.setState env (installers,
    { manager with impurePasses := manager.impurePasses.push (recordPass groups) })

/-- Compile unchanged source using Lake's resolved setup. Like upstream's
frontend entry, the caller must enable initializer execution before imports.
Serial ordinary elaboration preserves declaration-group order. Existing source
providers and their policies are not modified by this opt-in API. -/
def compile (sourceFile : System.FilePath) (setup : ModuleSetup) :
    IO (Except MessageLog CapturedModule) := do
  setup.dynlibs.forM Lean.loadDynlib
  let input ← IO.FS.readFile sourceFile
  let inputCtx := Parser.mkInputContext input sourceFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  unless Elab.HeaderSyntax.isModule header && setup.isModule do
    throw <| IO.userError "ordinary module capture requires an actual module header and setup"
  let opts := setup.options.toOptions |>.setBool `compiler.postponeCompile false
    |>.setBool `Elab.async false
  let (env, messages) ← withImporting <| Elab.processHeaderCore
    (Elab.HeaderSyntax.startPos header)
    (setup.imports?.getD (Elab.HeaderSyntax.imports header)) true opts messages inputCtx
    (plugins := setup.plugins) (mainModule := setup.name)
    (package? := setup.package?) (arts := setup.importArts) (headerStx? := header)
  if messages.hasErrors then return .error messages
  if (env.getModuleIdx? setup.name).isSome then
    throw <| IO.userError "target module was imported into its own compilation context"
  let groups ← IO.mkRef #[]
  let env := installRecorder env groups
  let state ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages opts)
  if state.commandState.messages.hasErrors then return .error state.commandState.messages
  unless (postponedCompileDeclsExt.getState state.commandState.env).isEmpty do
    throw <| IO.userError "ordinary module source left postponed compiler groups"
  return .ok {
    moduleName := setup.name, sourceFile, environment := state.commandState.env,
    options := opts, groups := ← groups.get }

/-- Select a real local entry's closure with upstream's dependency collector.
Imported functions remain explicit signatures; this is not transitive linking. -/
def CapturedModule.artifact (captured : CapturedModule) (entry : Name) :
    IO Fir.Compiler.Lcnf.Artifact := do
  unless captured.groups.any (·.any (·.name == entry)) do
    throw <| IO.userError s!"entry `{entry}` was not captured in `{captured.moduleName}`"
  let collect : CoreM Fir.Compiler.Lcnf.Artifact := do
    let (locals, signatures) ← collectUsedDecls #[entry]
    let externals := signatures.map fun sig => {
      name := sig.name, levelParams := sig.levelParams, params := sig.params,
      type := sig.type, safe := sig.safe,
      value := .extern ((getExternAttrData? captured.environment sig.name).getD
        { entries := [.opaque] }), inlineAttr? := none : Decl .impure }
    let program := { decls := locals ++ externals : Fir.LeanIR.ImpureProgram }
    return {
      entry
      program
      externalNames := signatures.map (·.name)
      forms := Fir.Compiler.Lcnf.collectForms program }
  collect.toIO' {
    fileName := captured.sourceFile.toString
    fileMap := default
    options := captured.options } { env := captured.environment }

end Fir.Wasm.Emit.ModuleSource
