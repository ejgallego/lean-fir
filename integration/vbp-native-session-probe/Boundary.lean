import Probe
import Lean.Elab.Command

open Lean Elab Command Lean.Compiler.LCNF

-- Read-only observer around the configured passes. It forwards each input to
-- the original pass exactly once, preserves its result and environment, and
-- enriches only errors. No source unit, compiler pass order or body is changed.
private def observePass (pass : Pass) : Pass :=
  { pass with run := fun decls => do
      IO.eprintln s!"Renderer pass begin: {pass.phase}/{pass.name}/{pass.occurrence} ({decls.size} declarations)"
      try
        let result ← pass.run decls
        IO.eprintln s!"Renderer pass end: {pass.phase}/{pass.name}/{pass.occurrence} ({result.size} declarations)"
        return result
      catch error =>
        throwError "Renderer compiler boundary: phase={pass.phase}, pass={pass.name}, occurrence={pass.occurrence}\n{error.toMessageData}" }

private def observeManager : CoreM Unit := do
  let (installers, manager) := passManagerExt.getState (← getEnv)
  let manager := { manager with
    basePasses := manager.basePasses.map observePass
    monoPasses := manager.monoPasses.map observePass
    monoPassesNoLambda := manager.monoPassesNoLambda.map observePass
    impurePasses := manager.impurePasses.map observePass }
  modifyEnv fun env => passManagerExt.setState env (installers, manager)

set_option maxHeartbeats 0 in
set_option compiler.postponeCompile false in
run_cmd do
  if (← IO.getEnv "FIR_RENDERER_BOUNDARY") == some "1" then
    liftCoreM <| withoutModifyingEnv do
      -- Materialize the ordinary pass manager before wrapping it. FIR's later
      -- terminal capture installer remains responsible for final consumption.
      discard <| getPassManager
      observeManager
      discard <| NativeSessionProbe.capture
