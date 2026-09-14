import Probe
import Lean.Elab.Command

open Lean Elab Command Lean.Compiler.LCNF
open Fir.Wasm.Emit.Source

-- Non-module Source cannot be imported with `import all`. Resolve its exact
-- private declarations from Lean's name metadata, only in this diagnostic.
elab "sourcePrivate% " id:ident : term => do
  let env ← getEnv
  let some (name, _) := env.constants.toList.find? fun (name, _) =>
    privateToUserName? name == some id.getId
    | throwError "private source function not found: {id.getId}"
  return mkConst name

private def sourceCompilationRoot? := sourcePrivate% Fir.Wasm.Emit.Source.sourceCompilationRoot?
private def discoveredFinalSourceRoots := sourcePrivate% Fir.Wasm.Emit.Source.discoveredFinalSourceRoots
private def sourceOwnersCallingUnresolvedDeclarations := sourcePrivate% Fir.Wasm.Emit.Source.sourceOwnersCallingUnresolvedDeclarations
private def addSourceCompilationRoot := sourcePrivate% Fir.Wasm.Emit.Source.addSourceCompilationRoot
private def addSourceBridgeRoots := sourcePrivate% Fir.Wasm.Emit.Source.addSourceBridgeRoots
private def sourceRuntimeValueClosure := sourcePrivate% Fir.Wasm.Emit.Source.sourceRuntimeValueClosure
private def sourceSpecializationBridgeRoots := sourcePrivate% Fir.Wasm.Emit.Source.sourceSpecializationBridgeRoots

private def target : Name :=
  "_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map._at_._private.Verso.Doc.0.Verso.Doc.ListItem.toJson.spec_0".toName

private def namesJson (names : Array Name) : Json := toJson (names.map Name.toString)

private def rootsJson (roots : Array SourceCompilationRoot) : Json :=
  toJson (roots.map fun root => Json.mkObj [
    ("name", toJson root.name.toString), ("companions", namesJson root.companions)])

private def snapshot : CoreM Json := do
  let env ← getEnv
  let names := #[target] ++
    Fir.Wasm.Emit.CompilerPrivate.specializationCallerCandidates target ++
    Fir.Wasm.Emit.CompilerPrivate.specializationCalleeCandidates target
  let rows ← names.mapM fun name => do
    let idx := env.getModuleIdxFor? name
    let root ← sourceCompilationRoot? env name
    return Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson (idx.map fun i => env.header.moduleNames[i]!.toString)),
      ("constant", toJson (env.find? name).isSome),
      ("sourceIndex", toJson (idx.any fun i => env.header.moduleData[i]!.constNames.contains name)),
      ("extraIndex", toJson (idx.any fun i => env.header.moduleData[i]!.extraConstNames.contains name)),
      ("impureSignature", toJson (← getImpureSignature? name).isSome),
      ("localImpure", toJson (← getLocalImpureDecl? name).isSome),
      ("nativeIR", toJson (Lean.IR.findEnvDecl env name).isSome),
      ("resolvedRoot", rootsJson root.toArray)]
  return toJson rows

-- Read-only A/B of the current traversal versus upstream's executable body
-- selection. This does not add compilation roots or invoke the final rebuild.
private partial def runtimeClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) (names : Array Name := #[]) : CoreM (Array Name) := do
  let some name := pending.head? | return names
  let pending := pending.tail!
  if seen.contains name then return ← runtimeClosure env pending seen names
  let seen := seen.insert name
  unless env.constants.contains name && !isExtern env name &&
      (← sourceDeclarationIsCompilable env name) do
    return ← runtimeClosure env pending seen names
  let info ← getDeclInfo? name
  let references := (info.bind (·.value? (allowOpaque := true))).map Expr.getUsedConstants |>.getD #[]
  runtimeClosure env (references.toList ++ pending) seen (names.push name)

private def diagnose : CoreM Unit := do
  let initial ← snapshot
  let (artifact, candidates) ← NativeSessionProbe.captureBeforeFinal
  let beforeFinal ← snapshot
  let retained := candidates.map Name.toString ++
    Fir.Wasm.Emit.ResidentLinker.closedApplicationRetainedExternalNames
  let env ← getEnv
  let direct ← discoveredFinalSourceRoots artifact retained #[]
  let callers ← sourceOwnersCallingUnresolvedDeclarations artifact retained
  let roots := callers.foldl addSourceCompilationRoot direct
  let unresolved ← artifact.externalNames.filterM fun name => do
    if retained.contains name.toString then return false
    return (← sourceCompilationRoot? env name).isSome
  let bridged ← addSourceBridgeRoots env unresolved (direct.map (·.name)) roots
  let sourceNames ← sourceRuntimeValueClosure env (bridged.toList.flatMap fun root =>
    root.name :: root.companions.toList)
  let executableNames ← runtimeClosure env (bridged.toList.flatMap fun root =>
    root.name :: root.companions.toList)
  let specializations ← sourceSpecializationBridgeRoots env artifact bridged
  let result := Json.mkObj [
    ("imported", initial), ("beforeFinal", beforeFinal),
    ("targetCaptured", toJson (artifact.program.findDecl? target).isSome),
    ("targetExternal", toJson (artifact.externalNames.contains target)),
    ("directRoots", rootsJson direct), ("callerRoots", rootsJson callers),
    ("bridgedRoots", rootsJson bridged), ("sourceValueClosure", namesJson sourceNames),
    ("executableValueClosure", namesJson executableNames),
    ("specializationRoots", rootsJson specializations)]
  IO.FS.writeFile "../../.deps/native-session-probe/control/provenance.json" (result.pretty ++ "\n")
  IO.println s!"Provenance recorded: {artifact.program.decls.size} pre-final declarations"

set_option maxHeartbeats 0 in
set_option compiler.postponeCompile false in
run_cmd do
  if (← IO.getEnv "FIR_RENDERER_PROVENANCE") == some "1" then
    liftCoreM diagnose
