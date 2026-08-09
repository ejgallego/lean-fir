import Fir.Validation.LCNF
import Fir.Wasm.Emit.BitExactFloat
import Fir.Wasm.Emit.CompilerPrivate
import Fir.Wasm.Emit.Manifest
import Fir.Wasm.WellFormed
import Lean.CoreM

namespace Fir.Wasm.Emit.Source

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure

inductive CompileError where
  | lowering (error : Fir.Wasm.SupportedLoweringError)
  | encoding (error : Fir.Wasm.Emit.EncodeError)
  | manifest (message : String)
  deriving Inhabited, Repr

structure ModuleArtifact where
  source : Fir.Validation.Lcnf.Artifact
  module : Fir.Wasm.Module
  bytes : ByteArray
  formattedLcnf : String

structure Artifact extends ModuleArtifact where
  manifest : Json

private partial def environmentDeclarationAncestor? (env : Environment) (name : Name) :
    Option Name :=
  if env.contains name then
    some name
  else if name.isAnonymous then
    none
  else
    environmentDeclarationAncestor? env name.getPrefix

private partial def sourceDeclarationAncestor? (env : Environment) (name : Name) :
    CoreM (Option Name) := do
  if name.isAnonymous then return none
  if let some moduleIdx := env.getModuleIdxFor? name then
    if env.header.moduleData[moduleIdx]!.constNames.contains name &&
        (← LCNF.getImpureSignature? name).isSome then
      return some name
  sourceDeclarationAncestor? env name.getPrefix

private def addUniqueName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

/-!
Lean's ordinary `LCNF.main` entry returns `Unit`: it sends each completed
final-impure SCC directly to `Lean.IR.toIR`, then leaves callers to recover a
named closure from the LCNF environment extensions.  That recovery loses
private specializations which exist in the completed SCC but are not published
as independently compilable source declarations.

The pass below is an identity consumer installed after Lean's real final
impure pipeline.  It records the exact declaration groups immediately before
the built-in `Lean.IR.toIR` handoff.  FIR continues to consume LCNF; the later
IR conversion performed by the stock compiler is deliberately ignored.
-/

initialize finalImpureCaptureExt : EnvExtension (Array (Array (LCNF.Decl .impure))) ←
  registerEnvExtension (pure #[]) (asyncMode := .sync)

private def resetFinalImpureCapture : CoreM Unit := do
  modifyEnv fun env => finalImpureCaptureExt.modifyState env fun _ => #[]

private def resetSpecializationCache : CoreM Unit := do
  modifyEnv Fir.Wasm.Emit.CompilerPrivate.clearSpecializationCache

private def recordFinalImpureGroup (decls : Array (LCNF.Decl .impure)) :
    LCNF.CompilerM Unit := do
  modifyEnv fun env => finalImpureCaptureExt.modifyState env (·.push decls)

def finalImpureCapturePass : LCNF.Pass where
  phase := .impure
  phaseOut := .impure
  name := `firCaptureFinalImpure
  run decls := do
    recordFinalImpureGroup decls
    return decls

/-- Dynamically installed only inside one isolated source-compilation call. -/
def finalImpureCaptureInstaller : LCNF.PassInstaller :=
  LCNF.PassInstaller.installAtEnd .impure finalImpureCapturePass

mutual

private partial def collectCodeReferences (names : Array Name) :
    LCNF.Code .impure → Array Name
  | .let decl continuation =>
      let names := match decl.value with
        | .fap name _ | .pap name _ => addUniqueName names name
        | .const _ _ _ h => nomatch h
        | _ => names
      collectCodeReferences names continuation
  | .jp decl continuation =>
      collectCodeReferences (collectCodeReferences names decl.value) continuation
  | .cases cases => cases.alts.foldl collectAltReferences names
  | .oset (k := continuation) .. | .uset (k := continuation) .. |
      .sset (k := continuation) .. | .setTag (k := continuation) .. |
      .inc (k := continuation) .. | .dec (k := continuation) .. |
      .del (k := continuation) .. => collectCodeReferences names continuation
  | .jmp .. | .return .. | .unreach .. => names
  | .fun _ _ h => nomatch h

private partial def collectAltReferences (names : Array Name) :
    LCNF.Alt .impure → Array Name
  | .ctorAlt _ code | .default code => collectCodeReferences names code
  | .alt _ _ _ h => nomatch h

end

private partial def reachableDeclarations (program : Fir.LeanIR.ImpureProgram)
    (pending : List Name) (seen : Array Name := #[]) : Except String (Array Name) := do
  match pending with
  | [] => return seen
  | name :: pending =>
      if seen.contains name then
        reachableDeclarations program pending seen
      else
        let some decl := program.findDecl? name |
          throw s!"reachable declaration {name} is absent from the captured program"
        let references := match decl.value with
          | .code code => collectCodeReferences #[] code
          | .extern _ => #[]
        reachableDeclarations program (references.toList ++ pending) (seen.push name)

/--
Retain precisely the declarations named by the entry and the additional roots,
plus their transitive named-call closure. This removes source ancestors pulled
in while internalizing final LCNF when no generated declaration actually
references them.
-/
def pruneUnreachableDeclarations (artifact : Fir.Validation.Lcnf.Artifact)
    (retainedRoots : Array Name := #[]) :
    Except String Fir.Validation.Lcnf.Artifact := do
  let reachable ← reachableDeclarations artifact.program
    ([artifact.entry] ++ retainedRoots.toList)
  let program : Fir.LeanIR.ImpureProgram := {
    decls := artifact.program.decls.filter (fun decl => reachable.contains decl.name) }
  unless program.findDecl? artifact.entry |>.isSome do
    throw s!"entry {artifact.entry} disappeared during declaration pruning"
  return { artifact with
    program
    externalNames := artifact.externalNames.filter reachable.contains
    forms := Fir.Validation.Lcnf.collectForms program }

private def capturedExternDecl (sig : LCNF.Signature .impure)
    (data : ExternAttrData) : LCNF.Decl .impure :=
  { name := sig.name
    levelParams := sig.levelParams
    type := sig.type
    params := sig.params
    safe := sig.safe
    value := .extern data
    inlineAttr? := none }

private def appendCapturedDecl (decls : Array (LCNF.Decl .impure))
    (decl : LCNF.Decl .impure) : Array (LCNF.Decl .impure) :=
  match decls.find? (fun existing => existing.name == decl.name) with
  | some existing =>
      let selected := match existing.value, decl.value with
        | .code _, .extern _ => existing
        | _, _ => decl
      decls.map fun candidate =>
        if candidate.name == decl.name then selected else candidate
  | none => decls.push decl

/--
Compile one source unit and build its artifact from the declaration groups
observed by the final-impure identity pass.  Ordinary `collectUsedDecls`
continues to supply imported signatures, but a captured body always wins over
an external stub with the same generated name.
-/
private def compileEntryFinalCaptured (entry : Name) (dependencies : Array Name := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let roots := #[entry] ++ dependencies
  LCNF.main roots (← getOptions)
  let capturedGroups := finalImpureCaptureExt.getState (← getEnv)
  let (ordinaryLocals, ordinaryExternalSigs) ← LCNF.collectUsedDecls roots
  let mut localDecls : Array (LCNF.Decl .impure) := #[]
  for group in capturedGroups do
    for decl in group do
      localDecls := appendCapturedDecl localDecls decl
  for decl in ordinaryLocals do
    localDecls := appendCapturedDecl localDecls decl
  localDecls ← localDecls.mapM fun decl => do
    match decl.value with
    | .code _ => return decl
    | .extern _ =>
        let some saved ← LCNF.getLocalImpureDecl? decl.name | return decl
        match saved.value with
        | .code _ => return saved
        | .extern _ => return decl
  unless localDecls.any (fun decl => decl.name == entry) do
    throwError "final-impure capture did not contain entry `{entry}`"
  let mut localNames : NameSet := localDecls.foldl (init := {}) fun names decl =>
    names.insert decl.name
  let env ← getEnv
  let mut referencedNames : Array Name := #[]
  let mut index := 0
  while h : index < localDecls.size do
    let decl := localDecls[index]
    let mut references := match decl.value with
      | .code code => collectCodeReferences #[] code
      | .extern _ => #[]
    if let some initializer := getBuiltinInitFnNameFor? env decl.name <|>
        getInitFnNameFor? env decl.name then
      references := addUniqueName references initializer
    for name in references do
      unless localNames.contains name do
        match ← LCNF.getLocalImpureDecl? name with
        | some saved =>
            match saved.value with
            | .code _ =>
                localDecls := localDecls.push saved
                localNames := localNames.insert name
            | .extern _ =>
                referencedNames := addUniqueName referencedNames name
        | none => referencedNames := addUniqueName referencedNames name
    index := index + 1
  let mut externalSigs : Array (LCNF.Signature .impure) := #[]
  for sig in ordinaryExternalSigs do
    unless localNames.contains sig.name || externalSigs.any (·.name == sig.name) do
      externalSigs := externalSigs.push sig
  for name in referencedNames do
    unless localNames.contains name || externalSigs.any (·.name == name) do
      let some sig ← LCNF.getImpureSignature? name
        | throwError "final-impure declaration `{name}` has no captured body or external signature"
      externalSigs := externalSigs.push sig
  let externalDecls := externalSigs.map fun sig =>
    let data := getExternAttrData? env sig.name |>.getD { entries := [.opaque] }
    capturedExternDecl sig data
  let externalNames :=
    localDecls.filterMap (fun decl => match decl.value with
      | .extern _ => some decl.name
      | .code _ => none) ++ externalSigs.map (·.name)
  let program : Fir.LeanIR.ImpureProgram := { decls := localDecls ++ externalDecls }
  return {
    entry
    program
    externalNames
    forms := Fir.Validation.Lcnf.collectForms program }

private def mergeSeparatelyCompiledArtifacts (entry : Name)
    (artifacts : Array Fir.Validation.Lcnf.Artifact) : CoreM Fir.Validation.Lcnf.Artifact := do
  let localNames : NameSet := artifacts.foldl (init := {}) fun names artifact =>
    artifact.program.decls.foldl (init := names) fun names decl =>
      if artifact.externalNames.contains decl.name then names else names.insert decl.name
  let mut decls : Array (Lean.Compiler.LCNF.Decl .impure) := #[]
  -- Preserve the ordinary compiler layout: declarations supplied by the
  -- compilation units precede the unresolved imports that remain after
  -- linking. In particular, an entry-unit import must not jump ahead of the
  -- declarations supplied by a later dependency unit.
  for artifact in artifacts do
    for decl in artifact.program.decls do
      if artifact.externalNames.contains decl.name then continue
      match decls.find? (fun existing => existing.name == decl.name) with
      | some existing =>
          unless existing == decl do
            throwError "separately compiled LCNF declaration `{decl.name}` is inconsistent"
      | none =>
          decls := decls.push decl
  for artifact in artifacts do
    for decl in artifact.program.decls do
      unless artifact.externalNames.contains decl.name do continue
      if localNames.contains decl.name then continue
      match decls.find? (fun existing => existing.name == decl.name) with
      | some existing =>
          unless existing == decl do
            throwError "separately compiled LCNF declaration `{decl.name}` is inconsistent"
      | none =>
          decls := decls.push decl
  let externalNames := decls.filterMap fun decl =>
    if localNames.contains decl.name then none else some decl.name
  let program : Fir.LeanIR.ImpureProgram := { decls }
  return {
    entry
    program
    externalNames
    forms := Fir.Validation.Lcnf.collectForms program }

private def discoveredSourceRoots (artifact : Fir.Validation.Lcnf.Artifact)
    (retainedExternalNames : Array String) (excluded : Array Name) : CoreM (Array Name) := do
  let env ← getEnv
  return artifact.externalNames.foldl (init := #[]) fun additions name =>
    if retainedExternalNames.contains name.toString then
      additions
    else
      match environmentDeclarationAncestor? env name with
      | some ancestor =>
          if excluded.contains ancestor then additions
          else addUniqueName additions ancestor
      | none => additions

private partial def compileEntrySeparatelyInternalizedAux (entry : Name)
    (retainedExternalNames : Array String)
    (entryArtifact : Fir.Validation.Lcnf.Artifact) (dependencies : Array Name) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  if dependencies.isEmpty then
    return entryArtifact
  let dependencyArtifact ← withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry dependencies[0]!
      (dependencies.extract 1 dependencies.size)
  let additions ← discoveredSourceRoots dependencyArtifact retainedExternalNames
    (#[entry] ++ dependencies)
  if additions.isEmpty then
    mergeSeparatelyCompiledArtifacts entry #[entryArtifact, dependencyArtifact]
  else
    compileEntrySeparatelyInternalizedAux entry retainedExternalNames entryArtifact
      (dependencies ++ additions)

/--
Compile an entry and its discovered source dependencies as two independent
LCNF units, then link their final impure declarations. Keeping the imported
roots together preserves their shared specialization and closed-value unit,
while the entry boundary mirrors Lean's ordinary cross-module compilation and
prevents imported helpers from joining its specialization/SCC unit.
-/
def compileEntrySeparatelyInternalized (entry : Name)
    (retainedExternalNames : Array String := #[]) : CoreM Fir.Validation.Lcnf.Artifact := do
  let entryArtifact ← withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry entry
  let dependencies ← discoveredSourceRoots entryArtifact retainedExternalNames #[entry]
  compileEntrySeparatelyInternalizedAux entry retainedExternalNames entryArtifact dependencies

private def initializePersistentExtension {α β σ} [Inhabited σ]
    (extension : PersistentEnvExtension α β σ) (env : Environment) : IO Environment := do
  let state := extension.toEnvExtension.getState env
  let initialized ← extension.addImportedFn state.importedEntries { env, opts := {} }
  return extension.toEnvExtension.setState (asyncMode := .sync) env
    { state with state := initialized }

private def importPrivateModuleEnvironment (moduleName : Name)
    (options : Options) : IO Environment := do
  let imports : Array Lean.Import := #[
    { module := moduleName, importAll := true, isMeta := true }]
  let environment ← Lean.withImporting do
    let (_, state) ← Lean.importModulesCore (globalLevel := .private) imports |>.run
    let state := Fir.Wasm.Emit.CompilerPrivate.setTargetRuntimePhase state moduleName
    Lean.finalizeImport (leakEnv := true) (loadExts := false)
      (level := .exported) state imports options
  let environment := environment.setMainModule moduleName
  let environment ← initializePersistentExtension Lean.Compiler.CSimp.ext.ext environment
  let environment ← initializePersistentExtension Meta.instanceExtension.ext environment
  let environment ← initializePersistentExtension classExtension environment
  let environment ← initializePersistentExtension Meta.Match.Extension.extension environment
  let some moduleIndex := environment.getModuleIdx? moduleName |
    throw <| IO.userError s!"deferred final-LCNF target module `{moduleName}` is unavailable"
  let externals := LCNF.impureSigExt.getModuleEntries environment moduleIndex |>.filter
    (isExtern environment ·.name)
  let environment := externals.foldl (fun environment declaration =>
    LCNF.setDeclPublic (LCNF.impureSigExt.addEntry environment declaration)
      declaration.name) environment
  let state := Lean.IR.declMapExt.toEnvExtension.getState environment
  let unbox : Name → Name
    | .str functionName "_boxed" => functionName
    | name => name
  let localState := state.importedEntries[moduleIndex]!.foldl
    (fun (declarations, declarationsByName) declaration =>
      if isExtern environment (unbox declaration.name) then
        (declaration :: declarations, declarationsByName.insert declaration.name declaration)
      else
        (declarations, declarationsByName)) state.state
  let environment := Lean.IR.declMapExt.toEnvExtension.setState
    (asyncMode := .sync) environment { state with state := localState }
  let some environment :=
      Fir.Wasm.Emit.CompilerPrivate.setTargetDirectImports environment moduleIndex |
    throw <| IO.userError s!"deferred target module `{moduleName}` has no module data"
  return environment

private def installFinalImpureCaptureDirect : CoreM Unit := do
  let (installers, manager) := LCNF.passManagerExt.getState (← getEnv)
  let impurePasses ← finalImpureCaptureInstaller.install manager.impurePasses
  modifyEnv fun environment => LCNF.passManagerExt.setState environment
    (installers, { manager with impurePasses })

private def artifactFromCapturedModule (entry : Name) : CoreM Fir.Validation.Lcnf.Artifact := do
  let capturedGroups := finalImpureCaptureExt.getState (← getEnv)
  let mut localDecls : Array (LCNF.Decl .impure) := #[]
  for group in capturedGroups do
    for declaration in group do
      localDecls := appendCapturedDecl localDecls declaration
  unless localDecls.any (·.name == entry) do
    throwError "deferred final-LCNF module capture did not contain entry `{entry}`"
  let localNames : NameSet := localDecls.foldl (init := {}) fun names declaration =>
    names.insert declaration.name
  let environment ← getEnv
  let mut referencedNames : Array Name := #[]
  for declaration in localDecls do
    let mut references := match declaration.value with
      | .code code => collectCodeReferences #[] code
      | .extern _ => #[]
    if let some initializer := getBuiltinInitFnNameFor? environment declaration.name <|>
        getInitFnNameFor? environment declaration.name then
      references := addUniqueName references initializer
    for reference in references do
      unless localNames.contains reference do
        referencedNames := addUniqueName referencedNames reference
  let mut externalDecls : Array (LCNF.Decl .impure) := #[]
  for name in referencedNames do
    let some signature ← LCNF.getImpureSignature? name |
      throwError "deferred final-LCNF reference `{name}` has no signature"
    let data := getExternAttrData? environment name |>.getD { entries := [.opaque] }
    externalDecls := externalDecls.push (capturedExternDecl signature data)
  let program : Fir.LeanIR.ImpureProgram := { decls := localDecls ++ externalDecls }
  return {
    entry
    program
    externalNames := externalDecls.map (·.name)
    forms := Fir.Validation.Lcnf.collectForms program }

private def replayDeferredModuleFinalCaptured (moduleName entry : Name)
    (options : Options) : CoreM Fir.Validation.Lcnf.Artifact := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdx? moduleName |
    throwError "deferred final-LCNF target module `{moduleName}` is unavailable"
  let groups := LCNF.postponedCompileDeclsExt.getModuleEntries environment moduleIndex
  if groups.isEmpty then
    throwError "module `{moduleName}` has no deferred compiler groups"
  modifyEnv (LCNF.postponedCompileDeclsExt.setState ·
    (groups.foldl (fun state group =>
      group.declNames.foldl (·.insert · group) state) {}))
  resetFinalImpureCapture
  resetSpecializationCache
  installFinalImpureCaptureDirect
  for group in groups do
    for declaration in group.declNames do
      LCNF.resumeCompilation declaration options
  artifactFromCapturedModule entry

private def compileDeferredModuleFinalCaptured (moduleName entry : Name) :
    CoreM (Option Fir.Validation.Lcnf.Artifact) := do
  let options := compiler.inLeanIR.set (← getOptions) true
  let environment ← Lean.Core.liftIOCore <|
    importPrivateModuleEnvironment moduleName options
  let some moduleIndex := environment.getModuleIdx? moduleName |
    throwError "deferred final-LCNF target module `{moduleName}` is unavailable"
  if (LCNF.postponedCompileDeclsExt.getModuleEntries environment moduleIndex).isEmpty then
    return none
  let context ← read
  let artifact ← Lean.Core.liftIOCore <|
    (replayDeferredModuleFinalCaptured moduleName entry options).toIO'
      { context with options } { env := environment }
  return some artifact

private def sourceModuleFor? (environment : Environment) (name : Name) :
    CoreM (Option (Name × Name)) := do
  let some sourceRoot ← sourceDeclarationAncestor? environment name | return none
  let some moduleIndex := environment.getModuleIdxFor? sourceRoot | return none
  return some (environment.header.moduleNames[moduleIndex]!, sourceRoot)

private partial def compileEntryDeferredModulesInternalizedAux (entry : Name)
    (retainedExternalNames : Array String) (environment : Environment)
    (pending : Array (Name × Name × Bool)) (seenModules : Array Name)
    (artifacts : Array Fir.Validation.Lcnf.Artifact) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let some (moduleName, sourceRoot, required) := pending[0]? | do
    let merged ← mergeSeparatelyCompiledArtifacts entry artifacts
    match pruneUnreachableDeclarations merged with
    | .ok artifact => return artifact
    | .error message => throwError message
  let pending := pending.extract 1 pending.size
  if seenModules.contains moduleName then
    return ← compileEntryDeferredModulesInternalizedAux entry retainedExternalNames
      environment pending seenModules artifacts
  let some artifact ← compileDeferredModuleFinalCaptured moduleName sourceRoot | do
    if required then
      throwError "entry module `{moduleName}` has no deferred compiler groups; build its source view with `compiler.postponeCompile=true`"
    return ← compileEntryDeferredModulesInternalizedAux entry retainedExternalNames
      environment pending (seenModules.push moduleName) artifacts
  let discoveryArtifact ← match pruneUnreachableDeclarations artifact with
    | .ok artifact => pure artifact
    | .error message => throwError message
  let mut additions : Array (Name × Name × Bool) := #[]
  for externalName in discoveryArtifact.externalNames do
    if retainedExternalNames.contains externalName.toString then continue
    let some sourceModule ← sourceModuleFor? environment externalName | continue
    unless seenModules.contains sourceModule.1 || pending.any (·.1 == sourceModule.1) ||
        additions.any (·.1 == sourceModule.1) do
      additions := additions.push (sourceModule.1, sourceModule.2, false)
  compileEntryDeferredModulesInternalizedAux entry retainedExternalNames environment
    (pending ++ additions) (seenModules.push moduleName) (artifacts.push artifact)

/--
Compile the exact deferred declaration groups stored for every recursively
required source module, in the same order used by Lean's `leanir` driver, then
retain the entry's named-call closure. This preserves private specialization,
closed-term, and mutual-group identities while FIR consumes final LCNF rather
than the IR subsequently emitted by Lean.

Every source module intended for internalization must have been built with
`compiler.postponeCompile=true`, which records replay groups in its private
olean data. Prebuilt Lean/runtime modules without such groups remain explicit
external declarations.
-/
def compileEntryModuleWiseInternalized (entry : Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let environment ← getEnv
  let some (moduleName, sourceRoot) ← sourceModuleFor? environment entry |
    throwError "entry `{entry}` has no source module"
  compileEntryDeferredModulesInternalizedAux entry retainedExternalNames environment
    #[(moduleName, sourceRoot, true)] #[] #[]

/--
Compile an entry and its recursively discovered source dependencies as one
compiler unit, obtaining that unit from the exact final-impure SCCs observed
before Lean's IR handoff. Recompiling the growing root set avoids having to
equate independently generated binder identifiers while retaining private
specializations as ordinary local declarations.
-/
private partial def compileEntryFinalCapturedInternalizedAux (entry : Name)
    (dependencies : Array Name := #[]) (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let artifact ← compileEntryFinalCaptured entry dependencies
  let additions ← discoveredSourceRoots artifact retainedExternalNames
    (#[entry] ++ dependencies)
  if additions.isEmpty then
    return artifact
  compileEntryFinalCapturedInternalizedAux entry (dependencies ++ additions)
    retainedExternalNames

def compileEntryFinalCapturedInternalized (entry : Name)
    (dependencies : Array Name := #[]) (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := withoutModifyingEnv do
  resetFinalImpureCapture
  resetSpecializationCache
  LCNF.addPass ``finalImpureCaptureInstaller
  compileEntryFinalCapturedInternalizedAux entry dependencies retainedExternalNames

/--
Compile several public source entries in one exact final-LCNF unit, internalize
their recursively discovered source dependencies, and discard declarations
that are not reachable from one of the requested entries. The first entry is
the artifact's canonical entry; all entries remain ordinary local declarations.
-/
def compileEntriesFinalCapturedInternalized (entries : Array Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let some entry := entries[0]? |
    throwError "final-LCNF multi-entry capture requires at least one entry"
  unless (entries.foldl (init := #[]) addUniqueName).size == entries.size do
    throwError "final-LCNF multi-entry capture received duplicate entries: {entries}"
  let artifact ← compileEntryFinalCapturedInternalized entry
    (entries.extract 1 entries.size) retainedExternalNames
  for root in entries do
    let some decl := artifact.program.findDecl? root |
      throwError "final-LCNF multi-entry capture did not contain root `{root}`"
    if artifact.externalNames.contains decl.name then
      throwError "final-LCNF multi-entry root `{root}` remained external"
  match pruneUnreachableDeclarations artifact (entries.extract 1 entries.size) with
  | .ok artifact => return artifact
  | .error message => throwError message

/--
Recursively ask Lean to compile imported source helpers whose declarations are
available in the environment. Generated helper suffixes are rooted at their
nearest source declaration; retaining a name leaves that helper as an explicit
semantic Wasm import.
-/
partial def compileEntryInternalized (entry : Name) (dependencies : Array Name := #[])
    (retainedExternalNames : Array String := #[]) : CoreM Fir.Validation.Lcnf.Artifact := do
  let artifact ← withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry entry dependencies
  let env ← getEnv
  let additions := artifact.externalNames.foldl (init := #[]) fun additions name =>
    if retainedExternalNames.contains name.toString then
      additions
    else
      match environmentDeclarationAncestor? env name with
      | some ancestor =>
          if ancestor == entry || dependencies.contains ancestor then additions
          else addUniqueName additions ancestor
      | none => additions
  if additions.isEmpty then
    return artifact
  compileEntryInternalized entry (dependencies ++ additions) retainedExternalNames

/--
Lower an already captured compiler artifact, apply one symbolic-module
pipeline, and encode only its result.
-/
private def installBitExactFloatExports (module : Fir.Wasm.Module) :
    List Name → Except String Fir.Wasm.Module
  | [] => return module
  | entry :: entries => do
      let module ← Fir.Wasm.Emit.BitExactFloat.install module entry
      installBitExactFloatExports module entries

def compileModuleArtifactWithExports (source : Fir.Validation.Lcnf.Artifact)
    (exports : Array Name)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) := do
  if exports.isEmpty then
    return .error (.manifest "Wasm source lowering requires at least one export")
  unless (exports.foldl (init := #[]) addUniqueName).size == exports.size do
    return .error (.manifest s!"Wasm source lowering received duplicate exports: {exports}")
  unless exports.contains source.entry do
    return .error (.manifest s!"Wasm exports do not contain source entry {source.entry}")
  let module ←
    match Fir.Wasm.lowerSupported source.program with
    | .ok module => pure module
    | .error error => return .error (.lowering error)
  for exportedName in exports do
    unless module.functions.any (fun function => function.name == exportedName) do
      return .error (.manifest s!"Wasm export {exportedName} is not a lowered source function")
  let module := { module with exports }
  let module ← match installBitExactFloatExports module exports.toList with
    | .ok module => pure module
    | .error message => return .error (.manifest message)
  let module ← match transform module with
    | .ok transformed => pure transformed
    | .error error => return .error error
  let bytes ←
    match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => return .error (.encoding error)
  let formattedLcnf ← source.format
  return .ok { source, module, bytes, formattedLcnf }

/--
Lower an already captured compiler artifact with its canonical entry as the
only public source export, apply one symbolic-module pipeline, and encode the
result.
-/
def compileModuleArtifactWith (source : Fir.Validation.Lcnf.Artifact)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) :=
  compileModuleArtifactWithExports source #[source.entry] transform

/-- Lower and encode an already captured compiler artifact. -/
def compileModuleArtifact (source : Fir.Validation.Lcnf.Artifact) :
    CoreM (Except CompileError ModuleArtifact) :=
  compileModuleArtifactWith source .ok

/--
Compile one Lean declaration through final impure LCNF into a reusable Wasm
module. Invocation data is attached separately with `withInvocation`.
-/
def compileModule (entry : Name) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError ModuleArtifact) := do
  let source ← withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry entry dependencies
  compileModuleArtifact source

/-- Build the invocation-free descriptor for a reusable compiled module. -/
def ModuleArtifact.moduleManifest (artifact : ModuleArtifact) : Except CompileError Json :=
  Manifest.moduleJson artifact.source.entry artifact.source.entry artifact.module
    |>.mapError .manifest

/-- Attach one checked semantic invocation to an already compiled module. -/
def ModuleArtifact.withInvocation (artifact : ModuleArtifact) (artifactName : String)
    (sourceEntry entry : Name) (args : Array Value) : Except CompileError Artifact := do
  let manifest ← Manifest.artifactJson artifactName sourceEntry entry artifact.module args
    |>.mapError .manifest
  return {
    source := artifact.source
    module := artifact.module
    bytes := artifact.bytes
    formattedLcnf := artifact.formattedLcnf
    manifest }

/--
Attach one checked semantic invocation whose arguments may refer to an explicit
initial FIR runtime. The runtime is invocation data and does not affect the
captured declaration, lowered module, or encoded Wasm bytes.
-/
def ModuleArtifact.withRuntimeInvocation (artifact : ModuleArtifact) (artifactName : String)
    (sourceEntry entry : Name) (runtime : RuntimeState) (args : Array Value) :
    Except CompileError Artifact := do
  let manifest ← Manifest.artifactJsonWithRuntime artifactName sourceEntry entry artifact.module
      runtime args
    |>.mapError .manifest
  return {
    source := artifact.source
    module := artifact.module
    bytes := artifact.bytes
    formattedLcnf := artifact.formattedLcnf
    manifest }

/-- Check that a backend-neutral validation result schema agrees with the emitted ABI lane. -/
def validationSchemaAcceptsAbiKind : Fir.Validation.ValidationSchema → Fir.Wasm.AbiKind → Bool
  | .usize, .usize => true
  | .bits 8, .uint8 => true
  | .bits 16, .uint16 => true
  | .bits 32, .uint32 => true
  | .bits 64, .uint64 => true
  | .float32, .float32 => true
  | .float64, .float => true
  | .bool, .uint8 => true
  | .unit, kind
  | .bool, kind
  | .nat, kind
  | .int, kind
  | .string, kind
  | .bytes, kind
  | .seq _, kind
  | .ctor .., kind => kind.isObjectLike
  | _, _ => false

/-- Normalize a backend-neutral validation value to the checked parameter ABI.
The validation protocol represents `Bool` as a tagged object, while Lean 4.32
uses scalar `UInt8` for compiler-produced Boolean parameters. -/
def validationArgumentForAbi (schema : Fir.Validation.ValidationSchema)
    (kind : Fir.Wasm.AbiKind) (value : Value) : Except String Value := do
  unless validationSchemaAcceptsAbiKind schema kind do
    throw s!"argument schema {repr schema} does not match ABI kind {repr kind}"
  match schema, kind, value with
  | .bool, .uint8, .object (.tagged payload) =>
      if payload == 0 || payload == 1 then
        return .scalar (.uint8 (UInt8.ofNat payload.toNat))
      else
        throw s!"Boolean argument tag must be zero or one, got {payload}"
  | _, _, value =>
      unless kind.acceptsValue value do
        throw s!"argument {repr value} does not match ABI kind {repr kind}"
      return value

/--
Attach an invocation encoded from the validation protocol. This is the common
boundary for corpus-driven emitters: schemas check both the source arguments
and the emitted result lane, while validation datums construct the initial FIR
runtime and semantic argument values.
-/
def ModuleArtifact.withValidationInvocation (artifact : ModuleArtifact)
    (artifactName : String) (sourceEntry entry : Name)
    (argSchemas : Array Fir.Validation.ValidationSchema)
    (data : Array Fir.Validation.ValidationDatum)
    (resultSchema : Fir.Validation.ValidationSchema) : Except CompileError Artifact := do
  let function ← Manifest.entryFunction artifact.module entry |>.mapError .manifest
  let resultKind ← Manifest.entryResultKind entry function |>.mapError .manifest
  unless validationSchemaAcceptsAbiKind resultSchema resultKind do
    throw (.manifest s!"result schema {repr resultSchema} does not match ABI kind {repr resultKind}")
  let paramKinds := function.params.map (·.snd)
  unless paramKinds.size == argSchemas.size do
    throw (.manifest
      s!"entry {entry} expects {paramKinds.size} argument schemas, got {argSchemas.size}")
  let (runtime, args) ← Fir.Validation.Lcnf.encodeArgs argSchemas data |>.mapError .manifest
  let args ← (paramKinds.toList.zip (argSchemas.toList.zip args.toList)).mapM
    fun (kind, schema, value) =>
      validationArgumentForAbi schema kind value |>.mapError .manifest
  let args := args.toArray
  if runtime.heap.isEmpty then
    artifact.withInvocation artifactName sourceEntry entry args
  else
    artifact.withRuntimeInvocation artifactName sourceEntry entry runtime args

/--
Compile a Lean declaration and attach one checked semantic invocation. The
arguments affect only the manifest, never capture, lowering, or Wasm bytes.
-/
def compile (entry : Name) (args : Array Value) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withInvocation entry.toString entry entry args

/-- Compile a Lean declaration and attach an invocation with an explicit initial runtime. -/
def compileWithRuntime (entry : Name) (runtime : RuntimeState) (args : Array Value)
    (dependencies : Array Name := #[]) : CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withRuntimeInvocation entry.toString entry entry runtime args

/-- Compile a source declaration and attach one validation-protocol invocation. -/
def compileValidationInvocation (artifactName : String) (entry : Name)
    (argSchemas : Array Fir.Validation.ValidationSchema)
    (data : Array Fir.Validation.ValidationDatum)
    (resultSchema : Fir.Validation.ValidationSchema)
    (dependencies : Array Name := #[]) : CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withValidationInvocation artifactName entry entry argSchemas data resultSchema

/-- Compile a zero-argument Lean declaration and record its closed invocation. -/
def compileClosed (entry : Name) (dependencies : Array Name := #[]) :
    CoreM (Except CompileError Artifact) :=
  compile entry #[] dependencies

private def writeArtifactFiles (artifact : ModuleArtifact) (manifest : Json)
    (path : System.FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path artifact.bytes
  IO.FS.writeFile (path.toString ++ ".json") manifest.compress
  IO.FS.writeFile (path.toString ++ ".lcnf") (artifact.formattedLcnf ++ "\n")

/-- Write reusable Wasm, its invocation-free ABI descriptor, and captured LCNF. -/
def ModuleArtifact.write (artifact : ModuleArtifact) (path : System.FilePath) :
    IO (Except CompileError Unit) := do
  let manifest ← match artifact.moduleManifest with
    | .ok manifest => pure manifest
    | .error error => return .error error
  writeArtifactFiles artifact manifest path
  return .ok ()

def Artifact.write (artifact : Artifact) (path : System.FilePath) : IO Unit := do
  writeArtifactFiles artifact.toModuleArtifact artifact.manifest path

end Fir.Wasm.Emit.Source
