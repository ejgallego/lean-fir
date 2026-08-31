import Fir.Validation.LCNF
import Fir.Wasm.Emit.BitExactFloat
import Fir.Wasm.Emit.ClosureDispatch
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

structure SourceCompilationRoot where
  name : Name
  companions : Array Name := #[]

private def addUniqueName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

/-- Match Lean's code-generator computability boundary before promoting an
environment declaration into the recursively growing source unit. The public
`LCNF.shouldGenerateCode` predicate deliberately answers a broader source-shape
question and does not reject declarations marked noncomputable. -/
def sourceDeclarationIsCompilable (env : Environment) (name : Name) : CoreM Bool := do
  if isNoncomputable env name || isNoncomputable env (mkUnsafeRecName name) then
    return false
  LCNF.shouldGenerateCode name

/--
Resolve a generated specialization to the source caller that owns its body.
Lean embeds the caller after `._at_.`; accept that provenance when the caller
is an independently compilable final-LCNF source declaration. The generated
name's apparent module is not authoritative: a specialization of a private
generic callee retains the callee's private-module prefix. Include the generic
callee in the next growing unit so the specializer reconstructs the caller's
source context in the same pass-manager run.
-/
private def specializationSourceCaller? (env : Environment) (name : Name) :
    CoreM (Option SourceCompilationRoot) := do
  for candidate in
      Fir.Wasm.Emit.CompilerPrivate.specializationCallerCandidates name do
    let some source ← sourceDeclarationAncestor? env candidate | continue
    if source == candidate then
      unless ← sourceDeclarationIsCompilable env candidate do continue
      let mut companions : Array Name := #[]
      for callee in
          Fir.Wasm.Emit.CompilerPrivate.specializationCalleeCandidates name do
        unless env.constants.contains callee do continue
        if isExtern env callee then continue
        unless ← sourceDeclarationIsCompilable env callee do continue
        companions := addUniqueName companions callee
      return some { name := candidate, companions }
  return none

/--
Recover the real extern declaration behind an upstream-generated boxed
adapter. Compiling the extern through Lean's ordinary final-LCNF pipeline lets
`LCNF.ExplicitBoxing.addBoxedVersions` derive the adapter from its exact raw
signature; FIR does not reproduce that ABI policy or catalog wrapper names.
-/
private def boxedExternSourceRoot? (env : Environment) (name : Name) :
    CoreM (Option SourceCompilationRoot) := do
  let .str declaration "_boxed" := name | return none
  unless env.constants.contains declaration do return none
  unless isExtern env declaration do return none
  unless ← LCNF.shouldGenerateCode declaration do return none
  return some { name := declaration }

private def sourceCompilationRoot? (env : Environment) (name : Name) :
    CoreM (Option SourceCompilationRoot) := do
  if let some caller ← specializationSourceCaller? env name then
    return some caller
  if let some declaration ← boxedExternSourceRoot? env name then
    return some declaration
  let some ancestor := environmentDeclarationAncestor? env name | return none
  match env.find? ancestor with
  | some (.ctorInfo _) | some (.inductInfo _) => return none
  | _ => pure ()
  if isExtern env ancestor then return none
  unless ← sourceDeclarationIsCompilable env ancestor do return none
  return some { name := ancestor }

private def addSourceCompilationRoot (roots : Array SourceCompilationRoot)
    (root : SourceCompilationRoot) : Array SourceCompilationRoot :=
  match roots.findIdx? (·.name == root.name) with
  | none => roots.push root
  | some index => roots.modify index fun existing =>
      { existing with
        companions := root.companions.foldl addUniqueName existing.companions }

/-!
Lean's ordinary `LCNF.main` entry returns `Unit`: it sends each completed
final-impure SCC directly to `Lean.IR.toIR`, then leaves callers to recover a
named closure from the LCNF environment extensions.  That recovery loses
private specializations which exist in the completed SCC but are not published
as independently compilable source declarations.

The pass below is a terminal consumer installed after Lean's real final impure
pipeline. It records the exact declaration groups immediately before the
built-in `Lean.IR.toIR` handoff, then consumes them. The stock driver therefore
still selects and runs Lean's complete configured LCNF pipeline, while its
mandatory IR phase receives an empty group. FIR consumes the captured LCNF
directly and does not pay for, or depend on, a throwaway IR compilation.
-/

initialize finalImpureCaptureExt : EnvExtension (Array (Array (LCNF.Decl .impure))) ←
  registerEnvExtension (pure #[]) (asyncMode := .sync)

private def resetFinalImpureCapture : CoreM Unit := do
  modifyEnv fun env => finalImpureCaptureExt.modifyState env fun _ => #[]

private def resetCompilerCaches (moduleIndices : Array ModuleIdx)
    (sourceRoots : Array Name) : CoreM Unit := do
  modifyEnv fun environment =>
    Fir.Wasm.Emit.CompilerPrivate.forgetGeneratedCompilerModuleMappings
      environment moduleIndices sourceRoots

private def recordFinalImpureGroup (decls : Array (LCNF.Decl .impure)) :
    LCNF.CompilerM Unit := do
  modifyEnv fun env => finalImpureCaptureExt.modifyState env (·.push decls)

def finalImpureCapturePass : LCNF.Pass where
  phase := .impure
  phaseOut := .impure
  name := `firCaptureFinalImpure
  run decls := do
    recordFinalImpureGroup decls
    return #[]

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

private def declaredExternalBehindBoxedAdapter? (externalNames : Array Name) :
    Name → Option Name
  | .str declaration "_boxed" =>
      if externalNames.contains declaration then some declaration else none
  | _ => none

/--
Internalize Lean's generated boxed adapters for an explicit source-level
external frontier while leaving the named raw declarations external.

Some source compilers expose host operations through their own declaration
attributes rather than Lean's `@[extern]`. Their imported final LCNF still has
the ordinary raw declaration and `._boxed` call boundary, but FIR must not
compile the opaque source fallback or retain the generated adapter as a second
host import. Re-run Lean's public `LCNF.addBoxedVersions` pass over the exact
captured raw signatures and replace only matching unresolved adapters. This
keeps boxed ABI policy upstream-owned and does not teach FIR about a producer's
custom attribute.
-/
def internalizeExternalBoxedAdapters (artifact : Fir.Validation.Lcnf.Artifact)
    (externalNames : Array Name) : CoreM Fir.Validation.Lcnf.Artifact := do
  let boxedSource? := declaredExternalBehindBoxedAdapter? externalNames
  let boxedExternalNames := artifact.externalNames.filter (boxedSource? · |>.isSome)
  if boxedExternalNames.isEmpty then
    return artifact
  let mut rawDeclarations : Array (LCNF.Decl .impure) := #[]
  let mut recoveredRawDeclarations : Array (LCNF.Decl .impure) := #[]
  let environment ← getEnv
  for boxedName in boxedExternalNames do
    let some rawName := boxedSource? boxedName |
      throwError "internal error: boxed external `{boxedName}` lost its source declaration"
    let declaration ← match artifact.program.findDecl? rawName with
      | some declaration => pure declaration
      | none => do
          let some signature ← LCNF.getImpureSignature? rawName |
            throwError
              "boxed external `{boxedName}` has no captured or environment signature for `{rawName}`"
          let data := getExternAttrData? environment rawName |>.getD
            { entries := [.opaque] }
          let declaration := capturedExternDecl signature data
          recoveredRawDeclarations := recoveredRawDeclarations.push declaration
          pure declaration
    match declaration.value with
    | .code _ =>
        throwError "boxed external `{boxedName}` names local raw declaration `{rawName}`"
    | .extern _ => pure ()
    unless rawDeclarations.any (·.name == rawName) do
      rawDeclarations := rawDeclarations.push declaration
  let generated ← withoutModifyingEnv <|
    LCNF.CompilerM.run (LCNF.addBoxedVersions rawDeclarations) (phase := .impure)
  let mut replacements : Array (LCNF.Decl .impure) := #[]
  for boxedName in boxedExternalNames do
    let some declaration := generated.find? (·.name == boxedName) |
      throwError
        "Lean ExplicitBoxing did not regenerate required external adapter `{boxedName}`"
    match declaration.value with
    | .code _ => replacements := replacements.push declaration
    | .extern _ =>
        throwError "Lean ExplicitBoxing regenerated `{boxedName}` as an external declaration"
  let decls := artifact.program.decls.map (fun declaration =>
    replacements.find? (·.name == declaration.name) |>.getD declaration) ++
      recoveredRawDeclarations
  let program : Fir.LeanIR.ImpureProgram := { decls }
  let externalNames := rawDeclarations.foldl (init := artifact.externalNames) fun names raw =>
    if names.contains raw.name then names else names.push raw.name
  return { artifact with
    program
    externalNames := externalNames.filter (!boxedExternalNames.contains ·)
    forms := Fir.Validation.Lcnf.collectForms program }

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
Keep Lean-generated adapters for extern declarations local, but restore the
original declarations themselves to their native boundary. Asking Lean to
compile an extern is how `ExplicitBoxing` derives its exact `_boxed` adapter;
the extern's Lean fallback body is not part of the application's source
closure and must not make its implementation dependencies discoverable.
-/
private def restoreCapturedExternBoundaries (environment : Environment)
    (decls : Array (LCNF.Decl .impure)) : Array (LCNF.Decl .impure) :=
  decls.map fun decl =>
    if isExtern environment decl.name then
      let data := getExternAttrData? environment decl.name |>.getD { entries := [.opaque] }
      { decl with value := .extern data, inlineAttr? := none }
    else
      decl

/--
Compile one source unit and build its artifact from the declaration groups
observed by the final-impure identity pass.  Ordinary `collectUsedDecls`
continues to supply imported signatures, but a captured body always wins over
an external stub with the same generated name.
-/
private def compileEntryFinalCaptured (entry : Name) (dependencies : Array Name := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  -- Internalization grows the root set and recompiles the complete synthetic
  -- unit. Generated specialization and closed-term names are only meaningful
  -- within one such compiler run: retaining either the cache or earlier
  -- captured groups can pair a regenerated name with a stale ABI.
  resetFinalImpureCapture
  let roots := #[entry] ++ dependencies
  let environment ← getEnv
  let moduleIndices := roots.foldl (init := #[]) fun indices root =>
    match environment.getModuleIdxFor? root with
    | some index => if indices.contains index then indices else indices.push index
    | none => indices
  resetCompilerCaches moduleIndices roots
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
  localDecls := restoreCapturedExternBoundaries environment localDecls
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

private def discoveredOrdinarySourceRoots (artifact : Fir.Validation.Lcnf.Artifact)
    (retainedExternalNames : Array String) (excluded : Array Name) :
    CoreM (Array Name) := do
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

private def discoveredFinalSourceRoots (artifact : Fir.Validation.Lcnf.Artifact)
    (retainedExternalNames : Array String) (excluded : Array Name) :
    CoreM (Array SourceCompilationRoot) := do
  let env ← getEnv
  artifact.externalNames.foldlM (init := #[]) fun additions name => do
    if retainedExternalNames.contains name.toString then
      return additions
    else
      let some root ← sourceCompilationRoot? env name | return additions
      if excluded.contains root.name then return additions
      return addSourceCompilationRoot additions root

private partial def compileEntrySeparatelyInternalizedAux (entry : Name)
    (retainedExternalNames : Array String)
    (entryArtifact : Fir.Validation.Lcnf.Artifact) (dependencies : Array Name) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  if dependencies.isEmpty then
    return entryArtifact
  let dependencyArtifact ← withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry dependencies[0]!
      (dependencies.extract 1 dependencies.size)
  let additions ← discoveredOrdinarySourceRoots dependencyArtifact retainedExternalNames
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
  let dependencies ← discoveredOrdinarySourceRoots entryArtifact retainedExternalNames #[entry]
  compileEntrySeparatelyInternalizedAux entry retainedExternalNames entryArtifact dependencies

private def sourceRootCovers (available required : SourceCompilationRoot) : Bool :=
  available.name == required.name &&
    required.companions.all available.companions.contains

private def enqueueSourceRoot (completed pending : Array SourceCompilationRoot)
    (root : SourceCompilationRoot) : Array SourceCompilationRoot :=
  if completed.any (sourceRootCovers · root) then pending
  else addSourceCompilationRoot pending root

private def compileIndividualSourceRoot (root : SourceCompilationRoot) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  Core.prependError m!"Failed to compile individual source root `{root.name}`" do
    withoutModifyingEnv do
      resetFinalImpureCapture
      LCNF.addPass ``finalImpureCaptureInstaller
      compileEntryFinalCaptured root.name root.companions

private partial def compileEntryIndividuallyInternalizedAux (entry : Name)
    (retainedExternalNames : Array String)
    (completed pending : Array SourceCompilationRoot)
    (artifacts : Array Fir.Validation.Lcnf.Artifact) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let some root := pending[0]? | do
    let merged ← mergeSeparatelyCompiledArtifacts entry artifacts
    match pruneUnreachableDeclarations merged with
    | .ok artifact => return artifact
    | .error message => throwError message
  let pending := pending.extract 1 pending.size
  let artifact ← compileIndividualSourceRoot root
  let excluded := completed.map (·.name) ++ pending.map (·.name)
  let discoveries ← discoveredFinalSourceRoots artifact retainedExternalNames excluded
  /- A specialization is attributed to its source caller plus the generic
  callee needed to regenerate it. If the caller was just compiled without that
  companion, discard this incomplete unit and immediately rebuild the exact
  source group; otherwise merging both caller bodies would be ambiguous. -/
  if let some enhancement := discoveries.find? fun discovery =>
      discovery.name == root.name && !sourceRootCovers root discovery then
    let enhanced := { root with
      companions := enhancement.companions.foldl addUniqueName root.companions }
    return ← compileEntryIndividuallyInternalizedAux entry retainedExternalNames
      completed (#[enhanced] ++ pending) artifacts
  let completed := completed.push root
  let pending := discoveries.foldl (enqueueSourceRoot completed) pending
  compileEntryIndividuallyInternalizedAux entry retainedExternalNames
    completed pending (artifacts.push artifact)

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
  let sourceRoots := groups.flatMap (·.declNames)
  resetCompilerCaches #[moduleIndex] sourceRoots
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
  if let some sourceRoot ← sourceDeclarationAncestor? environment name then
    if let some moduleIndex := environment.getModuleIdxFor? sourceRoot then
      return some (environment.header.moduleNames[moduleIndex]!, sourceRoot)
  /-
  A private source caller is absent from an ordinary imported environment, but
  its exact module remains encoded by Lean in the specialization provenance.
  Prefer caller candidates over the generated name itself: the latter keeps
  the private prefix of the generic callee and can therefore name the wrong
  module. The private module replay imports the private environment and finds
  this exact source root in its postponed declaration groups.
  -/
  for candidate in
      Fir.Wasm.Emit.CompilerPrivate.specializationCallerCandidates name do
    let some moduleName :=
      Fir.Wasm.Emit.CompilerPrivate.privateNameModule? candidate | continue
    unless environment.getModuleIdx? moduleName |>.isSome do continue
    return some (moduleName, candidate)
  return none

/-- Resolve an ordinary public source entry even when its module postponed
final-LCNF compilation and therefore exported no impure signature. Generated
helpers are excluded because they live in `extraConstNames`, not `constNames`;
dependency discovery continues to use the stricter signature-aware resolver. -/
private def postponedEntryModuleFor? (environment : Environment) (entry : Name) :
    Option (Name × Name) := do
  let moduleIndex ← environment.getModuleIdxFor? entry
  guard <| environment.header.moduleData[moduleIndex]!.constNames.contains entry
  return (environment.header.moduleNames[moduleIndex]!, entry)

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
external declarations. The explicit module and source-root parameters let a
package façade remain independent of the source module's native IR artifacts.
-/
def compileEntryModuleWiseInternalizedFrom
    (moduleName sourceRoot entry : Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let environment ← getEnv
  compileEntryDeferredModulesInternalizedAux entry retainedExternalNames environment
    #[(moduleName, sourceRoot, true)] #[] #[]

/-- Derive an imported entry's source module, then replay its postponed final LCNF. -/
def compileEntryModuleWiseInternalized (entry : Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let environment ← getEnv
  let sourceModule? ← sourceModuleFor? environment entry
  let some (moduleName, sourceRoot) :=
      sourceModule?.orElse fun _ => postponedEntryModuleFor? environment entry |
    throwError "entry `{entry}` has no source module"
  compileEntryModuleWiseInternalizedFrom moduleName sourceRoot entry
    retainedExternalNames

/--
Compile several public entries by replaying each entry's recursively required
postponed source modules, then link the independently captured module closures.
This is the multi-entry counterpart of `compileEntryModuleWiseInternalized`.
It preserves the source-module boundary (including private specializations)
while exposing several logical roots from one physical Wasm package.
-/
def compileEntriesModuleWiseInternalized (entries : Array Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let some entry := entries[0]? |
    throwError "module-wise multi-entry capture requires at least one entry"
  unless (entries.foldl (init := #[]) addUniqueName).size == entries.size do
    throwError "module-wise multi-entry capture received duplicate entries: {entries}"
  let artifacts ← entries.mapM fun root =>
    compileEntryModuleWiseInternalized root retainedExternalNames
  let artifact ← mergeSeparatelyCompiledArtifacts entry artifacts
  for root in entries do
    let some declaration := artifact.program.findDecl? root |
      throwError "module-wise multi-entry capture did not contain root `{root}`"
    if artifact.externalNames.contains declaration.name then
      throwError "module-wise multi-entry root `{root}` remained external"
  match pruneUnreachableDeclarations artifact (entries.extract 1 entries.size) with
  | .ok artifact => return artifact
  | .error message => throwError message

/--
Capture an entry at the same source-unit boundary Lean made available, then
compile every recursively discovered ordinary imported source root as its own
LCNF unit. A module built with `compiler.postponeCompile=true` must first replay
its exact deferred declaration groups: its private/closed helpers and sibling
signatures are module-owned and cannot be regenerated faithfully as unrelated
one-declaration units. Prebuilt modules without deferred groups retain the
individual-root path, which avoids synthesizing a larger cross-module compiler
unit around macro-inlined helpers.
-/
def compileEntryIndividuallyInternalized (entry : Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let environment ← getEnv
  let signatureModule? ← sourceModuleFor? environment entry
  let sourceModule? := signatureModule?.orElse
    fun _ => postponedEntryModuleFor? environment entry
  let moduleArtifact? ← match sourceModule? with
    | some (moduleName, sourceRoot) =>
        compileDeferredModuleFinalCaptured moduleName sourceRoot
    | none => pure none
  let some moduleArtifact := moduleArtifact? |
    return ← Core.prependError
      m!"Entry `{entry}` has no deferred source module ({repr sourceModule?})" do
        compileEntryIndividuallyInternalizedAux entry retainedExternalNames
          #[] #[{ name := entry }] #[]
  let moduleArtifact ← match pruneUnreachableDeclarations moduleArtifact with
    | .ok artifact => pure artifact
    | .error message => throwError message
  let completed : Array SourceCompilationRoot :=
    moduleArtifact.program.decls.filterMap fun declaration =>
      if moduleArtifact.externalNames.contains declaration.name then none
      else some { name := declaration.name }
  let pending ← discoveredFinalSourceRoots moduleArtifact retainedExternalNames
    (completed.map (·.name))
  compileEntryIndividuallyInternalizedAux entry retainedExternalNames
    completed pending #[moduleArtifact]

/--
Compile several public entries through their exact individual source-unit
closures, merge declarations only when their independently recovered bodies
agree, and retain every requested entry. This is the multi-entry counterpart
of `compileEntryIndividuallyInternalized`; it avoids synthesizing one larger
compiler unit around roots that Lean originally compiled in ordinary source
modules.
-/
def compileEntriesIndividuallyInternalized (entries : Array Name)
    (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let some entry := entries[0]? |
    throwError "individual-source multi-entry capture requires at least one entry"
  unless (entries.foldl (init := #[]) addUniqueName).size == entries.size do
    throwError "individual-source multi-entry capture received duplicate entries: {entries}"
  let artifacts ← entries.mapM fun root =>
    compileEntryIndividuallyInternalized root retainedExternalNames
  let artifact ← mergeSeparatelyCompiledArtifacts entry artifacts
  for root in entries do
    let some declaration := artifact.program.findDecl? root |
      throwError "individual-source multi-entry capture did not contain root `{root}`"
    if artifact.externalNames.contains declaration.name then
      throwError "individual-source multi-entry root `{root}` remained external"
  match pruneUnreachableDeclarations artifact (entries.extract 1 entries.size) with
  | .ok artifact => return artifact
  | .error message => throwError message

/--
Compile an entry and its recursively discovered source dependencies as one
compiler unit, obtaining that unit from the exact final-impure SCCs observed
before Lean's IR handoff. Dependency discovery compiles only each new frontier;
one final compilation of the complete root set owns all generated binder
identifiers and retains private specializations as ordinary local declarations.
-/
private partial def discoverFinalCapturedRoots (roots frontier : Array Name)
    (retainedExternalNames : Array String) :
    CoreM (Array Name × Option Fir.Validation.Lcnf.Artifact) := do
  let some entry := frontier[0]? | return (roots, none)
  let artifact ← withoutModifyingEnv <|
    compileEntryFinalCaptured entry (frontier.extract 1 frontier.size)
  let discovered ← discoveredFinalSourceRoots artifact retainedExternalNames roots
  let additions := discovered.foldl (init := #[]) fun names root =>
    (#[root.name] ++ root.companions).foldl (fun names name =>
      if roots.contains name then names else addUniqueName names name) names
  if additions.isEmpty then
    return (roots, if roots == frontier then some artifact else none)
  discoverFinalCapturedRoots (roots ++ additions) additions retainedExternalNames

private partial def compileEntryFinalCapturedInternalizedAux (entry : Name)
    (roots frontier : Array Name) (retainedExternalNames : Array String) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  let (roots, completeArtifact?) ←
    discoverFinalCapturedRoots roots frontier retainedExternalNames
  let artifact ← match completeArtifact? with
    | some artifact => pure artifact
    | none => withoutModifyingEnv <|
        compileEntryFinalCaptured entry (roots.extract 1 roots.size)
  let discovered ← discoveredFinalSourceRoots artifact retainedExternalNames roots
  let additions := discovered.foldl (init := #[]) fun names root =>
    (#[root.name] ++ root.companions).foldl (fun names name =>
      if roots.contains name then names else addUniqueName names name) names
  if additions.isEmpty then
    return artifact
  compileEntryFinalCapturedInternalizedAux entry (roots ++ additions) additions
    retainedExternalNames

def compileEntryFinalCapturedInternalized (entry : Name)
    (dependencies : Array Name := #[]) (retainedExternalNames : Array String := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := withoutModifyingEnv do
  resetFinalImpureCapture
  LCNF.addPass ``finalImpureCaptureInstaller
  let roots := #[entry] ++ dependencies
  compileEntryFinalCapturedInternalizedAux entry roots roots retainedExternalNames

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

private def sourceOwnersCallingUnresolvedDeclarations
    (artifact : Fir.Validation.Lcnf.Artifact)
    (retainedExternalNames : Array String) :
    CoreM (Array SourceCompilationRoot) := do
  let environment ← getEnv
  let unresolvedSourceNames ← artifact.externalNames.filterM fun name => do
    if retainedExternalNames.contains name.toString then return false
    return (← sourceCompilationRoot? environment name).isSome
  if unresolvedSourceNames.isEmpty then return #[]
  artifact.program.decls.foldlM (init := #[]) fun roots declaration => do
    if artifact.externalNames.contains declaration.name then return roots
    let references := match declaration.value with
      | .code code => collectCodeReferences #[] code
      | .extern _ => #[]
    unless references.any unresolvedSourceNames.contains do return roots
    /- A generated caller may live below an unrelated private implementation
    namespace while its `._at_.` suffix records the real source declaration
    that owns the specialization. Reuse the same compiler-provenance resolver
    as direct external discovery instead of relying only on name ancestry. -/
    let some source ← sourceCompilationRoot? environment declaration.name |
      return roots
    return addSourceCompilationRoot roots source

private partial def importedClosureReachesAny (targets : Array Name)
    (pending : List Name) (seen : NameSet := {}) : CoreM Bool := do
  let some name := pending.head? | return false
  let pending := pending.tail!
  if targets.contains name then return true
  if seen.contains name then
    return ← importedClosureReachesAny targets pending seen
  let seen := seen.insert name
  let references ← match ← LCNF.getLocalImpureDecl? name with
    | some declaration => pure <| match declaration.value with
      | .code code => collectCodeReferences #[] code
      | .extern _ => #[]
    | none => pure #[]
  importedClosureReachesAny targets (references.toList ++ pending) seen

private partial def sourceValueReachesAny (environment : Environment)
    (targets : Array Name) (pending : List Name) (seen : NameSet := {}) : Bool :=
  match pending with
  | [] => false
  | name :: pending =>
    if targets.contains name then true
    else if seen.contains name then
      sourceValueReachesAny environment targets pending seen
    else
      let seen := seen.insert name
      let references := match environment.find? name with
        | some declaration => match declaration.value? (allowOpaque := true) with
          | some value => value.getUsedConstants
          | none => #[]
        | none => #[]
      sourceValueReachesAny environment targets (references.toList ++ pending) seen

private partial def sourceRuntimeValueClosure (environment : Environment)
    (pending : List Name) (seen : NameSet := {})
    (names : Array Name := #[]) : CoreM (Array Name) := do
  let some name := pending.head? | return names
  let pending := pending.tail!
  if seen.contains name then
    return ← sourceRuntimeValueClosure environment pending seen names
  let seen := seen.insert name
  unless environment.constants.contains name && !isExtern environment name &&
      (← sourceDeclarationIsCompilable environment name) do
    return ← sourceRuntimeValueClosure environment pending seen names
  let references := match environment.find? name with
    | some declaration => match declaration.value? (allowOpaque := true) with
      | some value => value.getUsedConstants
      | none => #[]
    | none => #[]
  sourceRuntimeValueClosure environment (references.toList ++ pending)
    seen (addUniqueName names name)

/--
Find missing imported generated specializations whose source caller is
reachable from the source roots about to be recompiled, but whose body was not
captured at the current source boundary.

Classic (non-`module`) Lean libraries export these generated declarations as
native object/IR symbols plus final-LCNF signatures. A fresh source overlay
cannot resolve such a symbol if an inline imported body refers to it. Lean's
per-module `extraConstNames` index and specializer `._at_.` provenance identify
the exact source caller and generic callee needed to regenerate it. Adding that
pair to the same source unit mirrors the original compiler ownership boundary.
Do not add every nested specialization recorded for that caller: Lean already
regenerates those while compiling the source root, and forcing their generic
callees into the root set can suppress the nested specialization itself.
-/
private def sourceSpecializationBridgeRoots (environment : Environment)
    (artifact : Fir.Validation.Lcnf.Artifact)
    (roots : Array SourceCompilationRoot) :
    CoreM (Array SourceCompilationRoot) := do
  let pending := roots.foldl (init := []) fun pending root =>
    (root.name :: root.companions.toList) ++ pending
  let sourceNames ← sourceRuntimeValueClosure environment pending
  let moduleIndices := sourceNames.foldl (init := #[]) fun indices name =>
    match environment.getModuleIdxFor? name with
    | some index => if indices.contains index then indices else indices.push index
    | none => indices
  let mut bridges : Array SourceCompilationRoot := #[]
  for moduleIndex in moduleIndices do
    for generated in environment.header.moduleData[moduleIndex]!.extraConstNames do
      if (artifact.program.findDecl? generated |>.isSome) &&
          !artifact.externalNames.contains generated then
        continue
      if (← LCNF.getLocalImpureDecl? generated).isSome then continue
      let callers :=
        Fir.Wasm.Emit.CompilerPrivate.specializationCallerCandidates generated
      let some caller := callers.find? sourceNames.contains | continue
      /- A nested specialization records its generated immediate caller before
      the real source ancestor in its sequence of `._at_.` contexts.
      Recompiling that ancestor regenerates the entire nested chain; adding the
      nested generic callee as an explicit companion can instead suppress
      Lean's ordinary inner specialization. Only a generated edge with one
      caller context crosses this source-unit boundary. -/
      unless callers.size == 1 do continue
      unless ← sourceDeclarationIsCompilable environment caller do continue
      let mut companions : Array Name := #[]
      for callee in
          Fir.Wasm.Emit.CompilerPrivate.specializationCalleeCandidates generated do
        unless environment.constants.contains callee do continue
        if isExtern environment callee then continue
        unless ← sourceDeclarationIsCompilable environment callee do continue
        companions := addUniqueName companions callee
      bridges := addSourceCompilationRoot bridges { name := caller, companions }
  return bridges

private partial def addSourceBridgeRoots (environment : Environment)
    (unresolvedSourceNames sourceTargetNames : Array Name)
    (roots : Array SourceCompilationRoot)
    (index : Nat := 0) : CoreM (Array SourceCompilationRoot) := do
  if h : index < roots.size then
    let root := roots[index]
    let usedConstants := match environment.find? root.name with
      | some declaration => match declaration.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      | none => #[]
    let mut roots := roots
    for dependency in usedConstants do
      let importedReach ← importedClosureReachesAny unresolvedSourceNames [dependency]
      let sourceReach :=
        sourceValueReachesAny environment sourceTargetNames [dependency]
      unless importedReach || sourceReach do
        continue
      let some source ← sourceDeclarationAncestor? environment dependency |
        continue
      unless ← sourceDeclarationIsCompilable environment source do continue
      roots := addSourceCompilationRoot roots { name := source }
    addSourceBridgeRoots environment unresolvedSourceNames sourceTargetNames
      roots (index + 1)
  else
    return roots

/--
Close the source dependencies left by an exact module-wise replay through one
fresh final-LCNF compiler unit. The replayed module's declarations keep their
native specialization/SCC identities; only unresolved declarations from
prebuilt modules without postponed groups are recompiled. Explicit runtime
frontier names remain external.
-/
def internalizeFinalDependencies (artifact : Fir.Validation.Lcnf.Artifact)
    (retainedExternalNames : Array String := #[])
    (retainedRoots : Array Name := #[]) :
    CoreM Fir.Validation.Lcnf.Artifact := do
  /- An unresolved generated declaration can belong to a source caller that is
  already local. Do not exclude that caller here: the coherent source-unit
  overlay below is what replaces its stale imported body. -/
  let directRoots ← discoveredFinalSourceRoots artifact retainedExternalNames #[]
  let callerRoots ←
    sourceOwnersCallingUnresolvedDeclarations artifact retainedExternalNames
  let roots := callerRoots.foldl (addSourceCompilationRoot) directRoots
  let environment ← getEnv
  let unresolvedSourceNames ← artifact.externalNames.filterM fun name => do
    if retainedExternalNames.contains name.toString then return false
    return (← sourceCompilationRoot? environment name).isSome
  let sourceTargetNames := directRoots.map (·.name)
  let roots ← addSourceBridgeRoots environment unresolvedSourceNames
    sourceTargetNames roots
  let specializationRoots ← sourceSpecializationBridgeRoots environment
    artifact roots
  let roots := specializationRoots.foldl addSourceCompilationRoot roots
  let dependencyNames := roots.foldl (init := #[]) fun names root =>
    (#[root.name] ++ root.companions).foldl addUniqueName names
  let some dependencyEntry := dependencyNames[0]? | return artifact
  let dependencies ← Core.prependError
      m!"Failed to rebuild unresolved source closure {dependencyNames}" do
    compileEntryFinalCapturedInternalized dependencyEntry
      (dependencyNames.extract 1 dependencyNames.size) retainedExternalNames
  /- The freshly compiled dependency unit is an atomic source closure. An
  imported caller can reference a bootstrap-generated specialization whose
  exact name is not regenerated by the current compiler; keeping that caller
  while merely appending its new closure would leave the stale reference
  reachable. Let the coherent new unit replace every declaration it supplies,
  while declarations it still treats as external continue to resolve from the
  original artifact. -/
  let replacementNames := dependencies.program.decls.filterMap fun declaration =>
    if dependencies.externalNames.contains declaration.name then none
    else some declaration.name
  let retainedDecls := artifact.program.decls.filter fun declaration =>
    !replacementNames.contains declaration.name
  let retainedProgram : Fir.LeanIR.ImpureProgram := { decls := retainedDecls }
  let retainedArtifact := { artifact with
    program := retainedProgram
    externalNames := artifact.externalNames.filter (!replacementNames.contains ·)
    forms := Fir.Validation.Lcnf.collectForms retainedProgram }
  let merged ← mergeSeparatelyCompiledArtifacts artifact.entry
    #[retainedArtifact, dependencies]
  match pruneUnreachableDeclarations merged retainedRoots with
  | .ok merged => return merged
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
  let additions ← discoveredOrdinarySourceRoots artifact retainedExternalNames
    (#[entry] ++ dependencies)
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

private def compileModuleArtifactWithExportsUsing
    (source : Fir.Validation.Lcnf.Artifact)
    (exports : Array Name)
    (lowerProgram : Fir.LeanIR.ImpureProgram →
      Except Fir.Wasm.SupportedLoweringError Fir.Wasm.Module)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) := do
  if exports.isEmpty then
    return .error (.manifest "Wasm source lowering requires at least one export")
  unless (exports.foldl (init := #[]) addUniqueName).size == exports.size do
    return .error (.manifest s!"Wasm source lowering received duplicate exports: {exports}")
  unless exports.contains source.entry do
    return .error (.manifest s!"Wasm exports do not contain source entry {source.entry}")
  let module ←
    match lowerProgram source.program with
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

def compileModuleArtifactWithExports (source : Fir.Validation.Lcnf.Artifact)
    (exports : Array Name)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) :=
  compileModuleArtifactWithExportsUsing source exports Fir.Wasm.lowerSupported transform

/--
Lower an already captured compiler artifact with its canonical entry as the
only public source export, apply one symbolic-module pipeline, and encode the
result.
-/
def compileModuleArtifactWith (source : Fir.Validation.Lcnf.Artifact)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) :=
  compileModuleArtifactWithExports source #[source.entry] transform

/--
Lower a captured source program whose public input boundary cannot contain
pre-existing Lean closures, then retain only closure-dispatch targets allocated
by the program's own final-LCNF `pap` nodes.

This is an explicit package capability rather than the generic default: code
which accepts an opaque closure from its host must keep using
`compileModuleArtifactWithExports`. The closed module derives its dispatch and
descriptor tables from exactly the retained closure operations; their indices
remain module-local and no opaque closure ID crosses this boundary. The final
structural pass validates that no non-source target survived before the
caller's resident-link transform runs.
-/
def compileModuleArtifactWithClosedClosuresAndExports
    (source : Fir.Validation.Lcnf.Artifact) (exports : Array Name)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) :=
  let targets := Fir.Wasm.Emit.ClosureDispatch.partialApplicationTargets source.program
  compileModuleArtifactWithExportsUsing source exports
      (fun program => Fir.Wasm.lowerSupportedWithClosureTargets program targets) fun module => do
    let (module, _) ←
      Fir.Wasm.Emit.ClosureDispatch.pruneClosedProgram source.program module
        |>.mapError fun error =>
          CompileError.manifest
            s!"closed closure-dispatch pruning failed: {repr error}"
    transform module

/-- Single-entry form of `compileModuleArtifactWithClosedClosuresAndExports`. -/
def compileModuleArtifactWithClosedClosures
    (source : Fir.Validation.Lcnf.Artifact)
    (transform : Fir.Wasm.Module → Except CompileError Fir.Wasm.Module) :
    CoreM (Except CompileError ModuleArtifact) :=
  compileModuleArtifactWithClosedClosuresAndExports source #[source.entry] transform

/-- Lower and encode one source artifact with a closed heap-closure boundary. -/
def compileClosedClosureModuleArtifact (source : Fir.Validation.Lcnf.Artifact) :
    CoreM (Except CompileError ModuleArtifact) :=
  compileModuleArtifactWithClosedClosures source .ok

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
  | .array _, kind
  | .seq _, kind
  | .boxed _, kind
  | .ctor .., kind => kind.isObjectLike
  | _, _ => false

/-- Normalize a backend-neutral validation value to the checked parameter ABI.
The validation protocol represents `Bool` as a tagged object, while Lean 4.33
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
    (resultSchema : Fir.Validation.ValidationSchema)
    (argumentAliases : Array Fir.Validation.ArgumentAlias := #[])
    (nestedArgumentAliases : Array Fir.Validation.NestedArgumentAlias := #[]) :
    Except CompileError Artifact := do
  let function ← Manifest.entryFunction artifact.module entry |>.mapError .manifest
  let resultKind ← Manifest.entryResultKind entry function |>.mapError .manifest
  unless validationSchemaAcceptsAbiKind resultSchema resultKind do
    throw (.manifest s!"result schema {repr resultSchema} does not match ABI kind {repr resultKind}")
  let paramKinds := function.params.map (·.snd)
  unless paramKinds.size == argSchemas.size do
    throw (.manifest
      s!"entry {entry} expects {paramKinds.size} argument schemas, got {argSchemas.size}")
  let (runtime, args) ← Fir.Validation.Lcnf.encodeArgs argSchemas data argumentAliases
    nestedArgumentAliases
    |>.mapError .manifest
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
    (dependencies : Array Name := #[])
    (argumentAliases : Array Fir.Validation.ArgumentAlias := #[])
    (nestedArgumentAliases : Array Fir.Validation.NestedArgumentAlias := #[]) :
    CoreM (Except CompileError Artifact) := do
  let result ← compileModule entry dependencies
  return result.bind fun artifact =>
    artifact.withValidationInvocation artifactName entry entry argSchemas data resultSchema
      argumentAliases nestedArgumentAliases

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

private def ModuleArtifact.functionInventory (artifact : ModuleArtifact) :
    Array Name × Array Name × Array Name :=
  let functions := artifact.module.functions.map (·.name)
  let sourceFunctions := artifact.source.program.decls.filterMap fun declaration =>
    match declaration.value with
    | .code _ => some declaration.name
    | .extern _ => none
  let retainedSourceFunctions := sourceFunctions.filter functions.contains
  let residentHelpers := functions.filter fun name =>
    !retainedSourceFunctions.contains name
  (functions, retainedSourceFunctions, residentHelpers)

/--
Return the exact emitter-final function inventory consumed by generic Wasm
function-index tooling. This inventory is meaningful only for `artifact.bytes`,
whose defined functions have the same order as `artifact.module.functions`.
-/
def ModuleArtifact.functionInventoryJson (artifact : ModuleArtifact) : Json :=
  let (functions, sourceFunctions, residentHelpers) := artifact.functionInventory
  Json.mkObj [
    ("schemaVersion", "fir.wasm.emitter-function-inventory/v1"),
    ("artifact", Json.mkObj [
      ("byteLength", artifact.bytes.size),
      ("functionImports", artifact.module.imports.size),
      ("definedFunctions", functions.size)]),
    ("functions", Json.arr <| functions.map fun name => name.toString),
    ("sourceFunctions", Json.arr <| sourceFunctions.map fun name => name.toString),
    ("residentHelpers", Json.arr <| residentHelpers.map fun name => name.toString)]

/-- Write only the opt-in exact emitter-final function inventory. -/
def ModuleArtifact.writeFunctionInventory (artifact : ModuleArtifact)
    (path : System.FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (artifact.functionInventoryJson.compress ++ "\n")

private def compactInstructionOriginJson (origin : InstructionOrigin) : Json :=
  Json.arr #[
    origin.offset,
    origin.encodedSize,
    Json.arr <| origin.opcode.map fun byte => byte.toNat]

/--
Return opt-in, release-byte-checked symbolic instruction provenance for a
compiled source artifact. The ordinary artifact writer remains unchanged.
-/
def ModuleArtifact.instructionOriginsJson (artifact : ModuleArtifact) :
    Except CompileError Json := do
  let encoding ← match Fir.Wasm.Emit.encodeWithOrigins artifact.module with
    | .ok encoding => pure encoding
    | .error error => throw (.encoding error)
  unless encoding.bytes == artifact.bytes do
    throw (.encoding (.invalidOriginTrace
      "origin encoding changed the ordinary artifact bytes"))
  let (functions, retainedSourceFunctions, residentHelpers) := artifact.functionInventory
  let functionImports := artifact.module.imports.size
  /-
  `traceOrigins` emits defined functions in module order and symbolic
  instructions in preorder. Consume that stream once: filtering the complete
  origin array for every function makes this diagnostic quadratic.
  -/
  let mut originCursor := 0
  let mut functionRows : Array Json := #[]
  for ordinal in [:functions.size] do
    let name := functions[ordinal]!
    let functionIndex := functionImports + ordinal
    let mut origins : Array Json := #[]
    while h : originCursor < encoding.origins.size do
      let origin := encoding.origins[originCursor]
      if origin.functionIndex != functionIndex then break
      origins := origins.push (compactInstructionOriginJson origin)
      originCursor := originCursor + 1
    let kind := if retainedSourceFunctions.contains name then
        "lean-source"
      else if residentHelpers.contains name then
        "resident-helper"
      else
        "unclassified-definition"
    functionRows := functionRows.push <| Json.mkObj [
      ("index", functionIndex),
      ("name", name.toString),
      ("kind", kind),
      ("public", artifact.module.exports.contains name),
      ("source", s!"fir-wasm-origin/{functionIndex}/{name}"),
      ("origins", Json.arr origins)]
  unless originCursor == encoding.origins.size do
    throw (.encoding (.invalidOriginTrace
      "instruction origins are not ordered by defined function index"))
  return Json.mkObj [
    ("schema", "fir.wasm.instruction-origins/v1"),
    ("artifact", Json.mkObj [
      ("byteLength", artifact.bytes.size),
      ("functionImports", functionImports),
      ("definedFunctions", functions.size),
      ("originCount", encoding.origins.size)]),
    ("encoding", Json.mkObj [
      ("functionOrder", "defined-function-order"),
      ("originOrder", "symbolic-preorder"),
      ("originRow", Json.arr #["absoluteOpcodeOffset", "encodedSize", "opcodeBytes"])]),
    ("functions", Json.arr functionRows)]

/-- Write only the opt-in symbolic instruction-origin table. -/
def ModuleArtifact.writeInstructionOrigins (artifact : ModuleArtifact)
    (path : System.FilePath) : IO (Except CompileError Unit) := do
  let origins ← match artifact.instructionOriginsJson with
    | .ok origins => pure origins
    | .error error => return .error error
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (origins.compress ++ "\n")
  return .ok ()

end Fir.Wasm.Emit.Source
