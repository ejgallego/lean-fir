import Fir.Wasm.Emit.ResidentPrettyFormat
import Fir.Wasm.Emit.ResidentFloat
import Fir.Wasm.Emit.ResidentDeadCode
import Fir.Wasm.Emit.ResidentArray
import Fir.Wasm.Emit.ResidentNatMod
import Fir.Wasm.Emit.ResidentNatShift
import Fir.Wasm.Emit.ResidentUSize
import Illuminate.Animation.FirLive

namespace IlluminateFirNative.Compile

open Lean
open Lean.Compiler

private def arrayGetBangName : Name := ``Array.get!InternalBorrowed

private def arrayGetName : Name := ``Array.getInternalBorrowed

private def arrayGetBangOwnedName : Name := ``Array.get!Internal

private def arrayUgetBorrowedName : Name := ``Array.ugetBorrowed

private def isArrayGetName (name : Name) : Bool :=
  name == arrayGetBangName || name == arrayGetName || name == arrayGetBangOwnedName ||
    name == arrayUgetBorrowedName

private def generatedCallerFamily (caller family : String) (redArg := false) : Bool :=
  caller.contains family && caller.contains ".spec_" &&
    (!redArg || caller.endsWith "._redArg")

private def expectedArrayGetCaller (target caller : Name) : Bool :=
  let suffix := caller.toString
  if target == arrayGetBangName then
    suffix.endsWith "Illuminate.AnimationPlayer.actionAt" ||
      suffix.endsWith "Illuminate.AnimationPlayer.tick" ||
      generatedCallerFamily suffix "Illuminate.AnimationPlayer.parameterUpdates" true ||
      generatedCallerFamily suffix "Illuminate.AnimationPlayer.findCurrentStep" true ||
      generatedCallerFamily suffix "Illuminate.AnimationPlayer.findCurrentStepFrom" true
  else if target == arrayGetName then
    suffix.endsWith "Illuminate.AnimationPlayer.selectPlayerSegment" ||
      suffix.endsWith "Illuminate.AnimationPlayer.parameterUpdates" ||
      suffix.endsWith "Illuminate.AnimationPlayer.advance" ||
      suffix.endsWith "Illuminate.AnimationPlayer.statusForPlaying" ||
      suffix.endsWith "Illuminate.AnimationPlayer.loopAt" ||
      suffix.endsWith "Illuminate.AnimationPlayer.tick" ||
      suffix.endsWith "Illuminate.AnimationPlayer.findStepEnd" ||
      generatedCallerFamily suffix "Illuminate.AnimationPlayer.findPlayerSegment" ||
      generatedCallerFamily suffix "Illuminate.AnimationPlayer.findCrossedPauseTo" true
  else if target == arrayGetBangOwnedName then
    suffix.endsWith "Illuminate.AnimationPlayer.tick"
  else if target == arrayUgetBorrowedName then
    generatedCallerFamily suffix "Illuminate.AnimationPlayer.validatePrepared" ||
      generatedCallerFamily suffix
        "Illuminate.AnimationPlayer.validateSelectionAnimation"
  else
    false

mutual

private partial def refineArrayGetCalls (caller : Name) :
    LCNF.Code .impure → Except String (LCNF.Code .impure × Array (Name × Name))
  | .let decl continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      let mut decl := decl
      let mut sites := sites
      if let .fap name _ := decl.value then
        if isArrayGetName name then
          unless expectedArrayGetCaller name caller do
            throw s!"unexpected monomorphic {name} caller {caller}"
          unless decl.type == LCNF.ImpureType.tobject do
            throw s!"{name} call in {caller} no longer binds a tobject"
          return (.let { decl with type := LCNF.ImpureType.object } continuation,
            sites.push (name, caller))
      return (.let decl continuation, sites)
  | .jp (.mk id binder params type value) continuation => do
      let (value, valueSites) ← refineArrayGetCalls caller value
      let (continuation, continuationSites) ← refineArrayGetCalls caller continuation
      return (.jp (.mk id binder params type value) continuation,
        valueSites ++ continuationSites)
  | .cases (.mk typeName resultType discr alts) => do
      let results ← alts.mapM (refineArrayGetAlt caller)
      return (.cases (.mk typeName resultType discr (results.map (fun result => result.1))),
        results.foldl (init := #[]) fun sites result => sites ++ result.2)
  | code@(.jmp ..) | code@(.return ..) | code@(.unreach ..) =>
      return (code, #[])
  | .oset objectId index value continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.oset objectId index value continuation, sites)
  | .uset objectId index value continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.uset objectId index value continuation, sites)
  | .sset objectId width offset value type continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.sset objectId width offset value type continuation, sites)
  | .setTag objectId tag continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.setTag objectId tag continuation, sites)
  | .inc objectId amount check persistent continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.inc objectId amount check persistent continuation, sites)
  | .dec objectId amount check persistent objects continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.dec objectId amount check persistent objects continuation, sites)
  | .del objectId continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
      return (.del objectId continuation, sites)
  | .fun _ _ h => nomatch h

private partial def refineArrayGetAlt (caller : Name) :
    LCNF.Alt .impure → Except String (LCNF.Alt .impure × Array (Name × Name))
  | .ctorAlt info code => do
      let (code, sites) ← refineArrayGetCalls caller code
      return (.ctorAlt info code, sites)
  | .default code => do
      let (code, sites) ← refineArrayGetCalls caller code
      return (.default code, sites)
  | .alt _ _ _ h => nomatch h

end

private def arrayGetSiteCount (sites : Array (Name × Name))
    (target : Name) (callerSuffix : String) : Nat :=
  sites.foldl (init := 0) fun count site =>
    if site.1 == target && site.2.toString.endsWith callerSuffix then count + 1 else count

private def arrayGetFamilySiteCount (sites : Array (Name × Name))
    (target : Name) (family : String) : Nat :=
  sites.foldl (init := 0) fun count site =>
    if site.1 == target && site.2.toString.contains family &&
        site.2.toString.contains ".spec_" then count + 1 else count

/--
Recovers the monomorphic heap-object results erased by Lean 4.32's generic
array-read declarations. The transform is deliberately tied to the exact
prepared-player call sites and rejects closure drift.
-/
def refineMonomorphicArrayGetsWithSelectionValidation
    (artifact : Fir.Validation.Lcnf.Artifact)
    (selectionValidationSites : Nat) :
    Except String Fir.Validation.Lcnf.Artifact := do
  for targetName in #[arrayGetBangName, arrayGetName, arrayGetBangOwnedName,
      arrayUgetBorrowedName] do
    let targets := artifact.program.decls.filter (fun decl => decl.name == targetName)
    let expectedCount := 1
    unless targets.size == expectedCount do
      throw s!"expected {expectedCount} {targetName} declaration(s), found {targets.size}"
    if let some target := targets[0]? then
      unless target.type == LCNF.ImpureType.tobject do
        throw s!"{targetName} no longer returns tobject"
      match target.value with
      | .extern _ => pure ()
      | .code _ => throw s!"{targetName} unexpectedly became local code"
  let results ← artifact.program.decls.mapM fun decl => do
    let decl := if isArrayGetName decl.name then
      { decl with type := LCNF.ImpureType.object }
    else
      decl
    match decl.value with
    | .extern _ => return (decl, #[])
    | .code code =>
        let (code, sites) ← refineArrayGetCalls decl.name code
        return ({ decl with value := .code code }, sites)
  let sites := results.foldl (init := #[]) fun sites result => sites ++ result.2
  unless sites.size == 21 + selectionValidationSites &&
      arrayGetSiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.actionAt" == 1 &&
      arrayGetSiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.tick" == 2 &&
      arrayGetFamilySiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.parameterUpdates" == 2 &&
      arrayGetFamilySiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.findCurrentStep.spec_" == 1 &&
      arrayGetFamilySiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.findCurrentStepFrom" == 2 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.selectPlayerSegment" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.parameterUpdates" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.advance" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.statusForPlaying" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.loopAt" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.tick" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.findStepEnd" == 1 &&
      arrayGetFamilySiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.findPlayerSegment" == 1 &&
      arrayGetFamilySiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.findCrossedPauseTo" == 1 &&
      arrayGetSiteCount sites arrayGetBangOwnedName
        "Illuminate.AnimationPlayer.tick" == 1 &&
      arrayGetFamilySiteCount sites arrayUgetBorrowedName
        "Illuminate.AnimationPlayer.validatePrepared" == 3 &&
      arrayGetFamilySiteCount sites arrayUgetBorrowedName
        "Illuminate.AnimationPlayer.validateSelectionAnimation" ==
          selectionValidationSites do
    throw s!"Illuminate array-read call-site inventory changed: {sites.map (fun site => (site.1.toString, site.2.toString))}"
  let program : Fir.LeanIR.ImpureProgram := { decls := results.map (fun result => result.1) }
  return { artifact with
    program
    forms := Fir.Validation.Lcnf.collectForms program }

/-- Recover the exact v3 live-player array-read ABI inventory. -/
def refineMonomorphicArrayGets (artifact : Fir.Validation.Lcnf.Artifact) :
    Except String Fir.Validation.Lcnf.Artifact :=
  refineMonomorphicArrayGetsWithSelectionValidation artifact 0

/-- Capture both real persistent-player entries and apply only checked ABI recovery. -/
def captureSource : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Validation.Lcnf.Artifact) := do
  let source ← Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized #[
    ``Illuminate.AnimationPlayer.initialLive,
    ``Illuminate.AnimationPlayer.transitionLive]
  match refineMonomorphicArrayGets source with
  | .ok source => return .ok source
  | .error message => return .error (.manifest message)

private def configureLiveModule
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← Fir.Wasm.Emit.ResidentCache.eliminateLazyInitializers
      artifact.module |>.mapError fun error =>
        Fir.Wasm.Emit.Source.CompileError.manifest
          s!"failed to make the live module rewind-safe: {repr error}"
  unless module.globals.isEmpty do
    throw (.manifest "live source module unexpectedly retained resident globals")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

/-- Lower the checked Illuminate final-LCNF closure before resident linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  match source with
  | .error error => return .error error
  | .ok source => do
      let result ← Fir.Wasm.Emit.Source.compileModuleArtifactWithExports source #[
        ``Illuminate.AnimationPlayer.initialLive,
        ``Illuminate.AnimationPlayer.transitionLive] .ok
      return result.bind configureLiveModule

private def internalizeAvailableNumeric
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentNumeric.internalizeAvailable artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize available Nat/Int operations: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

private def internalizeFloat
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentFloat.internalizeAvailable artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize Illuminate Float operations: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

private def internalizeArrays
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentArray.internalizeAvailable artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize Illuminate Array operations: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

private def internalizeNatMod
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentNatMod.internalizeAvailable artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize Illuminate Nat.mod: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

private def internalizeNatShift
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentNatShift.internalizeAvailable artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize Illuminate Nat.shiftRight: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

private def internalizeUSize
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentUSize.internalizeAvailable artifact.module with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to internalize Illuminate USize operations: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

private def pruneLinkedModule
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact)
    (publicExports : Array Name) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let module ← match Fir.Wasm.Emit.ResidentDeadCode.pruneToExports
      artifact.module publicExports with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to prune the linked Illuminate module: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

/-- Link every reusable resident helper family already accepted by W7, then
retain exactly the requested source and allocator exports. -/
def internalizeExistingRuntimeForExports
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact)
    (sourceExports : Array Name) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeGetTag artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeIsShared artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeReadProjections artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeClosureProjections artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeClosureMatches artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.installAllocator artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeConstructors artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeImmediateNaturals artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizePartialApplications artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeSetters artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeIncrements artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeReleases artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeTagSetters artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeCacheSets artifact
  let artifact ← internalizeAvailableNumeric artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeBigNumeric artifact
  let artifact ← internalizeFloat artifact
  let artifact ← internalizeArrays artifact
  let artifact ← internalizeNatMod artifact
  let artifact ← internalizeNatShift artifact
  let artifact ← internalizeUSize artifact
  let artifact ← Fir.Wasm.Emit.ResidentPrettyFormat.internalizeStringLiterals artifact
  pruneLinkedModule artifact (sourceExports ++ #[
    Fir.Wasm.Emit.ResidentAllocator.frontierName,
    Fir.Wasm.Emit.ResidentAllocator.setFrontierName,
    Fir.Wasm.Emit.ResidentAllocator.rewindName,
    Fir.Wasm.Emit.ResidentAllocator.allocateName])

/-- Link the accepted resident runtime for the v3 live-player entries. -/
def internalizeExistingRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact :=
  internalizeExistingRuntimeForExports artifact #[
    ``Illuminate.AnimationPlayer.initialLive,
    ``Illuminate.AnimationPlayer.transitionLive]

/-- Compile and link the currently reusable Wasm-resident runtime frontier. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind internalizeExistingRuntime

end IlluminateFirNative.Compile
