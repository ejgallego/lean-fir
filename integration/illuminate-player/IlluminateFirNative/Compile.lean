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
    generatedCallerFamily suffix "Illuminate.AnimationPlayer.validatePrepared"
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
def refineMonomorphicArrayGets (artifact : Fir.Validation.Lcnf.Artifact) :
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
  unless sites.size == 21 &&
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
        "Illuminate.AnimationPlayer.validatePrepared" == 3 do
    throw s!"Illuminate array-read call-site inventory changed: {sites.map (fun site => (site.1.toString, site.2.toString))}"
  let program : Fir.LeanIR.ImpureProgram := { decls := results.map (fun result => result.1) }
  return { artifact with
    program
    forms := Fir.Validation.Lcnf.collectForms program }

/-- Capture both real persistent-player entries and apply only checked ABI recovery. -/
def captureSource : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Validation.Lcnf.Artifact) := do
  let source ← Fir.Wasm.Emit.Source.compileEntriesFinalCapturedInternalized #[
    ``Illuminate.AnimationPlayer.initialLive,
    ``Illuminate.AnimationPlayer.transitionLive]
  match refineMonomorphicArrayGets source with
  | .ok source => return .ok source
  | .error message => return .error (.manifest message)

/-
Replace Lean's private lazy-cache globals by direct calls in this package.

The live adapter rewinds every per-event allocation to a persistent checkpoint.
A cache miss above that checkpoint would otherwise publish an object through a
private Wasm global. Closed zero-argument declarations are pure, so allocating
their values afresh in the scratch arena preserves the result while leaving the
allocator frontier as the module's only mutable heap root.
-/
mutual

private partial def removeLazyCacheInstructions :
    List Fir.Wasm.Instruction → Except String (List Fir.Wasm.Instruction)
  | .globalGet flagIndex .uint32 :: .ifElse [] miss ::
      .globalGet valueIndex resultKind :: rest => do
      match miss with
      | [.call (.declaration target),
          .call (.runtime (.cacheSet cacheTarget cacheKind)),
          .globalSet storedValueIndex storedKind,
          .i32Const .uint32 initialized,
          .globalSet storedFlagIndex .uint32] =>
          unless target == cacheTarget && resultKind == cacheKind &&
              valueIndex == storedValueIndex && resultKind == storedKind &&
              flagIndex == storedFlagIndex && initialized == 1 do
            throw s!"malformed lazy-cache sequence for {target}"
          return .call (.declaration target) ::
            (← removeLazyCacheInstructions rest)
      | _ =>
          let head ← removeLazyCacheInstruction (.globalGet flagIndex .uint32)
          return head :: (← removeLazyCacheInstructions
            (.ifElse [] miss :: .globalGet valueIndex resultKind :: rest))
  | instruction :: rest =>
      return (← removeLazyCacheInstruction instruction) ::
        (← removeLazyCacheInstructions rest)
  | [] => return []

private partial def removeLazyCacheInstruction :
    Fir.Wasm.Instruction → Except String Fir.Wasm.Instruction
  | .block label body =>
      return .block label (← removeLazyCacheInstructions body)
  | .loop label body =>
      return .loop label (← removeLazyCacheInstructions body)
  | .ifElse thenBody elseBody =>
      return .ifElse (← removeLazyCacheInstructions thenBody)
        (← removeLazyCacheInstructions elseBody)
  | instruction => return instruction

end

private partial def instructionUsesGlobal : Fir.Wasm.Instruction → Bool
  | .globalGet .. | .globalSet .. => true
  | .block _ body | .loop _ body => body.any instructionUsesGlobal
  | .ifElse thenBody elseBody =>
      thenBody.any instructionUsesGlobal || elseBody.any instructionUsesGlobal
  | _ => false

private def configureLiveModule
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let functions ← artifact.module.functions.mapM fun function => do
    let body ← removeLazyCacheInstructions function.body |>.mapError
      Fir.Wasm.Emit.Source.CompileError.manifest
    return { function with body }
  unless functions.all (fun function => !function.body.any instructionUsesGlobal) do
    throw (.manifest "live module retained a private cache-global access")
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  unless runtimeOperations.all (fun operation => !Fir.Wasm.Emit.ResidentCache.isCacheSet operation) do
    throw (.manifest "live module retained a cache-set operation")
  let externalImports := artifact.module.imports.filter (·.operation?.isNone)
  let imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
  let module := {
    artifact.module with
    functions
    exports := #[
      ``Illuminate.AnimationPlayer.initialLive,
      ``Illuminate.AnimationPlayer.transitionLive]
    initializers := #[]
    runtimeOperations
    imports }
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
    (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
    Except Fir.Wasm.Emit.Source.CompileError Fir.Wasm.Emit.Source.ModuleArtifact := do
  let publicExports := #[
    ``Illuminate.AnimationPlayer.initialLive,
    ``Illuminate.AnimationPlayer.transitionLive,
    Fir.Wasm.Emit.ResidentAllocator.frontierName,
    Fir.Wasm.Emit.ResidentAllocator.setFrontierName,
    Fir.Wasm.Emit.ResidentAllocator.rewindName,
    Fir.Wasm.Emit.ResidentAllocator.allocateName]
  let module ← match Fir.Wasm.Emit.ResidentDeadCode.pruneToExports
      artifact.module publicExports with
    | .ok module => pure module
    | .error error =>
        throw (.manifest s!"failed to prune the linked Illuminate module: {repr error}")
  let bytes ← match Fir.Wasm.Emit.encode module with
    | .ok bytes => pure bytes
    | .error error => throw (.encoding error)
  return { artifact with module, bytes }

/-- Link every reusable resident helper family already accepted by W7. -/
def internalizeExistingRuntime (artifact : Fir.Wasm.Emit.Source.ModuleArtifact) :
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
  pruneLinkedModule artifact

/-- Compile and link the currently reusable Wasm-resident runtime frontier. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind internalizeExistingRuntime

end IlluminateFirNative.Compile
