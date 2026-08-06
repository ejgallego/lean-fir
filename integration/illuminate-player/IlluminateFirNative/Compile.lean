import Fir.Wasm.Emit.ResidentPrettyFormat
import IlluminateFirNative.Facade

namespace IlluminateFirNative.Compile

open Lean
open Lean.Compiler

private partial def environmentDeclarationAncestor? (env : Environment) (name : Name) :
    Option Name :=
  if env.contains name then
    some name
  else if name.isAnonymous then
    none
  else
    environmentDeclarationAncestor? env name.getPrefix

private def addUniqueName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

/--
Recursively internalize source and compiler-generated declarations inside one
temporary compiler environment. Unlike the generic source helper, generated
specialization names created by one capture remain available as roots for the
next capture; the outer `withoutModifyingEnv` still restores the elaborating
module afterward.
-/
private partial def compileEntryInternalizedLive (entry : Name)
    (dependencies : Array Name := #[]) : CoreM Fir.Validation.Lcnf.Artifact := do
  let artifact ← Fir.Validation.Lcnf.compileEntry entry dependencies
  let env ← getEnv
  let additions := artifact.externalNames.foldl (init := #[]) fun additions name =>
    let candidate := if env.contains name then
      some name
    else
      environmentDeclarationAncestor? env name
    match candidate with
    | some candidate =>
        if candidate == entry || dependencies.contains candidate then additions
        else addUniqueName additions candidate
    | none => additions
  if additions.isEmpty then
    return artifact
  compileEntryInternalizedLive entry (dependencies ++ additions)

private def arrayGetBangName : Name := ``Array.get!InternalBorrowed

private def arrayGetName : Name := ``Array.getInternalBorrowed

private def isArrayGetName (name : Name) : Bool :=
  name == arrayGetBangName || name == arrayGetName

private def expectedArrayGetCaller (target caller : Name) : Bool :=
  let suffix := caller.toString
  if target == arrayGetBangName then
    suffix.endsWith "Illuminate.AnimationPlayer.findCurrentStep.loop" ||
      suffix.endsWith "Illuminate.AnimationPlayer.actionAt" ||
      suffix.endsWith "Illuminate.AnimationPlayer.tick"
  else if target == arrayGetName then
    suffix.endsWith "Illuminate.AnimationPlayer.parameterUpdates" ||
      suffix.endsWith "Illuminate.AnimationPlayer.advance" ||
      suffix.endsWith "Illuminate.AnimationPlayer.statusForPlaying" ||
      suffix.endsWith "Illuminate.AnimationPlayer.loopAt" ||
      suffix.endsWith "Illuminate.AnimationPlayer.tick" ||
      suffix.endsWith "Illuminate.AnimationPlayer.findStepEnd"
  else
    false

mutual

private partial def collectNamedCalls (names : Array Name) :
    LCNF.Code .impure → Array Name
  | .let decl continuation =>
      let names := match decl.value with
        | .fap name _ | .pap name _ =>
            if names.contains name then names else names.push name
        | _ => names
      collectNamedCalls names continuation
  | .jp decl continuation =>
      collectNamedCalls (collectNamedCalls names decl.value) continuation
  | .cases cases => cases.alts.foldl collectNamedCallsAlt names
  | .oset (k := continuation) .. | .uset (k := continuation) .. |
      .sset (k := continuation) .. | .setTag (k := continuation) .. |
      .inc (k := continuation) .. | .dec (k := continuation) .. |
      .del (k := continuation) .. => collectNamedCalls names continuation
  | .jmp .. | .return .. | .unreach .. => names
  | .fun _ _ h => nomatch h

private partial def collectNamedCallsAlt (names : Array Name) :
    LCNF.Alt .impure → Array Name
  | .ctorAlt _ code | .default code => collectNamedCalls names code
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
        let calls := match decl.value with
          | .code code => collectNamedCalls #[] code
          | .extern _ => #[]
        reachableDeclarations program (calls.toList ++ pending) (seen.push name)

/-- Remove compiler-captured source ancestors that have no named edge from the entry closure. -/
def pruneUnreachableDeclarations (artifact : Fir.Validation.Lcnf.Artifact) :
    Except String Fir.Validation.Lcnf.Artifact := do
  let reachable ← reachableDeclarations artifact.program [artifact.entry]
  let program : Fir.LeanIR.ImpureProgram := {
    decls := artifact.program.decls.filter (fun decl => reachable.contains decl.name) }
  unless program.findDecl? artifact.entry |>.isSome do
    throw s!"entry {artifact.entry} disappeared during declaration pruning"
  return { artifact with
    program
    externalNames := artifact.externalNames.filter reachable.contains
    forms := Fir.Validation.Lcnf.collectForms program }

mutual

private partial def refineArrayGetCalls (caller : Name) :
    LCNF.Code .impure → Except String (LCNF.Code .impure × Array (Name × Name))
  | .let decl continuation => do
      let (continuation, sites) ← refineArrayGetCalls caller continuation
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

/--
Recover the three monomorphic heap-object results erased by Lean 4.32's
generic array-read declarations. The transform is deliberately tied to the
exact `StepInfo`, `Segment`, and `Array String` call sites reachable from the
real Illuminate player and rejects closure drift.
-/
def refineMonomorphicArrayGets (artifact : Fir.Validation.Lcnf.Artifact) :
    Except String Fir.Validation.Lcnf.Artifact := do
  for targetName in #[arrayGetBangName, arrayGetName] do
    let targets := artifact.program.decls.filter (fun decl => decl.name == targetName)
    unless targets.size == 1 do
      throw s!"expected one {targetName} declaration, found {targets.size}"
    let target := targets[0]!
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
  unless sites.size == 10 &&
      arrayGetSiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.findCurrentStep.loop" == 1 &&
      arrayGetSiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.actionAt" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.parameterUpdates" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.advance" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.statusForPlaying" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.loopAt" == 1 &&
      arrayGetSiteCount sites arrayGetBangName
        "Illuminate.AnimationPlayer.tick" == 2 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.tick" == 1 &&
      arrayGetSiteCount sites arrayGetName
        "Illuminate.AnimationPlayer.findStepEnd" == 1 do
    throw s!"Illuminate array-read call-site inventory changed: {sites.map (fun site => (site.1.toString, site.2.toString))}"
  let program : Fir.LeanIR.ImpureProgram := { decls := results.map (fun result => result.1) }
  return { artifact with
    program
    forms := Fir.Validation.Lcnf.collectForms program }

/-- Capture the real Illuminate trace entry and apply only checked ABI recovery. -/
def captureSource : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Validation.Lcnf.Artifact) := do
  let source ← withoutModifyingEnv <| compileEntryInternalizedLive
    ``Illuminate.Animation.Native.replayTraceNative
  let source ← match pruneUnreachableDeclarations source with
    | .ok source => pure source
    | .error message => return .error (.manifest message)
  match refineMonomorphicArrayGets source with
  | .ok source => return .ok source
  | .error message => return .error (.manifest message)

/-- Lower the checked Illuminate final-LCNF closure before resident linking. -/
def compileBaseModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let source ← captureSource
  match source with
  | .error error => return .error error
  | .ok source => Fir.Wasm.Emit.Source.compileModuleArtifact source

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
  Fir.Wasm.Emit.ResidentPrettyFormat.internalizeStringLiterals artifact

/-- Compile and link the currently reusable Wasm-resident runtime frontier. -/
def compileResidentModule : CoreM (Except Fir.Wasm.Emit.Source.CompileError
    Fir.Wasm.Emit.Source.ModuleArtifact) := do
  let result ← compileBaseModule
  return result.bind internalizeExistingRuntime

end IlluminateFirNative.Compile
