import Fir.Wasm.Emit.ResidentPrettyFormat
import Lean.Elab.Command

open Lean Elab Command

namespace Fir.Wasm.Emit.SourceFixture

#fir_wasm_pretty_trace_facade prettyFormatTraceRaw

def prettyFormatTraceSource : Std.Format :=
  Std.Format.nil ++
    Std.Format.tag 7 (Std.Format.group
      (Std.Format.text "α" ++ Std.Format.line ++ Std.Format.text "β")) ++
    Std.Format.line ++
    Std.Format.nest 2
      (Std.Format.text "." ++ Std.Format.align false ++ Std.Format.text "γ" ++
        Std.Format.line ++ Std.Format.text "δ\nε")

def prettyFormatTraceTextExpected : String :=
  prettyFormatTraceSource.pretty 80

def prettyFormatTraceEventsExpected :
    List prettyFormatTraceRawEvent := [
  { kind := 3, text := "", value := 0 },
  { kind := 2, text := "", value := 7 },
  { kind := 0, text := "α", value := 0 },
  { kind := 3, text := "", value := 0 },
  { kind := 0, text := " ", value := 0 },
  { kind := 3, text := "", value := 0 },
  { kind := 0, text := "β", value := 0 },
  { kind := 3, text := "", value := 1 },
  { kind := 1, text := "", value := 0 },
  { kind := 3, text := "", value := 0 },
  { kind := 0, text := ".", value := 0 },
  { kind := 3, text := "", value := 0 },
  { kind := 0, text := " ", value := 0 },
  { kind := 3, text := "", value := 0 },
  { kind := 0, text := "γ", value := 0 },
  { kind := 3, text := "", value := 0 },
  { kind := 1, text := "", value := 2 },
  { kind := 3, text := "", value := 0 },
  { kind := 0, text := "δ", value := 0 },
  { kind := 1, text := "", value := 2 },
  { kind := 0, text := "ε", value := 0 },
  { kind := 3, text := "", value := 0 }]

run_cmd do
  unless Fir.Wasm.Emit.SourceFixture.prettyFormatTraceTextExpected ==
      "α β\n. γ\n  δ\n  ε" do
    throwError "native styled prettyM text oracle changed: {repr Fir.Wasm.Emit.SourceFixture.prettyFormatTraceTextExpected}"
  let trace := Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw
    Fir.Wasm.Emit.SourceFixture.prettyFormatTraceSource 80 0 0
  unless trace.text ==
      Fir.Wasm.Emit.SourceFixture.prettyFormatTraceTextExpected do
    throwError "native styled prettyM text projection changed: {repr trace.text}"
  unless trace.eventsRev.reverse ==
      Fir.Wasm.Emit.SourceFixture.prettyFormatTraceEventsExpected do
    throwError "native styled prettyM event oracle changed:\n{repr trace.eventsRev.reverse}"
  let result ← liftCoreM <|
    Fir.Wasm.Emit.ResidentPrettyFormat.compileConstructorModule
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw
  let constructorArtifact ← match result with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled constructor facade: {repr error}"
  unless constructorArtifact.module.memory.any fun memory =>
      memory.pagesMin == 1 && memory.exportName == some "memory" do
    throwError "resident styled Format module does not export its memory"
  unless Fir.Wasm.Emit.ResidentAllocator.helperNames.all
      constructorArtifact.module.exports.contains do
    throwError "resident styled Format module lost allocator exports"
  unless constructorArtifact.module.imports.size == 157 &&
      constructorArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentConstructor.isConstructor operation do
    throwError "resident styled Format constructor frontier changed"
  match ← constructorArtifact.write
      "_build/source-pretty-format-trace-resident-constructors.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled constructor module: {repr error}"
  let naturals := constructorArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentLiteral.isImmediateNatural
  unless naturals.size == 4 do
    throwError "resident styled Format immediate-Natural inventory changed"
  let naturalArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeImmediateNaturals
        constructorArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled Natural facade: {repr error}"
  unless naturalArtifact.module.imports.size == 153 &&
      naturalArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentLiteral.isImmediateNatural operation do
    throwError "resident styled Format Natural frontier changed"
  unless (naturalArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentLiteral.isStringLiteral).size == 4 do
    throwError "resident styled Format moved strings across the host boundary"
  unless naturalArtifact.module.closureDispatch ==
      constructorArtifact.module.closureDispatch &&
      naturalArtifact.module.closureDescriptors ==
        constructorArtifact.module.closureDescriptors do
    throwError "resident styled Natural linking changed closure metadata"
  match ← naturalArtifact.write
      "_build/source-pretty-format-trace-resident-naturals.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled Natural module: {repr error}"
  let partialApplications := naturalArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentClosureAllocation.isPartialApplication
  unless partialApplications.size == 87 do
    throwError "resident styled Format partial-application inventory changed"
  let partialApplicationArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizePartialApplications
        naturalArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError
          "failed to compile resident styled partial applications: {repr error}"
  unless partialApplicationArtifact.module.imports.size == 66 &&
      partialApplicationArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentClosureAllocation.isPartialApplication operation do
    throwError "resident styled Format partial-application frontier changed"
  unless partialApplicationArtifact.module.imports.size +
      partialApplications.size == naturalArtifact.module.imports.size do
    throwError "resident styled partial-application import accounting changed"
  unless (partialApplicationArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentLiteral.isStringLiteral).size == 4 do
    throwError "resident styled Format moved strings across the host boundary"
  unless partialApplicationArtifact.module.closureDispatch ==
      naturalArtifact.module.closureDispatch &&
      partialApplicationArtifact.module.closureDescriptors ==
        naturalArtifact.module.closureDescriptors do
    throwError "resident styled partial applications changed closure metadata"
  unless (List.range partialApplications.size).all fun ordinal =>
      partialApplicationArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentClosureAllocation.partialApplicationName ordinal) do
    throwError "resident styled partial-application helper exports changed"
  match ← partialApplicationArtifact.write
      "_build/source-pretty-format-trace-resident-partial-applications.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError
        "failed to write resident styled partial-application module: {repr error}"
  let setters := partialApplicationArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentMutation.isSetter
  unless setters.size == 10 do
    throwError "resident styled Format setter inventory changed"
  let setterArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeSetters
        partialApplicationArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled setters: {repr error}"
  unless setterArtifact.module.imports.size == 56 &&
      setterArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentMutation.isSetter operation do
    throwError "resident styled Format setter frontier changed"
  unless setterArtifact.module.imports.size + setters.size ==
      partialApplicationArtifact.module.imports.size do
    throwError "resident styled setter import accounting changed"
  unless setterArtifact.module.closureDispatch ==
      partialApplicationArtifact.module.closureDispatch &&
      setterArtifact.module.closureDescriptors ==
        partialApplicationArtifact.module.closureDescriptors do
    throwError "resident styled setters changed closure metadata"
  unless (List.range setters.size).all fun ordinal =>
      setterArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentMutation.setterName ordinal) do
    throwError "resident styled setter helper exports changed"
  match ← setterArtifact.write
      "_build/source-pretty-format-trace-resident-setters.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled setter module: {repr error}"
  let increments := setterArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentReferenceCount.isIncrement
  unless increments.size == 4 do
    throwError "resident styled Format increment inventory changed"
  let incrementArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeIncrements setterArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled increments: {repr error}"
  unless incrementArtifact.module.imports.size == 52 &&
      incrementArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentReferenceCount.isIncrement operation do
    throwError "resident styled Format increment frontier changed"
  unless incrementArtifact.module.imports.size + increments.size ==
      setterArtifact.module.imports.size do
    throwError "resident styled increment import accounting changed"
  unless incrementArtifact.module.closureDispatch ==
      setterArtifact.module.closureDispatch &&
      incrementArtifact.module.closureDescriptors ==
        setterArtifact.module.closureDescriptors do
    throwError "resident styled increments changed closure metadata"
  unless (List.range increments.size).all fun ordinal =>
      incrementArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentReferenceCount.incrementName ordinal) do
    throwError "resident styled increment helper exports changed"
  match ← incrementArtifact.write
      "_build/source-pretty-format-trace-resident-increments.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError
        "failed to write resident styled increment module: {repr error}"
  let releases := incrementArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentRelease.isRelease
  unless releases.size == 6 do
    throwError "resident styled Format recursive-release inventory changed"
  let releaseArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeReleases incrementArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled releases: {repr error}"
  unless releaseArtifact.module.imports.size == 46 &&
      releaseArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentRelease.isRelease operation do
    throwError "resident styled Format recursive-release frontier changed"
  unless releaseArtifact.module.imports.size + releases.size ==
      incrementArtifact.module.imports.size do
    throwError "resident styled release import accounting changed"
  unless releaseArtifact.module.closureDispatch ==
      incrementArtifact.module.closureDispatch &&
      releaseArtifact.module.closureDescriptors ==
        incrementArtifact.module.closureDescriptors do
    throwError "resident styled releases changed closure metadata"
  unless (List.range releases.size).all fun ordinal =>
      releaseArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentRelease.releaseName ordinal) do
    throwError "resident styled release helper exports changed"
  match ← releaseArtifact.write
      "_build/source-pretty-format-trace-resident-releases.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled release module: {repr error}"
  let tagSetters := releaseArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentMutation.isTagSetter
  unless tagSetters.size == 1 do
    throwError "resident styled Format tag-setter inventory changed"
  let tagSetterArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeTagSetters releaseArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled tag setter: {repr error}"
  unless tagSetterArtifact.module.imports.size == 45 &&
      tagSetterArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentMutation.isTagSetter operation do
    throwError "resident styled Format tag-setter frontier changed"
  unless tagSetterArtifact.module.imports.size + tagSetters.size ==
      releaseArtifact.module.imports.size do
    throwError "resident styled tag-setter import accounting changed"
  unless tagSetterArtifact.module.closureDispatch ==
      releaseArtifact.module.closureDispatch &&
      tagSetterArtifact.module.closureDescriptors ==
        releaseArtifact.module.closureDescriptors do
    throwError "resident styled tag setter changed closure metadata"
  unless (List.range tagSetters.size).all fun ordinal =>
      tagSetterArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentMutation.tagSetterName ordinal) do
    throwError "resident styled tag-setter helper exports changed"
  match ← tagSetterArtifact.write
      "_build/source-pretty-format-trace-resident-tag-setters.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled tag-setter module: {repr error}"
  let cacheSets := tagSetterArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentCache.isCacheSet
  unless cacheSets.size == 21 do
    throwError "resident styled Format lazy-cache inventory changed"
  let cacheArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeCacheSets tagSetterArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled cache: {repr error}"
  unless cacheArtifact.module.imports.size == 24 &&
      cacheArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentCache.isCacheSet operation do
    throwError "resident styled Format lazy-cache frontier changed"
  unless cacheArtifact.module.imports.size + cacheSets.size ==
      tagSetterArtifact.module.imports.size do
    throwError "resident styled lazy-cache import accounting changed"
  unless cacheArtifact.module.closureDispatch ==
      tagSetterArtifact.module.closureDispatch &&
      cacheArtifact.module.closureDescriptors ==
        tagSetterArtifact.module.closureDescriptors do
    throwError "resident styled cache changed closure metadata"
  unless (List.range cacheSets.size).all fun ordinal =>
      cacheArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentCache.cacheSetName ordinal) do
    throwError "resident styled lazy-cache helper exports changed"
  match ← cacheArtifact.write
      "_build/source-pretty-format-trace-resident-cache.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled cache module: {repr error}"
  let numericArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeNumeric cacheArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled numeric module: {repr error}"
  unless numericArtifact.module.imports.size == 14 do
    throwError "resident styled Format numeric frontier changed"
  unless Fir.Wasm.Emit.ResidentNumeric.externalHelperNames.all
      numericArtifact.module.exports.contains do
    throwError "resident styled numeric helper exports changed"
  unless numericArtifact.module.closureDispatch ==
      cacheArtifact.module.closureDispatch &&
      numericArtifact.module.closureDescriptors ==
        cacheArtifact.module.closureDescriptors &&
      numericArtifact.formattedLcnf == cacheArtifact.formattedLcnf do
    throwError "resident styled numeric linking changed source or closure metadata"
  match ← numericArtifact.write
      "_build/source-pretty-format-trace-resident-numeric.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled numeric module: {repr error}"
