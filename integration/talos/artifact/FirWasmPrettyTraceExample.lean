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
