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
    Fir.Wasm.Emit.ResidentPrettyFormat.compileModule
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw
  let artifact ← match result with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident styled Format facade: {repr error}"
  unless artifact.module.memory.any fun memory =>
      memory.pagesMin == 1 && memory.exportName == some "memory" do
    throwError "resident styled Format module does not export its memory"
  unless Fir.Wasm.Emit.ResidentAllocator.helperNames.all
      artifact.module.exports.contains do
    throwError "resident styled Format module lost allocator exports"
  match ← artifact.write
      "_build/source-pretty-format-trace-resident-allocator.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident styled Format module: {repr error}"
