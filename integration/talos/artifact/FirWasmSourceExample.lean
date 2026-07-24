import Fir.Validation.Corpus
import Fir.Wasm.Emit.Command
import Fir.Wasm.Emit.PrettyFormat
import Fir.Wasm.Emit.ResidentPrettyFormat

open Lean Elab Command

namespace Fir.Wasm.Emit.SourceFixture

def acceptString (_value : String) : UInt64 := 18446744073709551615

def classifyNatList (values : List Nat) : UInt64 :=
  match values with
  | [] => 0
  | _ :: _ => 1

#fir_wasm_pretty_facade prettyFormatRaw

def prettyFormatSource : Std.Format :=
  Std.Format.text "hello" ++
    Std.Format.nest 2 (Std.Format.line ++ Std.Format.text "world")

def prettyFormatExpected : String :=
  prettyFormatSource.pretty 12

def prettyFormatCoverageSource : Std.Format :=
  Std.Format.nil ++
    Std.Format.tag 7 (Std.Format.group
      (Std.Format.text "α" ++ Std.Format.line ++ Std.Format.text "β")) ++
    Std.Format.line ++
    Std.Format.nest 2
      (Std.Format.text "." ++ Std.Format.align false ++ Std.Format.text "γ" ++
        Std.Format.line ++ Std.Format.text "δ\nε")

def prettyFormatCoverageExpected : String :=
  prettyFormatCoverageSource.pretty 80

run_cmd do
  unless Fir.Wasm.Emit.SourceFixture.prettyFormatExpected == "hello\n  world" do
    throwError "native Std.Format.pretty oracle changed: {repr Fir.Wasm.Emit.SourceFixture.prettyFormatExpected}"
  unless Fir.Wasm.Emit.SourceFixture.prettyFormatCoverageExpected ==
      "α β\n. γ\n  δ\n  ε" do
    throwError "native Std.Format.pretty coverage oracle changed: {repr Fir.Wasm.Emit.SourceFixture.prettyFormatCoverageExpected}"

def formatAlignInfo : Lean.Compiler.LCNF.CtorInfo :=
  { name := ``Std.Format.align, cidx := 2, size := 0, «usize» := 0, ssize := 1 }

def formatTextInfo : Lean.Compiler.LCNF.CtorInfo :=
  { name := ``Std.Format.text, cidx := 3, size := 1, «usize» := 0, ssize := 0 }

def formatNestInfo : Lean.Compiler.LCNF.CtorInfo :=
  { name := ``Std.Format.nest, cidx := 4, size := 2, «usize» := 0, ssize := 0 }

def formatAppendInfo : Lean.Compiler.LCNF.CtorInfo :=
  { name := ``Std.Format.append, cidx := 5, size := 2, «usize» := 0, ssize := 0 }

def formatGroupInfo : Lean.Compiler.LCNF.CtorInfo :=
  { name := ``Std.Format.group, cidx := 6, size := 1, «usize» := 0, ssize := 1 }

def formatTagInfo : Lean.Compiler.LCNF.CtorInfo :=
  { name := ``Std.Format.tag, cidx := 7, size := 2, «usize» := 0, ssize := 0 }

def allocFormatText (runtime : Fir.LeanIR.Impure.RuntimeState) (value : String) :
    Except Fir.LeanIR.Impure.RuntimeFault
      (Fir.LeanIR.Impure.RuntimeState × Fir.LeanIR.Impure.Value) := do
  let (runtime, reference) := Fir.LeanIR.Impure.alloc runtime (.string value)
  Fir.LeanIR.Impure.allocCtor runtime formatTextInfo #[.object reference]

def allocFormatAppend (runtime : Fir.LeanIR.Impure.RuntimeState)
    (left right : Fir.LeanIR.Impure.Value) :
    Except Fir.LeanIR.Impure.RuntimeFault
      (Fir.LeanIR.Impure.RuntimeState × Fir.LeanIR.Impure.Value) :=
  Fir.LeanIR.Impure.allocCtor runtime formatAppendInfo #[left, right]

/-- Check one currently compiler-derived packed `UInt8` coordinate. This is a
source-fixture assertion, not a stable ABI promise: the fixture should move
with Lean whenever a cleaner constructor-layout surface becomes available. -/
def expectFormatUInt8Coordinate (runtime : Fir.LeanIR.Impure.RuntimeState)
    (format : Fir.LeanIR.Impure.Value) (slot offset : Nat) (expected : UInt8) :
    Except Fir.LeanIR.Impure.RuntimeFault Unit := do
  let actual ← Fir.LeanIR.Impure.getScalarField runtime format slot offset
  unless actual == .scalar (.uint8 expected) do
    throw (.malformed
      s!"unexpected packed Format UInt8 at compiler coordinate ({slot}, {offset})")

def allocFormatAlign (runtime : Fir.LeanIR.Impure.RuntimeState) (force : Bool) :
    Except Fir.LeanIR.Impure.RuntimeFault
      (Fir.LeanIR.Impure.RuntimeState × Fir.LeanIR.Impure.Value) := do
  let (runtime, align) ← Fir.LeanIR.Impure.allocCtor runtime formatAlignInfo #[]
  let value : UInt8 := if force then 1 else 0
  let runtime ← Fir.LeanIR.Impure.setScalarField runtime align 0 0
    (.scalar (.uint8 value))
  return (runtime, align)

def allocFormatGroup (runtime : Fir.LeanIR.Impure.RuntimeState)
    (format : Fir.LeanIR.Impure.Value) (behavior : Std.Format.FlattenBehavior) :
    Except Fir.LeanIR.Impure.RuntimeFault
      (Fir.LeanIR.Impure.RuntimeState × Fir.LeanIR.Impure.Value) := do
  let (runtime, group) ← Fir.LeanIR.Impure.allocCtor runtime formatGroupInfo #[format]
  let value : UInt8 := match behavior with
    | .allOrNone => 0
    | .fill => 1
  let runtime ← Fir.LeanIR.Impure.setScalarField runtime group 1 0
    (.scalar (.uint8 value))
  return (runtime, group)

def prettyFormatInvocation : Except Fir.LeanIR.Impure.RuntimeFault
    (Fir.LeanIR.Impure.RuntimeState × Array Fir.LeanIR.Impure.Value) := do
  let (runtime, hello) ← allocFormatText {} "hello"
  let (runtime, world) ← allocFormatText runtime "world"
  let (runtime, lineWorld) ← Fir.LeanIR.Impure.allocCtor runtime formatAppendInfo
    #[.object (.tagged 1), world]
  let (runtime, nested) ← Fir.LeanIR.Impure.allocCtor runtime formatNestInfo
    #[.object (.tagged 2), lineWorld]
  let (runtime, format) ← Fir.LeanIR.Impure.allocCtor runtime formatAppendInfo
    #[hello, nested]
  return (runtime, #[format, .object (.tagged 12), .object (.tagged 0),
    .object (.tagged 0)])

def prettyFormatCoverageInvocation : Except Fir.LeanIR.Impure.RuntimeFault
    (Fir.LeanIR.Impure.RuntimeState × Array Fir.LeanIR.Impure.Value) := do
  let nil : Fir.LeanIR.Impure.Value := .object (.tagged 0)
  let line : Fir.LeanIR.Impure.Value := .object (.tagged 1)
  let (runtime, alpha) ← allocFormatText {} "α"
  let (runtime, beta) ← allocFormatText runtime "β"
  let (runtime, alphaLine) ← allocFormatAppend runtime alpha line
  let (runtime, alphaLineBeta) ← allocFormatAppend runtime alphaLine beta
  let (runtime, grouped) ← allocFormatGroup runtime alphaLineBeta .allOrNone
  let _ ← expectFormatUInt8Coordinate runtime grouped 1 0 0
  let (runtime, taggedFormat) ← Fir.LeanIR.Impure.allocCtor runtime formatTagInfo
    #[.object (.tagged 7), grouped]
  let (runtime, emptyTagged) ← allocFormatAppend runtime nil taggedFormat
  let (runtime, formatPrefix) ← allocFormatAppend runtime emptyTagged line
  let (runtime, dot) ← allocFormatText runtime "."
  let (runtime, align) ← allocFormatAlign runtime false
  let _ ← expectFormatUInt8Coordinate runtime align 0 0 0
  let (runtime, gamma) ← allocFormatText runtime "γ"
  let (runtime, deltaEpsilon) ← allocFormatText runtime "δ\nε"
  let (runtime, dotAlign) ← allocFormatAppend runtime dot align
  let (runtime, dotAlignGamma) ← allocFormatAppend runtime dotAlign gamma
  let (runtime, beforeLine) ← allocFormatAppend runtime dotAlignGamma line
  let (runtime, nestedBody) ← allocFormatAppend runtime beforeLine deltaEpsilon
  let (runtime, nested) ← Fir.LeanIR.Impure.allocCtor runtime formatNestInfo
    #[.object (.tagged 2), nestedBody]
  let (runtime, format) ← allocFormatAppend runtime formatPrefix nested
  return (runtime, #[format, .object (.tagged 80), .object (.tagged 0),
    .object (.tagged 0)])

end Fir.Wasm.Emit.SourceFixture

#fir_wasm_emit Fir.Validation.Corpus.Source.maxUInt64 to "_build/source-uint64.wasm"

#fir_wasm_emit Fir.Validation.Corpus.Source.litNat to "_build/source-nat.wasm"

#fir_wasm_emit_case "usize-roundtrip"
  to "_build/source-usize-id.wasm"

#fir_wasm_emit_module Fir.Validation.Corpus.Source.idUSize
  to "_build/source-usize-id-module.wasm"

#fir_wasm_emit_case "uint8-roundtrip"
  to "_build/source-uint8-id.wasm"

#fir_wasm_emit_case "uint16-roundtrip"
  to "_build/source-uint16-id.wasm"

#fir_wasm_emit_case "uint32-roundtrip"
  to "_build/source-uint32-id.wasm"

#fir_wasm_emit_case "uint64-roundtrip"
  to "_build/source-uint64-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.acceptString with [string("hello α_world_β")]
  to "_build/source-string-input.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.classifyNatList with
    [natList([0, 18446744073709551616, 42])]
  to "_build/source-nat-list-case.wasm"

run_cmd do
  let (runtime, args) ← match Fir.Wasm.Emit.SourceFixture.prettyFormatInvocation with
    | .ok invocation => pure invocation
    | .error error => throwError "failed to construct Format runtime: {repr error}"
  let result ← liftCoreM <| Fir.Wasm.Emit.PrettyFormat.compileModule
    ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw
  let moduleArtifact ← match result with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile Format facade: {repr error}"
  match ← moduleArtifact.write "_build/source-pretty-format-module.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write reusable Format module: {repr error}"
  let residentResult ← liftCoreM <|
    Fir.Wasm.Emit.ResidentPrettyFormat.compileGetTagModule
    ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw
  let residentArtifact ← match residentResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile resident Format facade: {repr error}"
  unless moduleArtifact.module.runtimeOperations.contains .getTag &&
      !residentArtifact.module.runtimeOperations.contains .getTag &&
      residentArtifact.module.imports.size + 1 == moduleArtifact.module.imports.size do
    throwError "resident Format getTag import accounting changed"
  unless residentArtifact.module.memory.any fun memory =>
      memory.pagesMin == 1 && memory.exportName == some "memory" do
    throwError "resident Format module does not export its memory"
  unless residentArtifact.module.exports.contains
      Fir.Wasm.Emit.ResidentRuntime.getTagName do
    throwError "resident Format module does not export fir_getTag"
  match ← residentArtifact.write
      "_build/source-pretty-format-resident-get-tag.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write resident Format module: {repr error}"
  let residentRuntimeResult ← liftCoreM <|
    Fir.Wasm.Emit.ResidentPrettyFormat.compileRuntimeModule
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw
  let residentRuntimeArtifact ← match residentRuntimeResult with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to compile resident-runtime Format facade: {repr error}"
  unless residentArtifact.module.runtimeOperations.contains .isShared &&
      !residentRuntimeArtifact.module.runtimeOperations.contains .isShared &&
      residentRuntimeArtifact.module.imports.size + 1 ==
        residentArtifact.module.imports.size do
    throwError "resident Format isShared import accounting changed"
  unless residentRuntimeArtifact.module.exports.contains
      Fir.Wasm.Emit.ResidentRuntime.isSharedName do
    throwError "resident Format module does not export fir_isShared"
  match ← residentRuntimeArtifact.write
      "_build/source-pretty-format-resident-runtime.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident-runtime Format module: {repr error}"
  let readProjections := residentRuntimeArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentRuntime.supportsReadProjection
  let expectedReadProjections :=
    Fir.Wasm.Emit.ResidentRuntime.prettyFormatReadProjections
  unless readProjections.size == expectedReadProjections.size &&
      readProjections.all expectedReadProjections.contains &&
      expectedReadProjections.all readProjections.contains do
    throwError "resident Format read-projection inventory changed"
  let residentProjectionResult ← liftCoreM <|
    Fir.Wasm.Emit.ResidentPrettyFormat.compileModule
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw
  let residentProjectionArtifact ← match residentProjectionResult with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident-projection Format facade: {repr error}"
  unless residentProjectionArtifact.module.runtimeOperations.all fun operation =>
      !Fir.Wasm.Emit.ResidentRuntime.supportsReadProjection operation do
    throwError "resident Format retained a supported read-projection import"
  unless residentProjectionArtifact.module.imports.size + readProjections.size ==
      residentRuntimeArtifact.module.imports.size do
    throwError "resident Format read-projection import accounting changed"
  unless readProjections.all fun operation =>
      (Fir.Wasm.Emit.ResidentRuntime.readProjectionName? operation).any
        residentProjectionArtifact.module.exports.contains do
    throwError "resident Format projection helper exports changed"
  match ← residentProjectionArtifact.write
      "_build/source-pretty-format-resident-projections.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident-projection Format module: {repr error}"
  let artifact ← match moduleArtifact.withRuntimeInvocation "source-pretty-format"
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw runtime args with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to attach Format invocation: {repr error}"
  artifact.write "_build/source-pretty-format.wasm"
  let (coverageRuntime, coverageArgs) ←
    match Fir.Wasm.Emit.SourceFixture.prettyFormatCoverageInvocation with
    | .ok invocation => pure invocation
    | .error error => throwError "failed to construct Format coverage runtime: {repr error}"
  let coverageArtifact ← match moduleArtifact.withRuntimeInvocation
      "source-pretty-format-coverage"
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw
      ``Fir.Wasm.Emit.SourceFixture.prettyFormatRaw coverageRuntime coverageArgs with
    | .ok artifact => pure artifact
    | .error error => throwError "failed to attach Format coverage invocation: {repr error}"
  coverageArtifact.write "_build/source-pretty-format-coverage.wasm"
