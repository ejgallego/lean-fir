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
  unless moduleArtifact.module.closureDispatch.size == 38 &&
      moduleArtifact.module.closureDispatch ==
        Fir.Wasm.collectClosureDispatch moduleArtifact.module.runtimeOperations do
    throwError "compiler Format closure-dispatch inventory changed"
  unless moduleArtifact.module.closureDescriptors.size == 14 &&
      moduleArtifact.module.closureDescriptors ==
        Fir.Wasm.collectClosureDescriptors moduleArtifact.module.runtimeOperations do
    throwError "compiler Format closure-descriptor inventory changed"
  match ← moduleArtifact.write "_build/source-pretty-format-module.wasm" with
  | .ok () => pure ()
  | .error error => throwError "failed to write reusable Format module: {repr error}"
  let residentArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeGetTag moduleArtifact with
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
  let residentRuntimeArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeIsShared residentArtifact with
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
  let residentProjectionArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeReadProjections
        residentRuntimeArtifact with
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
  let closureProjections :=
    residentProjectionArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentRuntime.supportsClosureProjection
  let expectedClosureCoordinates :=
    Fir.Wasm.Emit.ResidentRuntime.prettyFormatClosureProjectionCoordinates
  unless closureProjections.size == 87 &&
      closureProjections.all (fun operation =>
        (Fir.Wasm.Emit.ResidentRuntime.closureProjectionCoordinate? operation).any
          expectedClosureCoordinates.contains) &&
      expectedClosureCoordinates.all (fun coordinate =>
        closureProjections.any fun operation =>
          Fir.Wasm.Emit.ResidentRuntime.closureProjectionCoordinate? operation ==
            some coordinate) do
    throwError "resident Format closure-projection inventory changed"
  let residentClosureArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeClosureProjections
        residentProjectionArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident closure-projection Format facade: {repr error}"
  unless residentClosureArtifact.module.runtimeOperations.all fun operation =>
      !Fir.Wasm.Emit.ResidentRuntime.supportsClosureProjection operation do
    throwError "resident Format retained a supported closure-projection import"
  unless residentClosureArtifact.module.imports.size + closureProjections.size ==
      residentProjectionArtifact.module.imports.size do
    throwError "resident Format closure-projection import accounting changed"
  unless residentClosureArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch do
    throwError "resident linking changed the stable closure-dispatch table"
  unless residentClosureArtifact.module.closureDescriptors ==
      moduleArtifact.module.closureDescriptors do
    throwError "resident linking changed the stable closure-descriptor table"
  unless expectedClosureCoordinates.all fun coordinate =>
      let operation : Fir.Wasm.RuntimeOp :=
        .closureProj `resident (coordinate.1 + 2) (coordinate.1 + 1)
          coordinate.1 coordinate.2
      (Fir.Wasm.Emit.ResidentRuntime.closureProjectionName? operation).any
        residentClosureArtifact.module.exports.contains do
    throwError "resident Format closure-projection helper exports changed"
  match ← residentClosureArtifact.write
      "_build/source-pretty-format-resident-closure-projections.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident closure-projection Format module: {repr error}"
  let closureMatches := residentClosureArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentRuntime.isClosureMatch
  unless closureMatches.size == 77 do
    throwError "resident Format closure-match inventory changed"
  let residentMatchArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeClosureMatches
        residentClosureArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident closure-match Format facade: {repr error}"
  unless residentMatchArtifact.module.runtimeOperations.all fun operation =>
      !Fir.Wasm.Emit.ResidentRuntime.isClosureMatch operation do
    throwError "resident Format retained a closure-match import"
  unless residentMatchArtifact.module.imports.size + closureMatches.size ==
      residentClosureArtifact.module.imports.size do
    throwError "resident Format closure-match import accounting changed"
  unless residentMatchArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch do
    throwError "closure-match linking changed the stable closure-dispatch table"
  unless residentMatchArtifact.module.closureDescriptors ==
      moduleArtifact.module.closureDescriptors do
    throwError "closure-match linking changed the stable closure-descriptor table"
  unless closureMatches.all fun operation =>
      (Fir.Wasm.Emit.ResidentRuntime.closureMatchName?
        residentMatchArtifact.module.closureDispatch operation).any
          residentMatchArtifact.module.exports.contains do
    throwError "resident Format closure-match helper exports changed"
  match ← residentMatchArtifact.write
      "_build/source-pretty-format-resident-closure-matches.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident closure-match Format module: {repr error}"
  let residentAllocatorArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.installAllocator
        residentMatchArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident-allocator Format facade: {repr error}"
  unless residentAllocatorArtifact.module.imports ==
      residentMatchArtifact.module.imports do
    throwError "resident allocator changed the semantic import frontier"
  unless residentAllocatorArtifact.module.runtimeOperations ==
      residentMatchArtifact.module.runtimeOperations do
    throwError "resident allocator changed the semantic runtime inventory"
  unless residentAllocatorArtifact.module.globals.size ==
      residentMatchArtifact.module.globals.size + 1 do
    throwError "resident allocator global accounting changed"
  unless Fir.Wasm.Emit.ResidentAllocator.helperNames.all
      residentAllocatorArtifact.module.exports.contains do
    throwError "resident allocator helper exports changed"
  match ← residentAllocatorArtifact.write
      "_build/source-pretty-format-resident-allocator.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident-allocator Format module: {repr error}"
  let constructors := residentAllocatorArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentConstructor.isConstructor
  unless constructors.size == 23 do
    throwError "resident Format constructor-allocation inventory changed"
  let residentConstructorArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeConstructors
        residentAllocatorArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident-constructor Format facade: {repr error}"
  unless residentConstructorArtifact.module.runtimeOperations.all fun operation =>
      !Fir.Wasm.Emit.ResidentConstructor.isConstructor operation do
    throwError "resident Format retained a constructor-allocation import"
  unless residentConstructorArtifact.module.imports.size + constructors.size ==
      residentAllocatorArtifact.module.imports.size do
    throwError "resident Format constructor import accounting changed"
  unless residentConstructorArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch do
    throwError "constructor linking changed the stable closure-dispatch table"
  unless residentConstructorArtifact.module.closureDescriptors ==
      moduleArtifact.module.closureDescriptors do
    throwError "constructor linking changed the stable closure-descriptor table"
  unless (List.range constructors.size).all fun ordinal =>
      residentConstructorArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentConstructor.constructorName ordinal) do
    throwError "resident Format constructor helper exports changed"
  match ← residentConstructorArtifact.write
      "_build/source-pretty-format-resident-constructors.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident-constructor Format module: {repr error}"
  let naturals := residentConstructorArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentLiteral.isImmediateNatural
  unless naturals.size == 2 do
    throwError "resident Format immediate-Natural inventory changed"
  let residentNaturalArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeImmediateNaturals
        residentConstructorArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident-Natural Format facade: {repr error}"
  unless residentNaturalArtifact.module.runtimeOperations.all fun operation =>
      !Fir.Wasm.Emit.ResidentLiteral.isImmediateNatural operation do
    throwError "resident Format retained an immediate-Natural import"
  unless (residentNaturalArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentLiteral.isStringLiteral).size == 4 do
    throwError "resident Format moved strings across the host boundary"
  unless residentNaturalArtifact.module.imports.size + naturals.size ==
      residentConstructorArtifact.module.imports.size do
    throwError "resident Format immediate-Natural import accounting changed"
  unless residentNaturalArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch do
    throwError "Natural linking changed the stable closure-dispatch table"
  unless residentNaturalArtifact.module.closureDescriptors ==
      moduleArtifact.module.closureDescriptors do
    throwError "Natural linking changed the stable closure-descriptor table"
  unless (List.range naturals.size).all fun ordinal =>
      residentNaturalArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentLiteral.naturalName ordinal) do
    throwError "resident Format Natural helper exports changed"
  match ← residentNaturalArtifact.write
      "_build/source-pretty-format-resident-naturals.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident-Natural Format module: {repr error}"
  let partialApplications :=
    residentNaturalArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentClosureAllocation.isPartialApplication
  unless partialApplications.size == 87 do
    throwError "resident Format partial-application inventory changed"
  let residentPartialApplicationArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizePartialApplications
        residentNaturalArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError
          "failed to compile resident partial-application Format facade: {repr error}"
  unless residentPartialApplicationArtifact.module.imports.size == 65 &&
      residentPartialApplicationArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentClosureAllocation.isPartialApplication operation do
    throwError "resident Format partial-application frontier changed"
  unless residentPartialApplicationArtifact.module.imports.size +
      partialApplications.size == residentNaturalArtifact.module.imports.size do
    throwError "resident Format partial-application import accounting changed"
  unless (residentPartialApplicationArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentLiteral.isStringLiteral).size == 4 do
    throwError "resident Format moved strings across the host boundary"
  unless residentPartialApplicationArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch &&
      residentPartialApplicationArtifact.module.closureDescriptors ==
        moduleArtifact.module.closureDescriptors do
    throwError "partial-application linking changed stable closure metadata"
  unless (List.range partialApplications.size).all fun ordinal =>
      residentPartialApplicationArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentClosureAllocation.partialApplicationName ordinal) do
    throwError "resident Format partial-application helper exports changed"
  match ← residentPartialApplicationArtifact.write
      "_build/source-pretty-format-resident-partial-applications.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError
        "failed to write resident partial-application Format module: {repr error}"
  let setters := residentPartialApplicationArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentMutation.isSetter
  unless setters.size == 11 do
    throwError "resident Format setter inventory changed"
  let residentSetterArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeSetters
        residentPartialApplicationArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident setter Format facade: {repr error}"
  unless residentSetterArtifact.module.imports.size == 54 &&
      residentSetterArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentMutation.isSetter operation do
    throwError "resident Format setter frontier changed"
  unless residentSetterArtifact.module.imports.size + setters.size ==
      residentPartialApplicationArtifact.module.imports.size do
    throwError "resident Format setter import accounting changed"
  unless residentSetterArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch &&
      residentSetterArtifact.module.closureDescriptors ==
        moduleArtifact.module.closureDescriptors do
    throwError "resident setter linking changed stable closure metadata"
  unless (List.range setters.size).all fun ordinal =>
      residentSetterArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentMutation.setterName ordinal) do
    throwError "resident Format setter helper exports changed"
  match ← residentSetterArtifact.write
      "_build/source-pretty-format-resident-setters.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident setter Format module: {repr error}"
  let increments :=
    residentSetterArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentReferenceCount.isIncrement
  unless increments.size == 4 do
    throwError "resident Format increment inventory changed"
  let residentIncrementArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeIncrements
        residentSetterArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident increment Format facade: {repr error}"
  unless residentIncrementArtifact.module.imports.size == 50 &&
      residentIncrementArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentReferenceCount.isIncrement operation do
    throwError "resident Format increment frontier changed"
  unless residentIncrementArtifact.module.imports.size + increments.size ==
      residentSetterArtifact.module.imports.size do
    throwError "resident Format increment import accounting changed"
  unless residentIncrementArtifact.module.closureDispatch ==
      moduleArtifact.module.closureDispatch &&
      residentIncrementArtifact.module.closureDescriptors ==
        moduleArtifact.module.closureDescriptors do
    throwError "resident increment linking changed stable closure metadata"
  unless (List.range increments.size).all fun ordinal =>
      residentIncrementArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentReferenceCount.incrementName ordinal) do
    throwError "resident Format increment helper exports changed"
  match ← residentIncrementArtifact.write
      "_build/source-pretty-format-resident-increments.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident increment Format module: {repr error}"
  let releases := residentIncrementArtifact.module.runtimeOperations.filter
    Fir.Wasm.Emit.ResidentRelease.isRelease
  unless releases.size == 6 do
    throwError "resident Format recursive-release inventory changed"
  let residentReleaseArtifact ← match
      Fir.Wasm.Emit.ResidentPrettyFormat.internalizeReleases
        residentIncrementArtifact with
    | .ok artifact => pure artifact
    | .error error =>
        throwError "failed to compile resident release Format facade: {repr error}"
  unless residentReleaseArtifact.module.imports.size == 44 &&
      residentReleaseArtifact.module.runtimeOperations.all fun operation =>
        !Fir.Wasm.Emit.ResidentRelease.isRelease operation do
    throwError "resident Format recursive-release frontier changed"
  unless residentReleaseArtifact.module.imports.size + releases.size ==
      residentIncrementArtifact.module.imports.size do
    throwError "resident Format recursive-release import accounting changed"
  unless residentReleaseArtifact.module.closureDispatch ==
      residentIncrementArtifact.module.closureDispatch &&
      residentReleaseArtifact.module.closureDescriptors ==
        residentIncrementArtifact.module.closureDescriptors do
    throwError "resident release linking changed stable closure metadata"
  unless (List.range releases.size).all fun ordinal =>
      residentReleaseArtifact.module.exports.contains
        (Fir.Wasm.Emit.ResidentRelease.releaseName ordinal) do
    throwError "resident Format recursive-release helper exports changed"
  match ← residentReleaseArtifact.write
      "_build/source-pretty-format-resident-releases.wasm" with
  | .ok () => pure ()
  | .error error =>
      throwError "failed to write resident release Format module: {repr error}"
  unless (residentReleaseArtifact.module.runtimeOperations.filter
      Fir.Wasm.Emit.ResidentMutation.isTagSetter).isEmpty do
    throwError "text Format unexpectedly retained a constructor-tag setter"
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
