import Fir.Validation.Corpus
import Fir.LeanIR.Checkpoint
import Fir.LeanIR.Interpreter
import Lean.Compiler.LCNF
import Lean.Compiler.LCNF.EmitUtil

namespace Fir.Validation.Lcnf

open Lean
open Lean.Compiler
open Fir.LeanIR
open Fir.LeanIR.Impure

/-- Compiler output retained by the validation harness for execution and coverage reporting. -/
structure Artifact where
  entry : Name
  program : ImpureProgram
  externalNames : Array Name
  forms : Array String

private def pushUnique (forms : Array String) (form : String) : Array String :=
  if forms.contains form then forms else forms.push form

private def addForms (forms : Array String) (more : Array String) : Array String :=
  more.foldl (init := forms) pushUnique

private def letValueForms : LCNF.LetValue .impure -> Array String
  | .lit _ => #["lit"]
  | .erased => #["erased"]
  | .proj .. => #["proj"]
  | .const .. => #["const"]
  | .fvar .. => #["fvar"]
  | .ctor .. => #["ctor"]
  | .oproj .. => #["oproj"]
  | .uproj .. => #["uproj"]
  | .sproj .. => #["sproj"]
  | .fap .. => #["fap"]
  | .pap .. => #["pap"]
  | .reset .. => #["reset"]
  | .reuse .. => #["reuse"]
  | .box .. => #["box"]
  | .unbox .. => #["unbox"]
  | .isShared .. => #["isShared"]

private partial def codeForms : LCNF.Code .impure -> Array String
  | .let decl k => addForms (letValueForms decl.value) (codeForms k)
  | .fun decl k _ => addForms #["fun"] (addForms (codeForms decl.value) (codeForms k))
  | .jp decl k => addForms #["join"] (addForms (codeForms decl.value) (codeForms k))
  | .jmp .. => #["jump"]
  | .cases cases =>
      cases.alts.foldl (init := #["cases"]) fun forms alt =>
        addForms forms (codeForms alt.getCode)
  | .return _ => #["return"]
  | .unreach _ => #["unreach"]
  | .oset (k := k) .. => addForms #["oset"] (codeForms k)
  | .uset (k := k) .. => addForms #["uset"] (codeForms k)
  | .sset (k := k) .. => addForms #["sset"] (codeForms k)
  | .setTag (k := k) .. => addForms #["setTag"] (codeForms k)
  | .inc (k := k) .. => addForms #["inc"] (codeForms k)
  | .dec (k := k) .. => addForms #["dec"] (codeForms k)
  | .del (k := k) .. => addForms #["del"] (codeForms k)

def collectForms (program : ImpureProgram) : Array String :=
  program.decls.foldl (init := #[]) fun forms decl =>
    match decl.value with
    | .code code => addForms forms (codeForms code)
    | .extern _ => pushUnique forms "extern"

def Artifact.missingForms (artifact : Artifact) (required : Array String) : Array String :=
  required.filter (!artifact.forms.contains ·)

/-- Stable human-readable compiler artifact retained beside the machine result. -/
def Artifact.format (artifact : Artifact) : CoreM String := do
  let declarations ← artifact.program.decls.mapM fun decl => do
    return toString (← LCNF.ppDecl' decl .impure)
  return String.intercalate "\n\n" declarations.toList

private def externDecl (sig : LCNF.Signature .impure) (data : ExternAttrData) :
    LCNF.Decl .impure :=
  { name := sig.name
    levelParams := sig.levelParams
    type := sig.type
    params := sig.params
    safe := sig.safe
    value := .extern data
    inlineAttr? := none }

/-- Compile an entry and retain its complete local dependency closure plus imported extern stubs. -/
def compileEntry (entry : Name) (dependencies : Array Name := #[]) : CoreM Artifact := do
  let roots := #[entry] ++ dependencies
  LCNF.main roots (← getOptions)
  let (localDecls, externalSigs) ← LCNF.collectUsedDecls roots
  let env ← getEnv
  let externalDecls := externalSigs.map fun sig =>
    let data := getExternAttrData? env sig.name |>.getD { entries := [.opaque] }
    externDecl sig data
  let program : ImpureProgram := { decls := localDecls ++ externalDecls }
  return {
    entry
    program
    externalNames := externalSigs.map (·.name)
    forms := collectForms program }

private def mismatch (expected : ValidationSchema) (actual : ValidationDatum) : Except String α :=
  .error s!"datum does not match schema: expected {repr expected}, got {repr actual}"

private partial def encodeDatum (runtime : RuntimeState) (schema : ValidationSchema)
    (datum : ValidationDatum) : Except String (RuntimeState × Value) := do
  if !schema.accepts datum then mismatch schema datum
  match schema, datum with
  | .unit, .unit => return (runtime, .object (.tagged 0))
  | .bool, .bool value => return (runtime, .object (.tagged (if value then 1 else 0)))
  | .nat, .nat value => return literal runtime (.nat value)
  | .usize, .usize value => return (runtime, .usize value)
  | .bits 8, .bits _ value => return (runtime, .scalar (.uint8 value.toUInt8))
  | .bits 16, .bits _ value => return (runtime, .scalar (.uint16 value.toUInt16))
  | .bits 32, .bits _ value => return (runtime, .scalar (.uint32 value.toUInt32))
  | .bits 64, .bits _ value => return (runtime, .scalar (.uint64 value))
  | .string, .string value =>
      let (runtime, reference) := alloc runtime (.string value)
      return (runtime, .object reference)
  | .seq element, .seq values =>
      values.foldrM (init := (runtime, .object (.tagged 0))) fun datum (runtime, tail) => do
        let (runtime, head) ← encodeDatum runtime element datum
        allocCtor runtime { name := ``List.cons, cidx := 1, size := 2, usize := 0, ssize := 0 }
          #[head, tail] |>.mapError (fun fault => toString (repr fault))
  | .ctor name tag schemas, .ctor _ _ fields =>
      let (runtime, values) ← schemas.zip fields |>.foldlM (init := (runtime, #[]))
        fun (runtime, values) (schema, field) => do
          let (runtime, value) ← encodeDatum runtime schema field
          return (runtime, values.push value)
      allocCtor runtime {
        name := Name.mkSimple name, cidx := tag, size := values.size, usize := 0, ssize := 0 }
        values |>.mapError (fun fault => toString (repr fault))
  | _, _ => mismatch schema datum

def encodeArgs (schemas : Array ValidationSchema) (data : Array ValidationDatum) :
    Except String (RuntimeState × Array Value) := do
  if schemas.size != data.size then
    throw s!"argument schema/fixture arity mismatch: {schemas.size} schemas, {data.size} values"
  schemas.zip data |>.foldlM (init := ({}, #[])) fun (runtime, values) (schema, datum) => do
    let (runtime, value) ← encodeDatum runtime schema datum
    return (runtime, values.push value)

private partial def decodeValue (runtime : RuntimeState) (schema : ValidationSchema)
    (value : Value) : Except String ValidationDatum := do
  match schema, value with
  | .unit, .object (.tagged 0) => return .unit
  | .bool, .object (.tagged value) =>
      if value == 0 then return .bool false
      else if value == 1 then return .bool true
      else throw s!"invalid Bool tag {value}"
  | .nat, .object (.tagged value) => return .nat value.toNat
  | .nat, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .natural value := cell.object | throw "expected a natural heap object"
      return .nat value
  | .usize, .usize value => return .usize value
  | .bits 8, .scalar (.uint8 value) => return .bits 8 (UInt64.ofNat value.toNat)
  | .bits 16, .scalar (.uint16 value) => return .bits 16 (UInt64.ofNat value.toNat)
  | .bits 32, .scalar (.uint32 value) => return .bits 32 (UInt64.ofNat value.toNat)
  | .bits 64, .scalar (.uint64 value) => return .bits 64 value
  | .string, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .string value := cell.object | throw "expected a string heap object"
      return .string value
  | .seq _, .object (.tagged 0) => return .seq #[]
  | .seq element, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .ctor object := cell.object | throw "expected a List constructor"
      if object.tag != 1 || object.objectFields.size != 2 then throw "expected List.cons"
      let head ← decodeValue runtime element object.objectFields[0]!
      let .seq tail ← decodeValue runtime (.seq element) object.objectFields[1]!
        | throw "expected List tail"
      return .seq (#[head] ++ tail)
  | .ctor name tag schemas, .object (.tagged actualTag) =>
      if schemas.isEmpty && actualTag.toNat == tag then return .ctor name tag #[]
      else throw s!"constructor tag/arity mismatch for {name}"
  | .ctor name tag schemas, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .ctor object := cell.object | throw s!"expected constructor {name}"
      if object.tag != tag || object.objectFields.size != schemas.size then
        throw s!"constructor tag/arity mismatch for {name}"
      let fields ← schemas.zip object.objectFields |>.mapM fun (schema, value) =>
        decodeValue runtime schema value
      return .ctor name tag fields
  | _, _ => throw s!"cannot decode {repr value} as {repr schema}"

private def faultKind : RuntimeFault -> String
  | .unknownVar .. => "unknown-var"
  | .unknownDecl .. => "unknown-decl"
  | .unknownJoinPoint .. => "unknown-join-point"
  | .arityMismatch .. => "arity-mismatch"
  | .deadObject .. => "dead-object"
  | .expectedObject => "expected-object"
  | .expectedConstructor => "expected-constructor"
  | .expectedClosure => "expected-closure"
  | .expectedScalar => "expected-scalar"
  | .expectedUSize => "expected-usize"
  | .expectedReuseToken => "expected-reuse-token"
  | .objectFieldOutOfBounds .. => "object-field-out-of-bounds"
  | .usizeFieldOutOfBounds .. => "usize-field-out-of-bounds"
  | .scalarFieldMissing .. => "scalar-field-missing"
  | .invalidCases => "invalid-cases"
  | .referenceCountUnderflow .. => "reference-count-underflow"
  | .expectedHeapReference => "expected-heap-reference"
  | .externalFailure .. => "external-failure"
  | .unreachable => "unreachable"
  | .malformed .. => "malformed"

def execute (case : Corpus.Case) (artifact : Artifact) : BackendResult :=
  let diagnostics := #[
    { key := "declarations", value := toString artifact.program.decls.size },
    { key := "externals", value := String.intercalate "," (artifact.externalNames.toList.map toString) },
    { key := "lcnf-forms", value := String.intercalate "," artifact.forms.toList },
    { key := "missing-lcnf-forms",
      value := String.intercalate "," (artifact.missingForms case.requiredLcnfForms).toList }]
  match encodeArgs case.argSchemas case.args with
  | .error message => { caseId := case.id, backend := "lcnf", outcome := .failure message, diagnostics }
  | .ok (runtime, args) =>
      match runProgram case.fuel rejectExternals artifact.program case.entry args runtime with
      | .outOfFuel _ =>
          { caseId := case.id, backend := "lcnf", outcome := .outOfFuel case.fuel, diagnostics }
      | .done observation =>
          match observation.outcome with
          | .fault fault =>
              { caseId := case.id, backend := "lcnf",
                outcome := .success {
                  termination := .runtimeFault (faultKind fault) (toString (repr fault)) },
                diagnostics }
          | .returned value =>
              let finalRuntime : RuntimeState := {
                runtime with
                heap := observation.heap
                world := observation.world
                trace := observation.trace }
              match decodeValue finalRuntime case.resultSchema value with
              | .error message =>
                  { caseId := case.id, backend := "lcnf", outcome := .failure message, diagnostics }
              | .ok datum =>
                  { caseId := case.id, backend := "lcnf",
                    outcome := .success { termination := .returned datum }, diagnostics }

def runCase (case : Corpus.Case) : CoreM (BackendResult × Artifact) := do
  let artifact ← compileEntry case.entry case.dependencies
  return (execute case artifact, artifact)

end Fir.Validation.Lcnf
