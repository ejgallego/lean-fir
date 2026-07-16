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

private def letValueForm : LCNF.LetValue .impure -> String
  | .lit _ => "lit"
  | .erased => "erased"
  | .proj .. => "proj"
  | .const .. => "const"
  | .fvar .. => "fvar"
  | .ctor .. => "ctor"
  | .oproj .. => "oproj"
  | .uproj .. => "uproj"
  | .sproj .. => "sproj"
  | .fap .. => "fap"
  | .pap .. => "pap"
  | .reset .. => "reset"
  | .reuse .. => "reuse"
  | .box .. => "box"
  | .unbox .. => "unbox"
  | .isShared .. => "isShared"

private def codeHeadForm : LCNF.Code .impure → String
  | .let decl _ => letValueForm decl.value
  | .fun .. => "fun"
  | .jp .. => "join"
  | .jmp .. => "jump"
  | .cases .. => "cases"
  | .return .. => "return"
  | .unreach .. => "unreach"
  | .oset .. => "oset"
  | .uset .. => "uset"
  | .sset .. => "sset"
  | .setTag .. => "setTag"
  | .inc .. => "inc"
  | .dec .. => "dec"
  | .del .. => "del"

private partial def codeForms (code : LCNF.Code .impure) : Array String :=
  let own := #[codeHeadForm code]
  match code with
  | .let _ k => addForms own (codeForms k)
  | .fun decl k _ => addForms own (addForms (codeForms decl.value) (codeForms k))
  | .jp decl k => addForms own (addForms (codeForms decl.value) (codeForms k))
  | .jmp .. => own
  | .cases cases =>
      cases.alts.foldl (init := own) fun forms alt =>
        addForms forms (codeForms alt.getCode)
  | .return _ | .unreach _ => own
  | .oset (k := k) .. | .uset (k := k) .. | .sset (k := k) .. |
      .setTag (k := k) .. | .inc (k := k) .. | .dec (k := k) .. | .del (k := k) .. =>
      addForms own (codeForms k)

def collectForms (program : ImpureProgram) : Array String :=
  program.decls.foldl (init := #[]) fun forms decl =>
    match decl.value with
    | .code code => addForms forms (codeForms code)
    | .extern _ => pushUnique forms "extern"

def Artifact.missingForms (artifact : Artifact) (required : Array String) : Array String :=
  required.filter (!artifact.forms.contains ·)

private def executedForm? (state : MachineState) : Option String :=
  match state.control with
  | .code code => some (codeHeadForm code)
  | .yielded .. => none
  | .invokeName .. | .invokeValue .. =>
      match coreStep state with
      | .external .. => some "extern"
      | _ => none

private structure InstrumentedRun where
  result : RunResult
  executedForms : Array String
  steps : Nat

/-- Validation-only telemetry layered over the canonical interpreter transition function. -/
private def runInstrumentedGo (externals : ExternalImpl) :
    Nat → MachineState → Array String → Nat → InstrumentedRun
  | 0, state, forms, steps => { result := .outOfFuel state, executedForms := forms, steps }
  | fuel + 1, state, forms, steps =>
      let forms := match executedForm? state with
        | some form => pushUnique forms form
        | none => forms
      match executeStep externals state with
      | .done observation => { result := .done observation, executedForms := forms, steps := steps + 1 }
      | .next state => runInstrumentedGo externals fuel state forms (steps + 1)

private def runInstrumented (fuel : Nat) (externals : ExternalImpl) (state : MachineState) :
    InstrumentedRun :=
  runInstrumentedGo externals fuel state #[] 0

private theorem runInstrumentedGo_result (externals : ExternalImpl) :
    ∀ fuel state forms steps,
      (runInstrumentedGo externals fuel state forms steps).result = run fuel externals state
  | 0, state, forms, steps => by simp [runInstrumentedGo, run]
  | fuel + 1, state, forms, steps => by
      simp only [runInstrumentedGo, run]
      split <;> rename_i transition
      · simp [transition]
      · simpa [transition] using
          runInstrumentedGo_result externals fuel _ _ (steps + 1)

private theorem runInstrumented_result (fuel : Nat) (externals : ExternalImpl)
    (state : MachineState) :
    (runInstrumented fuel externals state).result = run fuel externals state := by
  exact runInstrumentedGo_result externals fuel state #[] 0

private def runProgramInstrumented (fuel : Nat) (externals : ExternalImpl)
    (program : ImpureProgram) (entry : Name) (args : Array Value)
    (runtime : RuntimeState := {}) : InstrumentedRun :=
  runInstrumented fuel externals (initialState program entry args runtime)

private def externalNat (request : ExternalRequest) (runtime : RuntimeState)
    (value : Value) : Except RuntimeFault Nat := do
  match value with
  | .object (.tagged value) => return value.toNat
  | .object (.heap location) =>
      let cell ← getLiveCell runtime location
      let .natural value := cell.object
        | throw (.externalFailure request.name "expected a natural number")
      return value
  | _ => throw (.externalFailure request.name "expected a natural number")

private def natAddExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalNat request runtime left
  let right ← externalNat request runtime right
  let (runtime, value) := literal runtime (.nat (left + right))
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

/-- Pure runtime primitives explicitly modeled by the validation backend. -/
private def validationExternals : ExternalImpl where
  call request runtime :=
    if request.name == ``Nat.add then
      natAddExternal request runtime
    else
      .error (.externalFailure request.name "external is not in the validation allowlist")

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

private def int32SignBit : Nat := 2147483648

private def int32Mask : Nat := 4294967295

/-- Encode Lean's immediate signed-32-bit `Int` payload used by final impure LCNF. -/
private def encodeImmediateInt (runtime : RuntimeState) (value : Int) :
    Except String (RuntimeState × Value) :=
  match value with
  | .ofNat value =>
      if value < int32SignBit then
        .ok (runtime, .object (.tagged (UInt64.ofNat value)))
      else
        .error s!"Int value {value} requires an mpz heap object"
  | .negSucc value =>
      if value < int32SignBit then
        .ok (runtime, .object (.tagged (UInt64.ofNat (int32Mask - value))))
      else
        .error s!"negative Int payload {value} requires an mpz heap object"

private def decodeImmediateInt (payload : UInt64) : Except String Int := do
  let payload := payload.toNat
  if payload > int32Mask then
    throw s!"invalid immediate Int payload {payload}"
  if payload < int32SignBit then
    return .ofNat payload
  return .negSucc (int32Mask - payload)

private partial def encodeDatum (runtime : RuntimeState) (schema : ValidationSchema)
    (datum : ValidationDatum) : Except String (RuntimeState × Value) := do
  if !schema.accepts datum then mismatch schema datum
  match schema, datum with
  | .unit, .unit => return (runtime, .object (.tagged 0))
  | .bool, .bool value => return (runtime, .object (.tagged (if value then 1 else 0)))
  | .nat, .nat value => return literal runtime (.nat value)
  | .int, .int value => encodeImmediateInt runtime value
  | .usize, .usize value => return (runtime, .usize value)
  | .bits 8, .bits _ value => return (runtime, .scalar (.uint8 value.toUInt8))
  | .bits 16, .bits _ value => return (runtime, .scalar (.uint16 value.toUInt16))
  | .bits 32, .bits _ value => return (runtime, .scalar (.uint32 value.toUInt32))
  | .bits 64, .bits _ value => return (runtime, .scalar (.uint64 value))
  | .string, .string value =>
      let (runtime, reference) := alloc runtime (.string value)
      return (runtime, .object reference)
  | .bytes, .bytes values =>
      let bytes := values.map (UInt8.ofNat ·)
      let (runtime, reference) := alloc runtime (.byteArray bytes)
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
  | .int, .object (.tagged payload) => return .int (← decodeImmediateInt payload)
  | .usize, .usize value => return .usize value
  | .bits 8, .scalar (.uint8 value) => return .bits 8 (UInt64.ofNat value.toNat)
  | .bits 16, .scalar (.uint16 value) => return .bits 16 (UInt64.ofNat value.toNat)
  | .bits 32, .scalar (.uint32 value) => return .bits 32 (UInt64.ofNat value.toNat)
  | .bits 64, .scalar (.uint64 value) => return .bits 64 value
  | .string, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .string value := cell.object | throw "expected a string heap object"
      return .string value
  | .bytes, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .byteArray value := cell.object | throw "expected a byte-array heap object"
      return .bytes (value.map (UInt8.toNat ·))
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
  let staticDiagnostics := #[
    { key := "declarations", value := toString artifact.program.decls.size },
    { key := "externals", value := String.intercalate "," (artifact.externalNames.toList.map toString) },
    { key := "lcnf-forms", value := String.intercalate "," artifact.forms.toList },
    { key := "missing-lcnf-forms",
      value := String.intercalate "," (artifact.missingForms case.requiredLcnfForms).toList }]
  match encodeArgs case.argSchemas case.args with
  | .error message =>
      { caseId := case.id, backend := "lcnf", outcome := .failure message,
        diagnostics := staticDiagnostics }
  | .ok (runtime, args) =>
      let execution :=
        runProgramInstrumented case.fuel validationExternals artifact.program case.entry args runtime
      let missingExecuted := case.requiredExecutedLcnfForms.filter
        (!execution.executedForms.contains ·)
      let diagnostics := staticDiagnostics ++ #[
        { key := "executed-lcnf-forms",
          value := String.intercalate "," execution.executedForms.toList },
        { key := "missing-executed-lcnf-forms",
          value := String.intercalate "," missingExecuted.toList },
        { key := "interpreter-steps", value := toString execution.steps }]
      match execution.result with
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
