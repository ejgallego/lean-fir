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

private def pushUniqueName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

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

def Artifact.missingExternals (artifact : Artifact) (required : Array Name) : Array Name :=
  required.filter (!artifact.externalNames.contains ·)

private def externalRequest? (state : MachineState) : Option ExternalRequest :=
  match state.control with
  | .invokeName .. | .invokeValue .. =>
      match coreStep state with
      | .external request _ => some request
      | _ => none
  | _ => none

private def executedForm? (state : MachineState) : Option String :=
  match state.control with
  | .code code => some (codeHeadForm code)
  | .yielded .. => none
  | .invokeName .. | .invokeValue .. =>
      if (externalRequest? state).isSome then some "extern" else none

private def executedStepKind (state : MachineState) (executedForm : Option String) : String :=
  match executedForm with
  | some form => "form:" ++ form
  | none =>
      match state.control with
      | .yielded _ =>
          match state.frames with
          | [] => "admin:yield-done"
          | .bind .. :: _ => "admin:yield-bind"
          | .apply .. :: _ => "admin:yield-apply"
          | .cache .. :: _ => "admin:yield-cache"
      | .invokeName .. => "admin:invoke-name"
      | .invokeValue .. => "admin:invoke-value"
      | .code .. => "admin:unclassified"

/-- Heap states on either side of one successful external call, retained for effect decoding. -/
private structure ExternalSnapshot where
  event : ExternalEvent
  before : RuntimeState
  after : RuntimeState

private structure ExecutedFormCount where
  form : String
  count : Nat
  deriving Lean.ToJson

private def incrementFormCount (counts : Array ExecutedFormCount)
    (form : String) : Array ExecutedFormCount :=
  if counts.any (·.form == form) then
    counts.map fun entry =>
      if entry.form == form then { entry with count := entry.count + 1 } else entry
  else
    counts.push { form, count := 1 }

private structure ExecutedExternalCount where
  external : String
  count : Nat
  deriving Lean.ToJson

private def incrementExternalCount (counts : Array ExecutedExternalCount)
    (external : Name) : Array ExecutedExternalCount :=
  let external := toString external
  if counts.any (·.external == external) then
    counts.map fun entry =>
      if entry.external == external then { entry with count := entry.count + 1 } else entry
  else
    counts.push { external, count := 1 }

private structure InstrumentedRun where
  result : RunResult
  executedForms : Array String
  executedFormTrace : Array String
  executedStepTrace : Array String
  executedFormCounts : Array ExecutedFormCount
  executedExternals : Array Name
  executedExternalTrace : Array Name
  executedExternalCounts : Array ExecutedExternalCount
  externalSnapshots : Array ExternalSnapshot
  steps : Nat

/-- Validation-only telemetry layered over the canonical interpreter transition function. -/
private def runInstrumentedGo (externals : ExternalImpl) :
    Nat → MachineState → Array String → Array String → Array String →
      Array ExecutedFormCount → Array Name → Array Name → Array ExecutedExternalCount →
      Array ExternalSnapshot → Nat → InstrumentedRun
  | 0, state, forms, formTrace, stepTrace, formCounts, externalNames, externalTrace,
      externalCounts, externalSnapshots, steps =>
      { result := .outOfFuel state, executedForms := forms,
        executedFormTrace := formTrace, executedStepTrace := stepTrace,
        executedFormCounts := formCounts,
        executedExternals := externalNames, executedExternalTrace := externalTrace,
        executedExternalCounts := externalCounts,
        externalSnapshots, steps }
  | fuel + 1, state, forms, formTrace, stepTrace, formCounts, externalNames,
      externalTrace, externalCounts, externalSnapshots, steps =>
      let executedForm := executedForm? state
      let forms := match executedForm with
        | some form => pushUnique forms form
        | none => forms
      let formTrace := match executedForm with
        | some form => formTrace.push form
        | none => formTrace
      let stepTrace := stepTrace.push (executedStepKind state executedForm)
      let formCounts := match executedForm with
        | some form => incrementFormCount formCounts form
        | none => formCounts
      let request? := externalRequest? state
      let externalNames := match request? with
        | some request => pushUniqueName externalNames request.name
        | none => externalNames
      let externalTrace := match request? with
        | some request => externalTrace.push request.name
        | none => externalTrace
      let externalCounts := match request? with
        | some request => incrementExternalCount externalCounts request.name
        | none => externalCounts
      match executeStep externals state with
      | .done observation =>
          { result := .done observation, executedForms := forms,
            executedFormTrace := formTrace, executedStepTrace := stepTrace,
            executedFormCounts := formCounts,
            executedExternals := externalNames, executedExternalTrace := externalTrace,
            executedExternalCounts := externalCounts,
            externalSnapshots, steps := steps + 1 }
      | .next nextState =>
          let externalSnapshots := match request?, nextState.runtime.trace.back? with
            | some request, some event =>
                if event.name == request.name then
                  externalSnapshots.push {
                    event
                    before := state.runtime
                    after := nextState.runtime }
                else externalSnapshots
            | _, _ => externalSnapshots
          runInstrumentedGo externals fuel nextState forms formTrace stepTrace formCounts
            externalNames externalTrace externalCounts externalSnapshots (steps + 1)

private def runInstrumented (fuel : Nat) (externals : ExternalImpl) (state : MachineState) :
    InstrumentedRun :=
  runInstrumentedGo externals fuel state #[] #[] #[] #[] #[] #[] #[] #[] 0

private theorem runInstrumentedGo_result (externals : ExternalImpl) :
    ∀ fuel state forms formTrace stepTrace formCounts externalNames externalTrace
      externalCounts externalSnapshots steps,
      (runInstrumentedGo externals fuel state forms formTrace stepTrace formCounts
        externalNames externalTrace externalCounts externalSnapshots steps).result =
        run fuel externals state
  | 0, state, forms, formTrace, stepTrace, formCounts, externalNames, externalTrace,
      externalCounts, externalSnapshots, steps => by
      simp [runInstrumentedGo, run]
  | fuel + 1, state, forms, formTrace, stepTrace, formCounts, externalNames,
      externalTrace, externalCounts, externalSnapshots, steps => by
      simp only [runInstrumentedGo, run]
      split <;> rename_i transition
      · simp [transition]
      · simpa [transition] using
          runInstrumentedGo_result externals fuel _ _ _ _ _ _ _ _ _ (steps + 1)

private theorem runInstrumented_result (fuel : Nat) (externals : ExternalImpl)
    (state : MachineState) :
    (runInstrumented fuel externals state).result = run fuel externals state := by
  exact runInstrumentedGo_result externals fuel state #[] #[] #[] #[] #[] #[] #[] #[] 0

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

private def externalStringCell (request : ExternalRequest) (runtime : RuntimeState)
    (value : Value) : Except RuntimeFault (Location × HeapCell × String) := do
  let .object (.heap location) := value
    | throw (.externalFailure request.name "expected a string")
  let cell ← getLiveCell runtime location
  let .string value := cell.object
    | throw (.externalFailure request.name "expected a string")
  return (location, cell, value)

private def externalString (request : ExternalRequest) (runtime : RuntimeState)
    (value : Value) : Except RuntimeFault String := do
  let (_, _, value) ← externalStringCell request runtime value
  return value

private def int32SignBit : Nat := 2147483648

private def int32Mask : Nat := 4294967295

private def immediateIntPayload? : Int → Option UInt64
  | .ofNat value =>
      if value < int32SignBit then some (UInt64.ofNat value) else none
  | .negSucc value =>
      if value < int32SignBit then some (UInt64.ofNat (int32Mask - value)) else none

/-- Encode Lean's signed-32-bit immediate `Int` ABI, falling back to an mpz-like heap object. -/
private def encodeIntValue (runtime : RuntimeState) (value : Int) : RuntimeState × Value :=
  match immediateIntPayload? value with
  | some payload => (runtime, .object (.tagged payload))
  | none =>
      let (runtime, reference) := alloc runtime (.integer value)
      (runtime, .object reference)

private def decodeImmediateInt (payload : UInt64) : Except String Int := do
  let payload := payload.toNat
  if payload > int32Mask then
    throw s!"invalid immediate Int payload {payload}"
  if payload < int32SignBit then
    return .ofNat payload
  return .negSucc (int32Mask - payload)

private def externalInt (request : ExternalRequest) (runtime : RuntimeState)
    (value : Value) : Except RuntimeFault Int := do
  match value with
  | .object (.tagged payload) =>
      match decodeImmediateInt payload with
      | .ok value => return value
      | .error message => throw (.externalFailure request.name message)
  | .object (.heap location) =>
      let cell ← getLiveCell runtime location
      let .integer value := cell.object
        | throw (.externalFailure request.name "expected a signed integer")
      return value
  | _ => throw (.externalFailure request.name "expected a signed integer")

private def externalByteArrayCell (request : ExternalRequest) (runtime : RuntimeState)
    (value : Value) : Except RuntimeFault (Location × HeapCell × Array UInt8) := do
  let .object (.heap location) := value
    | throw (.externalFailure request.name "expected a byte array")
  let cell ← getLiveCell runtime location
  let .byteArray value := cell.object
    | throw (.externalFailure request.name "expected a byte array")
  return (location, cell, value)

private def externalByteArray (request : ExternalRequest) (runtime : RuntimeState)
    (value : Value) : Except RuntimeFault (Array UInt8) := do
  let (_, _, value) ← externalByteArrayCell request runtime value
  return value

private structure FixedWidthValueCodec (α : Type) where
  name : String
  decode? : Value → Option α
  encode : α → Value

private def uint8Codec : FixedWidthValueCodec UInt8 where
  name := "UInt8"
  decode?
    | .scalar (.uint8 value) => some value
    | _ => none
  encode value := .scalar (.uint8 value)

private def int8Codec : FixedWidthValueCodec Int8 where
  name := "Int8"
  decode?
    | .scalar (.uint8 value) => some ⟨value⟩
    | _ => none
  encode value := .scalar (.uint8 value.toUInt8)

private def uint16Codec : FixedWidthValueCodec UInt16 where
  name := "UInt16"
  decode?
    | .scalar (.uint16 value) => some value
    | _ => none
  encode value := .scalar (.uint16 value)

private def int16Codec : FixedWidthValueCodec Int16 where
  name := "Int16"
  decode?
    | .scalar (.uint16 value) => some ⟨value⟩
    | _ => none
  encode value := .scalar (.uint16 value.toUInt16)

private def uint32Codec : FixedWidthValueCodec UInt32 where
  name := "UInt32"
  decode?
    | .scalar (.uint32 value) => some value
    | _ => none
  encode value := .scalar (.uint32 value)

private def int32Codec : FixedWidthValueCodec Int32 where
  name := "Int32"
  decode?
    | .scalar (.uint32 value) => some ⟨value⟩
    | _ => none
  encode value := .scalar (.uint32 value.toUInt32)

private def uint64Codec : FixedWidthValueCodec UInt64 where
  name := "UInt64"
  decode?
    | .scalar (.uint64 value) => some value
    | _ => none
  encode value := .scalar (.uint64 value)

private def int64Codec : FixedWidthValueCodec Int64 where
  name := "Int64"
  decode?
    | .scalar (.uint64 value) => some ⟨value⟩
    | _ => none
  encode value := .scalar (.uint64 value.toUInt64)

private def usizeCodec : FixedWidthValueCodec USize where
  name := "USize"
  decode?
    | .usize value => some value.toUSize
    | _ => none
  encode value := .usize value.toUInt64

private def isizeCodec : FixedWidthValueCodec ISize where
  name := "ISize"
  decode?
    | .usize value => some ⟨value.toUSize⟩
    | _ => none
  encode value := .usize value.toUSize.toUInt64

private def externalFixedWidthValue (codec : FixedWidthValueCodec α)
    (request : ExternalRequest) (value : Value) : Except RuntimeFault α :=
  match codec.decode? value with
  | some value => .ok value
  | none => .error (.externalFailure request.name s!"expected a {codec.name} value")

private def externalUInt8 (request : ExternalRequest) (value : Value) :
    Except RuntimeFault UInt8 :=
  externalFixedWidthValue uint8Codec request value

private def externalUInt32 (request : ExternalRequest) (value : Value) :
    Except RuntimeFault UInt32 :=
  externalFixedWidthValue uint32Codec request value

private def natBinaryExternal (operation : Nat → Nat → Nat)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalNat request runtime left
  let right ← externalNat request runtime right
  let (runtime, value) := literal runtime (.nat (operation left right))
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def natAddExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal (· + ·) request runtime

private def natSubExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal (· - ·) request runtime

private def natMulExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal (· * ·) request runtime

private def natDivExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal (· / ·) request runtime

private def natModExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal (· % ·) request runtime

private def natLandExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal Nat.land request runtime

private def natLorExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal Nat.lor request runtime

private def natXorExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal Nat.xor request runtime

private def natShiftLeftExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal Nat.shiftLeft request runtime

private def natShiftRightExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natBinaryExternal Nat.shiftRight request runtime

private def natDecisionExternal (operation : Nat → Nat → Bool)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalNat request runtime left
  let right ← externalNat request runtime right
  return {
    value := .scalar (.uint8 (if operation left right then 1 else 0))
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def natDecEqExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natDecisionExternal (fun left right => decide (left = right)) request runtime

private def natDecLtExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natDecisionExternal (fun left right => decide (left < right)) request runtime

private def natDecLeExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  natDecisionExternal (fun left right => decide (left ≤ right)) request runtime

private def stringToNatExternal (operation : String → Nat)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalString request runtime value
  let (runtime, value) := literal runtime (.nat (operation value))
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def stringLengthExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringToNatExternal String.length request runtime

private def stringUtf8ByteSizeExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringToNatExternal String.utf8ByteSize request runtime

private def stringPosOf (source : String) (needle : Char) : Nat :=
  let rec go : List Char → Nat → Nat
    | [], position => position
    | char :: chars, position =>
        if char == needle then position
        else go chars (position + char.utf8Size)
  go source.toList 0

private def stringOffsetOfPos (source : String) (target : Nat) : Nat :=
  let rec go : List Char → Nat → Nat → Nat
    | [], _, offset => offset
    | char :: chars, position, offset =>
        if position >= target then offset
        else go chars (position + char.utf8Size) (offset + 1)
  go source.toList 0 0

private def utf8Width (first : UInt8) : Nat :=
  let first := first.toNat
  if first < 0x80 then 1
  else if first < 0xc0 then 1
  else if first < 0xe0 then 2
  else if first < 0xf0 then 3
  else if first < 0xf8 then 4
  else 1

private def stringNext (source : String) (position : Nat) : Nat :=
  match source.toUTF8[position]? with
  | some first => position + utf8Width first
  | none => position + 1

private def stringExtract (source : String) (beginPos endPos : Nat) : String :=
  let rec take : List Char → Nat → List Char
    | [], _ => []
    | char :: chars, position =>
        if position == endPos then []
        else char :: take chars (position + char.utf8Size)
  let rec seek : List Char → Nat → List Char
    | [], _ => []
    | chars@(char :: tail), position =>
        if position == beginPos then take chars position
        else seek tail (position + char.utf8Size)
  if beginPos >= endPos then "" else String.ofList (seek source.toList 0)

private def stringAppend (left right : String) : String :=
  String.ofList (left.toList ++ right.toList)

private def stringPushn (source : String) (char : Char) (count : Nat) : String :=
  String.ofList (source.toList ++ List.replicate count char)

private def compareUtf8 : List UInt8 → List UInt8 → UInt8
  | [], [] => 1
  | [], _ => 0
  | _, [] => 2
  | left :: leftTail, right :: rightTail =>
      if left < right then 0
      else if right < left then 2
      else compareUtf8 leftTail rightTail

private def stringCompare (left right : String) : UInt8 :=
  compareUtf8 left.toUTF8.toList right.toUTF8.toList

private def bmpPrivateUseString : String :=
  String.ofList [Char.ofNat 0xe000]

private def supplementaryPlaneString : String :=
  String.ofList [Char.ofNat 0x10000]

private def stringCharToNatExternal (operation : String → Char → Nat)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [source, needle] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let source ← externalString request runtime source
  let needle ← externalUInt32 request needle
  let (runtime, value) := literal runtime (.nat (operation source (Char.ofNat needle.toNat)))
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def stringNatToNatExternal (operation : String → Nat → Nat)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [source, position] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let source ← externalString request runtime source
  let position ← externalNat request runtime position
  let (runtime, value) := literal runtime (.nat (operation source position))
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def stringPosOfExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringCharToNatExternal stringPosOf request runtime

private def stringOffsetOfPosExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringNatToNatExternal stringOffsetOfPos request runtime

private def stringNextExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringNatToNatExternal stringNext request runtime

private def stringExtractExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [source, beginPos, endPos] := request.args.toList
    | throw (.arityMismatch 3 request.args.size)
  let source ← externalString request runtime source
  let beginPos ← externalNat request runtime beginPos
  let endPos ← externalNat request runtime endPos
  let (runtime, reference) := alloc runtime (.string (stringExtract source beginPos endPos))
  return {
    value := .object reference
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def consumingStringResult (location : Location) (cell : HeapCell)
    (result : String) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  if !cell.persistent && cell.rc == 1 then
    let runtime ← setCell runtime location { cell with object := .string result }
    return {
      value := .object (.heap location)
      heap := runtime.heap
      nextLocation := runtime.nextLocation
      world := runtime.world }
  let runtime ← decLocation runtime location
  let (runtime, reference) := alloc runtime (.string result)
  return {
    value := .object reference
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def stringAppendExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [leftValue, rightValue] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let (location, cell, left) ← externalStringCell request runtime leftValue
  let right ← externalString request runtime rightValue
  consumingStringResult location cell (stringAppend left right) runtime

private def stringPushnExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [sourceValue, charValue, countValue] := request.args.toList
    | throw (.arityMismatch 3 request.args.size)
  let (location, cell, source) ← externalStringCell request runtime sourceValue
  let char ← externalUInt32 request charValue
  let count ← externalNat request runtime countValue
  if count == 0 then
    return {
      value := sourceValue
      heap := runtime.heap
      nextLocation := runtime.nextLocation
      world := runtime.world }
  consumingStringResult location cell
    (stringPushn source (Char.ofNat char.toNat) count) runtime

private def stringBinaryUInt8External (operation : String → String → UInt8)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalString request runtime left
  let right ← externalString request runtime right
  return {
    value := .scalar (.uint8 (operation left right))
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def stringDecEqExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringBinaryUInt8External
    (fun left right => if stringCompare left right == 1 then 1 else 0)
    request runtime

private def stringDecLtExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringBinaryUInt8External
    (fun left right => if stringCompare left right == 0 then 1 else 0)
    request runtime

private def stringCompareExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  stringBinaryUInt8External stringCompare request runtime

private def natBinaryRequest (name : Name) (left right : Value) : ExternalRequest := {
  name
  paramTypes := #[]
  resultType := default
  args := #[left, right] }

private def natBinaryGuard (name : Name) (operation : Nat → Nat → Nat)
    (left right expected : Nat) (allocates : Bool) : Bool :=
  let (runtime, leftValue) := literal {} (.nat left)
  let (runtime, rightValue) := literal runtime (.nat right)
  let request := natBinaryRequest name leftValue rightValue
  match natBinaryExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalNat request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.world == runtime.world &&
          response.nextLocation ==
            runtime.nextLocation + if allocates then 1 else 0

private def multiLimbNat : Nat :=
  340282366920938463463374607431768211473

private def natDecisionGuard (name : Name) (operation : Nat → Nat → Bool)
    (left right : Nat) (expected : Bool) : Bool :=
  let (runtime, leftValue) := literal {} (.nat left)
  let (runtime, rightValue) := literal runtime (.nat right)
  let request := natBinaryRequest name leftValue rightValue
  match natDecisionExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == .scalar (.uint8 (if expected then 1 else 0)) &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private def stringToNatGuard (name : Name) (operation : String → Nat)
    (input : String) (expected : Nat) : Bool :=
  let (runtime, reference) := alloc {} (.string input)
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[.object reference] }
  match stringToNatExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalNat request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.heap == runtime.heap &&
          response.nextLocation == runtime.nextLocation &&
          response.world == runtime.world

#guard natBinaryGuard ``Nat.add (· + ·) multiLimbNat multiLimbNat
  680564733841876926926749214863536422946 true

#guard natBinaryGuard ``Nat.sub (· - ·) multiLimbNat 17
  340282366920938463463374607431768211456 true

#guard natBinaryGuard ``Nat.sub (· - ·) multiLimbNat multiLimbNat 0 false

#guard natBinaryGuard ``Nat.sub (· - ·) 17 multiLimbNat 0 false

#guard natBinaryGuard ``Nat.mul (· * ·) 9223372036854775807 2
  18446744073709551614 true

#guard natBinaryGuard ``Nat.mul (· * ·) multiLimbNat 18446744073709551619
  6277101735386680764856636523970481806806073916012401524787 true

#guard natBinaryGuard ``Nat.mul (· * ·) multiLimbNat 0 0 false

#guard natBinaryGuard ``Nat.div (· / ·) multiLimbNat 18446744073709551619
  18446744073709551613 true

#guard natBinaryGuard ``Nat.div (· / ·) multiLimbNat 0 0 false

#guard natBinaryGuard ``Nat.mod (· % ·) multiLimbNat 18446744073709551619
  26 false

#guard natBinaryGuard ``Nat.mod (· % ·) multiLimbNat 0 multiLimbNat true

#guard natBinaryGuard ``Nat.land Nat.land multiLimbNat 18446744073709551619 1 false

#guard natBinaryGuard ``Nat.lor Nat.lor multiLimbNat 18446744073709551619
  340282366920938463481821351505477763091 true

#guard natBinaryGuard ``Nat.xor Nat.xor multiLimbNat 18446744073709551619
  340282366920938463481821351505477763090 true

#guard natBinaryGuard ``Nat.xor Nat.xor multiLimbNat multiLimbNat 0 false

#guard natBinaryGuard ``Nat.shiftLeft Nat.shiftLeft 9223372036854775807 1
  18446744073709551614 true

#guard natBinaryGuard ``Nat.shiftLeft Nat.shiftLeft multiLimbNat 65
  12554203470773361527671578846415332832831900187434193780736 true

#guard natBinaryGuard ``Nat.shiftRight Nat.shiftRight multiLimbNat 65
  9223372036854775808 true

#guard natBinaryGuard ``Nat.shiftRight Nat.shiftRight multiLimbNat 128 1 false

#guard natBinaryGuard ``Nat.shiftRight Nat.shiftRight multiLimbNat 129 0 false

#guard natBinaryGuard ``Nat.shiftRight Nat.shiftRight multiLimbNat multiLimbNat 0 false

#guard natDecisionGuard ``Nat.decEq
  (fun left right => decide (left = right)) multiLimbNat multiLimbNat true

#guard natDecisionGuard ``Nat.decEq
  (fun left right => decide (left = right)) 9223372036854775807 9223372036854775808 false

#guard natDecisionGuard ``Nat.decLt
  (fun left right => decide (left < right)) 9223372036854775807 9223372036854775808 true

#guard natDecisionGuard ``Nat.decLt
  (fun left right => decide (left < right)) multiLimbNat multiLimbNat false

#guard natDecisionGuard ``Nat.decLe
  (fun left right => decide (left ≤ right)) multiLimbNat multiLimbNat true

#guard natDecisionGuard ``Nat.decLe
  (fun left right => decide (left ≤ right)) 9223372036854775808 9223372036854775807 false

#guard stringToNatGuard ``String.Internal.length String.length "" 0

#guard stringToNatGuard ``String.Internal.length String.length "\u0000é😀" 3

#guard stringToNatGuard ``String.utf8ByteSize String.utf8ByteSize "" 0

#guard stringToNatGuard ``String.utf8ByteSize String.utf8ByteSize "\u0000é😀" 7

private def stringCharToNatGuard (name : Name) (operation : String → Char → Nat)
    (source : String) (needle : Char) (expected : Nat) : Bool :=
  let (runtime, reference) := alloc {} (.string source)
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[.object reference, .scalar (.uint32 needle.val)] }
  match stringCharToNatExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalNat request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.heap == runtime.heap &&
          response.nextLocation == runtime.nextLocation &&
          response.world == runtime.world

private def stringNatToNatGuard (name : Name) (operation : String → Nat → Nat)
    (source : String) (position expected : Nat) : Bool :=
  let (runtime, reference) := alloc {} (.string source)
  let (runtime, positionValue) := literal runtime (.nat position)
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[.object reference, positionValue] }
  match stringNatToNatExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalNat request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.heap == runtime.heap &&
          response.nextLocation == runtime.nextLocation &&
          response.world == runtime.world

#guard stringCharToNatGuard ``String.Internal.posOf stringPosOf "" 'x' 0

#guard stringCharToNatGuard ``String.Internal.posOf stringPosOf "Aé😀Z" '😀' 3

#guard stringCharToNatGuard ``String.Internal.posOf stringPosOf "Aé😀Z" '\u0000' 8

#guard stringNatToNatGuard ``String.Internal.offsetOfPos stringOffsetOfPos "Aé😀Z" 0 0

#guard stringNatToNatGuard ``String.Internal.offsetOfPos stringOffsetOfPos "Aé😀Z" 2 2

#guard stringNatToNatGuard ``String.Internal.offsetOfPos stringOffsetOfPos "Aé😀Z" 4 3

#guard stringNatToNatGuard ``String.Internal.offsetOfPos stringOffsetOfPos "Aé😀Z" 8 4

#guard stringNatToNatGuard ``String.Internal.offsetOfPos stringOffsetOfPos "Aé😀Z" 50 4

#guard stringNatToNatGuard ``String.Internal.next stringNext "" 0 1

#guard stringNatToNatGuard ``String.Internal.next stringNext "Aé😀Z" 1 3

#guard stringNatToNatGuard ``String.Internal.next stringNext "Aé😀Z" 2 3

#guard stringNatToNatGuard ``String.Internal.next stringNext "Aé😀Z" 3 7

#guard stringNatToNatGuard ``String.Internal.next stringNext "Aé😀Z" 8 9

#guard stringNatToNatGuard ``String.Internal.next stringNext "Aé😀Z" 50 51

private def stringExtractGuard (source : String) (beginPos endPos : Nat)
    (expected : String) : Bool :=
  let (runtime, sourceReference) := alloc {} (.string source)
  let (runtime, beginValue) := literal runtime (.nat beginPos)
  let (runtime, endValue) := literal runtime (.nat endPos)
  let request : ExternalRequest := {
    name := ``String.Internal.extract
    paramTypes := #[]
    resultType := default
    args := #[.object sourceReference, beginValue, endValue] }
  match stringExtractExternal request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalString request after response.value, sourceReference, response.value with
      | .ok actual, .heap sourceLocation, .object (.heap resultLocation) =>
          match getLiveCell runtime sourceLocation, getLiveCell after sourceLocation with
          | .ok beforeSource, .ok afterSource =>
              actual == expected &&
              beforeSource == afterSource &&
              resultLocation == runtime.nextLocation &&
              response.nextLocation == runtime.nextLocation + 1 &&
              response.world == runtime.world
          | _, _ => false
      | _, _, _ => false

#guard stringExtractGuard "Aé😀Z" 0 8 "Aé😀Z"

#guard stringExtractGuard "Aé😀Z" 1 7 "é😀"

#guard stringExtractGuard "Aé😀Z" 4 7 ""

#guard stringExtractGuard "Aé😀Z" 3 4 "😀Z"

#guard stringExtractGuard "Aé😀Z" 1 50 "é😀Z"

#guard stringExtractGuard "Aé😀Z" 7 3 ""

private def stringAppendRequest (left right : ObjectRef) : ExternalRequest := {
  name := ``String.Internal.append
  paramTypes := #[]
  resultType := default
  args := #[.object left, .object right] }

private def stringAppendUniqueGuard : Bool :=
  let (runtime, left) := alloc {} (.string "A")
  let (runtime, right) := alloc runtime (.string "é😀")
  match left, right with
  | .heap leftLocation, .heap rightLocation =>
      match getLiveCell runtime rightLocation,
          stringAppendExternal (stringAppendRequest left right) runtime with
      | .ok beforeRight, .ok response =>
          let after : RuntimeState := {
            runtime with
            heap := response.heap
            nextLocation := response.nextLocation
            world := response.world }
          match getLiveCell after leftLocation, getLiveCell after rightLocation with
          | .ok afterLeft, .ok afterRight =>
              response.value == .object left &&
              response.nextLocation == runtime.nextLocation &&
              response.world == runtime.world &&
              afterLeft.rc == 1 && !afterLeft.persistent &&
              afterLeft.object == .string "Aé😀" &&
              afterRight == beforeRight
          | _, _ => false
      | _, _ => false
  | _, _ => false

private def stringAppendSharedGuard : Bool :=
  let (runtime, left) := alloc {} (.string "A")
  let (runtime, right) := alloc runtime (.string "é😀")
  match left, right with
  | .heap leftLocation, .heap rightLocation =>
      match incLocation runtime leftLocation 1 with
      | .error _ => false
      | .ok runtime =>
          match getLiveCell runtime rightLocation,
              stringAppendExternal (stringAppendRequest left right) runtime with
          | .ok beforeRight, .ok response =>
              let after : RuntimeState := {
                runtime with
                heap := response.heap
                nextLocation := response.nextLocation
                world := response.world }
              match response.value with
              | .object (.heap resultLocation) =>
                  match getLiveCell after leftLocation, getLiveCell after rightLocation,
                      getLiveCell after resultLocation with
                  | .ok afterLeft, .ok afterRight, .ok result =>
                      resultLocation == runtime.nextLocation &&
                      response.nextLocation == runtime.nextLocation + 1 &&
                      response.world == runtime.world &&
                      afterLeft.rc == 1 && !afterLeft.persistent &&
                      afterLeft.object == .string "A" &&
                      afterRight == beforeRight &&
                      result.rc == 1 && !result.persistent &&
                      result.object == .string "Aé😀"
                  | _, _, _ => false
              | _ => false
          | _, _ => false
  | _, _ => false

private def stringAppendPersistentGuard : Bool :=
  let (runtime, left) := alloc {} (.string "A") (persistent := true)
  let (runtime, right) := alloc runtime (.string "é😀")
  match left, right with
  | .heap leftLocation, .heap rightLocation =>
      match getLiveCell runtime leftLocation, getLiveCell runtime rightLocation,
          stringAppendExternal (stringAppendRequest left right) runtime with
      | .ok beforeLeft, .ok beforeRight, .ok response =>
          let after : RuntimeState := {
            runtime with
            heap := response.heap
            nextLocation := response.nextLocation
            world := response.world }
          match response.value with
          | .object (.heap resultLocation) =>
              match getLiveCell after leftLocation, getLiveCell after rightLocation,
                  getLiveCell after resultLocation with
              | .ok afterLeft, .ok afterRight, .ok result =>
                  resultLocation == runtime.nextLocation &&
                  response.nextLocation == runtime.nextLocation + 1 &&
                  response.world == runtime.world &&
                  afterLeft == beforeLeft && afterRight == beforeRight &&
                  result.rc == 1 && !result.persistent &&
                  result.object == .string "Aé😀"
              | _, _, _ => false
          | _ => false
      | _, _, _ => false
  | _, _ => false

private def stringPushnRequest (source : ObjectRef) (count : Nat) : ExternalRequest := {
  name := ``String.Internal.pushn
  paramTypes := #[]
  resultType := default
  args := #[
    .object source,
    .scalar (.uint32 0x1f600),
    .object (.tagged (UInt64.ofNat count))] }

private def stringPushnZeroSharedGuard : Bool :=
  let (runtime, source) := alloc {} (.string "A")
  match source with
  | .heap sourceLocation =>
      match incLocation runtime sourceLocation 1 with
      | .error _ => false
      | .ok runtime =>
          match getLiveCell runtime sourceLocation,
              stringPushnExternal (stringPushnRequest source 0) runtime with
          | .ok beforeSource, .ok response =>
              let after : RuntimeState := {
                runtime with
                heap := response.heap
                nextLocation := response.nextLocation
                world := response.world }
              match getLiveCell after sourceLocation with
              | .ok afterSource =>
                  response.value == .object source &&
                  response.nextLocation == runtime.nextLocation &&
                  response.world == runtime.world &&
                  afterSource == beforeSource && afterSource.rc == 2
              | _ => false
          | _, _ => false
  | _ => false

private def stringPushnUniqueGuard : Bool :=
  let (runtime, source) := alloc {} (.string "A")
  match source with
  | .heap sourceLocation =>
      match stringPushnExternal (stringPushnRequest source 2) runtime with
      | .error _ => false
      | .ok response =>
          let after : RuntimeState := {
            runtime with
            heap := response.heap
            nextLocation := response.nextLocation
            world := response.world }
          match getLiveCell after sourceLocation with
          | .ok afterSource =>
              response.value == .object source &&
              response.nextLocation == runtime.nextLocation &&
              response.world == runtime.world &&
              afterSource.rc == 1 && !afterSource.persistent &&
              afterSource.object == .string "A😀😀"
          | _ => false
  | _ => false

private def stringPushnSharedGuard : Bool :=
  let (runtime, source) := alloc {} (.string "A")
  match source with
  | .heap sourceLocation =>
      match incLocation runtime sourceLocation 1 with
      | .error _ => false
      | .ok runtime =>
          match stringPushnExternal (stringPushnRequest source 2) runtime with
          | .error _ => false
          | .ok response =>
              let after : RuntimeState := {
                runtime with
                heap := response.heap
                nextLocation := response.nextLocation
                world := response.world }
              match response.value with
              | .object (.heap resultLocation) =>
                  match getLiveCell after sourceLocation, getLiveCell after resultLocation with
                  | .ok afterSource, .ok result =>
                      resultLocation == runtime.nextLocation &&
                      response.nextLocation == runtime.nextLocation + 1 &&
                      response.world == runtime.world &&
                      afterSource.rc == 1 && !afterSource.persistent &&
                      afterSource.object == .string "A" &&
                      result.rc == 1 && !result.persistent &&
                      result.object == .string "A😀😀"
                  | _, _ => false
              | _ => false
  | _ => false

#guard stringAppendUniqueGuard
#guard stringAppendSharedGuard
#guard stringAppendPersistentGuard
#guard stringPushnZeroSharedGuard
#guard stringPushnUniqueGuard
#guard stringPushnSharedGuard

private def stringBinaryUInt8Guard (name : Name)
    (external : ExternalRequest → RuntimeState → Except RuntimeFault ExternalResponse)
    (left right : String) (expected : UInt8) : Bool :=
  let (runtime, leftReference) := alloc {} (.string left)
  let (runtime, rightReference) := alloc runtime (.string right)
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[.object leftReference, .object rightReference] }
  match external request runtime with
  | .error _ => false
  | .ok response =>
      response.value == .scalar (.uint8 expected) &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

#guard stringBinaryUInt8Guard ``String.decEq stringDecEqExternal
  "A\u0000é😀" "A\u0000é😀" 1

#guard stringBinaryUInt8Guard ``String.decEq stringDecEqExternal
  "A\u0000é😀" "A\u0000é😁" 0

#guard stringBinaryUInt8Guard ``String.decEq stringDecEqExternal "A" "A\u0000" 0

#guard stringBinaryUInt8Guard ``String.decidableLT stringDecLtExternal
  bmpPrivateUseString supplementaryPlaneString 1

#guard stringBinaryUInt8Guard ``String.decidableLT stringDecLtExternal
  supplementaryPlaneString bmpPrivateUseString 0

#guard stringBinaryUInt8Guard ``String.decidableLT stringDecLtExternal "A" "A\u0000" 1

#guard stringBinaryUInt8Guard ``String.compare stringCompareExternal
  "A\u0000é😀" "A\u0000é😀" 1

#guard stringBinaryUInt8Guard ``String.compare stringCompareExternal
  bmpPrivateUseString supplementaryPlaneString 0

#guard stringBinaryUInt8Guard ``String.compare stringCompareExternal
  supplementaryPlaneString bmpPrivateUseString 2

#guard stringBinaryUInt8Guard ``String.compare stringCompareExternal "A" "A\u0000" 0

private def recordEffectExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalNat request runtime value
  let (runtime, result) := literal runtime (.nat (value + 1))
  return {
    value := result
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world + 1 }

private def byteArraySizeExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalByteArray request runtime value
  let (runtime, value) := literal runtime (.nat value.size)
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def byteArrayGetExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value, index] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let value ← externalByteArray request runtime value
  let index ← externalNat request runtime index
  let value := value[index]?.getD 0
  return {
    value := .scalar (.uint8 value)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def byteArraySetExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [array, index, byte] := request.args.toList
    | throw (.arityMismatch 3 request.args.size)
  let (location, cell, bytes) ← externalByteArrayCell request runtime array
  let index ← externalNat request runtime index
  let byte ← externalUInt8 request byte
  if index >= bytes.size then
    return {
      value := array
      heap := runtime.heap
      nextLocation := runtime.nextLocation
      world := runtime.world }
  let bytes := bytes.set! index byte
  if !cell.persistent && cell.rc == 1 then
    let runtime ← setCell runtime location { cell with object := .byteArray bytes }
    return {
      value := array
      heap := runtime.heap
      nextLocation := runtime.nextLocation
      world := runtime.world }
  let runtime ← if cell.persistent then pure runtime else decLocation runtime location
  let (runtime, reference) := alloc runtime (.byteArray bytes)
  return {
    value := .object reference
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def byteArraySetRequest (array : Value) (index : Nat) (byte : UInt8) :
    ExternalRequest := {
  name := ``ByteArray.set!
  paramTypes := #[]
  resultType := default
  args := #[array, .object (.tagged (UInt64.ofNat index)), .scalar (.uint8 byte)] }

private def recordByteArrayExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [array, byte] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let byte ← externalUInt8 request byte
  let response ← byteArraySetExternal (byteArraySetRequest array 0 byte) runtime
  return { response with world := response.world + 1 }

private def byteArraySetUniqueGuard : Bool :=
  let original : Array UInt8 := #[0, 127, 128, 255]
  let expected : Array UInt8 := #[255, 127, 128, 255]
  let (runtime, reference) := alloc {} (.byteArray original)
  match reference with
  | .tagged _ => false
  | .heap location =>
      match byteArraySetExternal (byteArraySetRequest (.object reference) 0 255) runtime with
      | .error _ => false
      | .ok response =>
          let after : RuntimeState := {
            runtime with
            heap := response.heap
            nextLocation := response.nextLocation
            world := response.world }
          match getLiveCell after location with
          | .error _ => false
          | .ok cell =>
              response.value == .object reference &&
              response.nextLocation == runtime.nextLocation &&
              cell.rc == 1 && cell.object == .byteArray expected

private def byteArraySetSharedGuard : Bool :=
  let original : Array UInt8 := #[0, 127, 128, 255]
  let expected : Array UInt8 := #[0, 127, 255, 255]
  let (runtime, reference) := alloc {} (.byteArray original)
  match reference with
  | .tagged _ => false
  | .heap oldLocation =>
      match incLocation runtime oldLocation 1 with
      | .error _ => false
      | .ok runtime =>
          match byteArraySetExternal (byteArraySetRequest (.object reference) 2 255) runtime with
          | .error _ => false
          | .ok response =>
              match response.value with
              | .object (.heap newLocation) =>
                  let after : RuntimeState := {
                    runtime with
                    heap := response.heap
                    nextLocation := response.nextLocation
                    world := response.world }
                  match getLiveCell after oldLocation, getLiveCell after newLocation with
                  | .ok oldCell, .ok newCell =>
                      oldLocation != newLocation &&
                      newLocation == runtime.nextLocation &&
                      response.nextLocation == runtime.nextLocation + 1 &&
                      oldCell.rc == 1 && oldCell.object == .byteArray original &&
                      newCell.rc == 1 && newCell.object == .byteArray expected
                  | _, _ => false
              | _ => false

#guard byteArraySetUniqueGuard
#guard byteArraySetSharedGuard

private def intOfNatExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalNat request runtime value
  let (runtime, value) := encodeIntValue runtime (.ofNat value)
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intNegExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalInt request runtime value
  let (runtime, value) := encodeIntValue runtime (-value)
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intToNatExternal (operation : Int → Nat)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalInt request runtime value
  let (runtime, value) := literal runtime (.nat (operation value))
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intNatAbsExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intToNatExternal Int.natAbs request runtime

private def intToNatRequest (name : Name) (value : Value) : ExternalRequest := {
  name
  paramTypes := #[]
  resultType := default
  args := #[value] }

private def intToNatGuard (name : Name) (operation : Int → Nat)
    (input : Int) (expected : Nat) (allocates : Bool) : Bool :=
  let (runtime, inputValue) := encodeIntValue {} input
  let request := intToNatRequest name inputValue
  match intToNatExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalNat request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.world == runtime.world &&
          response.nextLocation ==
            runtime.nextLocation + if allocates then 1 else 0

private def intNatAbsGuard : Int → Nat → Bool → Bool :=
  intToNatGuard ``Int.natAbs Int.natAbs

private def intBinaryExternal (operation : Int → Int → Int)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalInt request runtime left
  let right ← externalInt request runtime right
  let (runtime, value) := encodeIntValue runtime (operation left right)
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intAddExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intBinaryExternal (· + ·) request runtime

private def intSubExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intBinaryExternal (· - ·) request runtime

private def intMulExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intBinaryExternal (· * ·) request runtime

private def intEDivExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intBinaryExternal (· / ·) request runtime

private def intEModExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intBinaryExternal (· % ·) request runtime

private def intNatBinaryExternal (operation : Int → Nat → Int)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value, count] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let value ← externalInt request runtime value
  let count ← externalNat request runtime count
  let (runtime, value) := encodeIntValue runtime (operation value count)
  return {
    value
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intShiftLeftExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intNatBinaryExternal Int.shiftLeft request runtime

private def intShiftRightExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intNatBinaryExternal Int.shiftRight request runtime

private def intBinaryRequest (name : Name) (left right : Value) : ExternalRequest := {
  name
  paramTypes := #[]
  resultType := default
  args := #[left, right] }

private def intBinaryGuard (name : Name) (operation : Int → Int → Int)
    (left right expected : Int) (allocates : Bool) : Bool :=
  let (runtime, leftValue) := encodeIntValue {} left
  let (runtime, rightValue) := encodeIntValue runtime right
  let request := intBinaryRequest name leftValue rightValue
  match intBinaryExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalInt request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.world == runtime.world &&
          response.nextLocation ==
            runtime.nextLocation + if allocates then 1 else 0

private def intNatBinaryGuard (name : Name) (operation : Int → Nat → Int)
    (input expected : Int) (count : Nat) (allocates : Bool) : Bool :=
  let (runtime, inputValue) := encodeIntValue {} input
  let (runtime, countValue) := literal runtime (.nat count)
  let request := intBinaryRequest name inputValue countValue
  match intNatBinaryExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      let after : RuntimeState := {
        runtime with
        heap := response.heap
        nextLocation := response.nextLocation
        world := response.world }
      match externalInt request after response.value with
      | .error _ => false
      | .ok actual =>
          actual == expected &&
          response.world == runtime.world &&
          response.nextLocation ==
            runtime.nextLocation + if allocates then 1 else 0

private def intAddGuard : Int → Int → Int → Bool → Bool :=
  intBinaryGuard ``Int.add (· + ·)

private def intSubGuard : Int → Int → Int → Bool → Bool :=
  intBinaryGuard ``Int.sub (· - ·)

private def multiLimbInt : Int :=
  340282366920938463463374607431768211473

#guard intAddGuard multiLimbInt multiLimbInt
  (680564733841876926926749214863536422946 : Int) true

#guard intAddGuard multiLimbInt (-multiLimbInt) 0 false

#guard intSubGuard multiLimbInt (-multiLimbInt)
  (680564733841876926926749214863536422946 : Int) true

#guard intSubGuard multiLimbInt multiLimbInt 0 false

#guard intBinaryGuard ``Int.mul (· * ·) 2147483647 2 4294967294 true

#guard intBinaryGuard ``Int.mul (· * ·) (-2147483648) (-1) 2147483648 true

#guard intBinaryGuard ``Int.mul (· * ·) multiLimbInt (-17)
  (-5784800237655953878877368326340059595041) true

#guard intBinaryGuard ``Int.mul (· * ·) multiLimbInt 0 0 false

#guard intBinaryGuard ``Int.ediv (· / ·) (-multiLimbInt) 17
  (-20016609818878733144904388672456953617) true

#guard intBinaryGuard ``Int.ediv (· / ·) (-12) (-7) 2 false

#guard intBinaryGuard ``Int.ediv (· / ·) multiLimbInt 0 0 false

#guard intBinaryGuard ``Int.emod (· % ·) (-multiLimbInt) 17 16 false

#guard intBinaryGuard ``Int.emod (· % ·) (-12) (-7) 2 false

#guard intBinaryGuard ``Int.emod (· % ·) (-multiLimbInt) 0
  (-multiLimbInt) true

#guard intNatBinaryGuard ``Int.shiftLeft Int.shiftLeft 2147483647 4294967294 1 true

#guard intNatBinaryGuard ``Int.shiftLeft Int.shiftLeft (-2147483648) (-4294967296) 1 true

#guard intNatBinaryGuard ``Int.shiftLeft Int.shiftLeft multiLimbInt
  12554203470773361527671578846415332832831900187434193780736 65 true

#guard intNatBinaryGuard ``Int.shiftLeft Int.shiftLeft (-multiLimbInt)
  (-12554203470773361527671578846415332832831900187434193780736) 65 true

#guard intNatBinaryGuard ``Int.shiftRight Int.shiftRight multiLimbInt
  9223372036854775808 65 true

#guard intNatBinaryGuard ``Int.shiftRight Int.shiftRight (-multiLimbInt)
  (-9223372036854775809) 65 true

#guard intNatBinaryGuard ``Int.shiftRight Int.shiftRight multiLimbInt 1 128 false

#guard intNatBinaryGuard ``Int.shiftRight Int.shiftRight (-multiLimbInt) (-1) 129 false

#guard intNatBinaryGuard ``Int.shiftRight Int.shiftRight (-multiLimbInt) (-1)
  multiLimbNat false

#guard intNatAbsGuard multiLimbInt multiLimbNat true

#guard intNatAbsGuard (-multiLimbInt) multiLimbNat true

#guard intNatAbsGuard (-2147483648) 2147483648 false

#guard intNatAbsGuard (-2147483649) 2147483649 false

private def intDecisionExternal (operation : Int → Int → Bool)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalInt request runtime left
  let right ← externalInt request runtime right
  return {
    value := .scalar (.uint8 (if operation left right then 1 else 0))
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intDecEqExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intDecisionExternal (fun left right => decide (left = right)) request runtime

private def intDecLtExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intDecisionExternal (fun left right => decide (left < right)) request runtime

private def intDecLeExternal (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse :=
  intDecisionExternal (fun left right => decide (left ≤ right)) request runtime

private def intDecisionGuard (name : Name) (operation : Int → Int → Bool)
    (left right : Int) (expected : Bool) : Bool :=
  let (runtime, leftValue) := encodeIntValue {} left
  let (runtime, rightValue) := encodeIntValue runtime right
  let request := intBinaryRequest name leftValue rightValue
  match intDecisionExternal operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == .scalar (.uint8 (if expected then 1 else 0)) &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

#guard intDecisionGuard ``Int.decEq
  (fun left right => decide (left = right)) multiLimbInt multiLimbInt true

#guard intDecisionGuard ``Int.decEq
  (fun left right => decide (left = right)) (-multiLimbInt) multiLimbInt false

#guard intDecisionGuard ``Int.decLt
  (fun left right => decide (left < right)) (-multiLimbInt) multiLimbInt true

#guard intDecisionGuard ``Int.decLt
  (fun left right => decide (left < right)) multiLimbInt multiLimbInt false

#guard intDecisionGuard ``Int.decLe
  (fun left right => decide (left ≤ right)) (-multiLimbInt) (-multiLimbInt) true

#guard intDecisionGuard ``Int.decLe
  (fun left right => decide (left ≤ right)) multiLimbInt (-multiLimbInt) false

private def fixedWidthBinaryExternal (codec : FixedWidthValueCodec α)
    (operation : α → α → α) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalFixedWidthValue codec request left
  let right ← externalFixedWidthValue codec request right
  return {
    value := codec.encode (operation left right)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def fixedWidthUnaryExternal (codec : FixedWidthValueCodec α)
    (operation : α → α) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalFixedWidthValue codec request value
  return {
    value := codec.encode (operation value)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def fixedWidthDecisionExternal (codec : FixedWidthValueCodec α)
    (operation : α → α → Bool) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [left, right] := request.args.toList
    | throw (.arityMismatch 2 request.args.size)
  let left ← externalFixedWidthValue codec request left
  let right ← externalFixedWidthValue codec request right
  return {
    value := .scalar (.uint8 (if operation left right then 1 else 0))
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def natToFixedWidthExternal (codec : FixedWidthValueCodec α)
    (operation : Nat → α) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalNat request runtime value
  return {
    value := codec.encode (operation value)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def intToFixedWidthExternal (codec : FixedWidthValueCodec α)
    (operation : Int → α) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalInt request runtime value
  return {
    value := codec.encode (operation value)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def fixedWidthToNatExternal (codec : FixedWidthValueCodec α)
    (operation : α → Nat) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalFixedWidthValue codec request value
  let (runtime, result) := literal runtime (.nat (operation value))
  return {
    value := result
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def fixedWidthToIntExternal (codec : FixedWidthValueCodec α)
    (operation : α → Int) (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalFixedWidthValue codec request value
  let (runtime, result) := encodeIntValue runtime (operation value)
  return {
    value := result
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def fixedWidthConversionExternal (sourceCodec : FixedWidthValueCodec α)
    (targetCodec : FixedWidthValueCodec β) (operation : α → β)
    (request : ExternalRequest) (runtime : RuntimeState) :
    Except RuntimeFault ExternalResponse := do
  let [value] := request.args.toList
    | throw (.arityMismatch 1 request.args.size)
  let value ← externalFixedWidthValue sourceCodec request value
  return {
    value := targetCodec.encode (operation value)
    heap := runtime.heap
    nextLocation := runtime.nextLocation
    world := runtime.world }

private def fixedWidthBinaryGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : α → α → α) (left right expected : α) : Bool :=
  let runtime : RuntimeState := {}
  let request := intBinaryRequest name
    (codec.encode left) (codec.encode right)
  match fixedWidthBinaryExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == codec.encode expected &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private def fixedWidthUnaryGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : α → α) (input expected : α) : Bool :=
  let runtime : RuntimeState := {}
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[codec.encode input] }
  match fixedWidthUnaryExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == codec.encode expected &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private def fixedWidthDecisionGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : α → α → Bool) (left right : α) (expected : Bool) : Bool :=
  let runtime : RuntimeState := {}
  let request := intBinaryRequest name
    (codec.encode left) (codec.encode right)
  match fixedWidthDecisionExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == .scalar (.uint8 (if expected then 1 else 0)) &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private def natToFixedWidthGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : Nat → α) (input : Nat) (expected : α) : Bool :=
  let (runtime, inputValue) := literal {} (.nat input)
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[inputValue] }
  match natToFixedWidthExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == codec.encode expected &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private def intToFixedWidthGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : Int → α) (input : Int) (expected : α) : Bool :=
  let (runtime, inputValue) := encodeIntValue {} input
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[inputValue] }
  match intToFixedWidthExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == codec.encode expected &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private def fixedWidthToNatGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : α → Nat) (input : α) (expected : Nat) : Bool :=
  let runtime : RuntimeState := {}
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[codec.encode input] }
  let (expectedRuntime, expectedValue) := literal runtime (.nat expected)
  match fixedWidthToNatExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == expectedValue &&
      response.heap == expectedRuntime.heap &&
      response.nextLocation == expectedRuntime.nextLocation &&
      response.world == expectedRuntime.world

private def fixedWidthToIntGuard (codec : FixedWidthValueCodec α) (name : Name)
    (operation : α → Int) (input : α) (expected : Int) : Bool :=
  let runtime : RuntimeState := {}
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[codec.encode input] }
  let (expectedRuntime, expectedValue) := encodeIntValue runtime expected
  match fixedWidthToIntExternal codec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == expectedValue &&
      response.heap == expectedRuntime.heap &&
      response.nextLocation == expectedRuntime.nextLocation &&
      response.world == expectedRuntime.world

private def fixedWidthConversionGuard (sourceCodec : FixedWidthValueCodec α)
    (targetCodec : FixedWidthValueCodec β) (name : Name)
    (operation : α → β) (input : α) (expected : β) : Bool :=
  let runtime : RuntimeState := {}
  let request : ExternalRequest := {
    name
    paramTypes := #[]
    resultType := default
    args := #[sourceCodec.encode input] }
  match fixedWidthConversionExternal sourceCodec targetCodec operation request runtime with
  | .error _ => false
  | .ok response =>
      response.value == targetCodec.encode expected &&
      response.heap == runtime.heap &&
      response.nextLocation == runtime.nextLocation &&
      response.world == runtime.world

private structure SignedFixedWidthContract (α : Type) where
  typeName : Name
  width : Nat
  codec : FixedWidthValueCodec α
  ofNat : Nat → α
  ofInt : Int → α
  toInt : α → Int
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  modulo : α → α → α
  land : α → α → α
  lor : α → α → α
  xor : α → α → α
  shiftLeft : α → α → α
  shiftRight : α → α → α
  complement : α → α
  neg : α → α
  abs : α → α
  decEq : α → α → Bool
  decLt : α → α → Bool
  decLe : α → α → Bool

private def signedFixedWidthContractGuard
    (contract : SignedFixedWidthContract α) : Bool :=
  let magnitude : Nat := 2 ^ (contract.width - 1)
  let minimum : Int := -(Int.ofNat magnitude)
  let maximum : Int := Int.ofNat (magnitude - 1)
  let value := contract.ofInt
  let name := contract.typeName
  fixedWidthBinaryGuard contract.codec name contract.add
      (value maximum) (value 1) (value minimum) &&
    fixedWidthBinaryGuard contract.codec name contract.sub
      (value minimum) (value 1) (value maximum) &&
    fixedWidthBinaryGuard contract.codec name contract.mul
      (value (Int.ofNat (2 ^ (contract.width - 2)))) (value 2) (value minimum) &&
    fixedWidthBinaryGuard contract.codec name contract.div
      (value (-7)) (value 3) (value (-2)) &&
    fixedWidthBinaryGuard contract.codec name contract.div
      (value minimum) (value (-1)) (value minimum) &&
    fixedWidthBinaryGuard contract.codec name contract.div
      (value (-7)) (value 0) (value 0) &&
    fixedWidthBinaryGuard contract.codec name contract.modulo
      (value (-7)) (value 3) (value (-1)) &&
    fixedWidthBinaryGuard contract.codec name contract.modulo
      (value 7) (value (-3)) (value 1) &&
    fixedWidthBinaryGuard contract.codec name contract.modulo
      (value (-7)) (value 0) (value (-7)) &&
    fixedWidthBinaryGuard contract.codec name contract.land
      (value (-16)) (value 60) (value 48) &&
    fixedWidthBinaryGuard contract.codec name contract.lor
      (value (-64)) (value 60) (value (-4)) &&
    fixedWidthBinaryGuard contract.codec name contract.xor
      (value (-16)) (value 60) (value (-52)) &&
    fixedWidthBinaryGuard contract.codec name contract.shiftLeft
      (value (minimum + 1)) (value (-(Int.ofNat contract.width))) (value (minimum + 1)) &&
    fixedWidthBinaryGuard contract.codec name contract.shiftLeft
      (value (minimum + 1)) (value (-1)) (value minimum) &&
    fixedWidthBinaryGuard contract.codec name contract.shiftLeft
      (value (minimum + 1)) (value (Int.ofNat contract.width + 1)) (value 2) &&
    fixedWidthBinaryGuard contract.codec name contract.shiftRight
      (value (minimum + 1)) (value (-(Int.ofNat contract.width))) (value (minimum + 1)) &&
    fixedWidthBinaryGuard contract.codec name contract.shiftRight
      (value (minimum + 1)) (value (-1)) (value (-1)) &&
    fixedWidthBinaryGuard contract.codec name contract.shiftRight
      (value (minimum + 1)) (value (Int.ofNat contract.width + 1)) (value (minimum / 2)) &&
    fixedWidthUnaryGuard contract.codec name contract.complement
      (value 0) (value (-1)) &&
    fixedWidthUnaryGuard contract.codec name contract.neg
      (value minimum) (value minimum) &&
    fixedWidthUnaryGuard contract.codec name contract.abs
      (value (-7)) (value 7) &&
    fixedWidthUnaryGuard contract.codec name contract.abs
      (value minimum) (value minimum) &&
    fixedWidthDecisionGuard contract.codec name contract.decEq
      (value (-1)) (value (-1)) true &&
    fixedWidthDecisionGuard contract.codec name contract.decEq
      (value (-1)) (value 1) false &&
    fixedWidthDecisionGuard contract.codec name contract.decLt
      (value (-1)) (value 0) true &&
    fixedWidthDecisionGuard contract.codec name contract.decLt
      (value maximum) (value minimum) false &&
    fixedWidthDecisionGuard contract.codec name contract.decLe
      (value minimum) (value minimum) true &&
    fixedWidthDecisionGuard contract.codec name contract.decLe
      (value 0) (value (-1)) false &&
    natToFixedWidthGuard contract.codec name contract.ofNat
      (2 ^ contract.width - 1) (value (-1)) &&
    natToFixedWidthGuard contract.codec name contract.ofNat
      (2 ^ contract.width) (value 0) &&
    natToFixedWidthGuard contract.codec name contract.ofNat
      multiLimbNat (value 17) &&
    intToFixedWidthGuard contract.codec name contract.ofInt
      (maximum + 1) (value minimum) &&
    intToFixedWidthGuard contract.codec name contract.ofInt
      (minimum - 1) (value maximum) &&
    intToFixedWidthGuard contract.codec name contract.ofInt
      multiLimbInt (value 17) &&
    intToFixedWidthGuard contract.codec name contract.ofInt
      (-multiLimbInt) (value (-17)) &&
    fixedWidthToIntGuard contract.codec name contract.toInt
      (value minimum) minimum &&
    fixedWidthToIntGuard contract.codec name contract.toInt
      (value maximum) maximum

private def int8Contract : SignedFixedWidthContract Int8 where
  typeName := ``Int8
  width := 8
  codec := int8Codec
  ofNat := Int8.ofNat
  ofInt := Int8.ofInt
  toInt := Int8.toInt
  add := Int8.add
  sub := Int8.sub
  mul := Int8.mul
  div := Int8.div
  modulo := Int8.mod
  land := Int8.land
  lor := Int8.lor
  xor := Int8.xor
  shiftLeft := Int8.shiftLeft
  shiftRight := Int8.shiftRight
  complement := Int8.complement
  neg := Int8.neg
  abs := Int8.abs
  decEq := fun left right => decide (left = right)
  decLt := fun left right => decide (left < right)
  decLe := fun left right => decide (left ≤ right)

private def int16Contract : SignedFixedWidthContract Int16 where
  typeName := ``Int16
  width := 16
  codec := int16Codec
  ofNat := Int16.ofNat
  ofInt := Int16.ofInt
  toInt := Int16.toInt
  add := Int16.add
  sub := Int16.sub
  mul := Int16.mul
  div := Int16.div
  modulo := Int16.mod
  land := Int16.land
  lor := Int16.lor
  xor := Int16.xor
  shiftLeft := Int16.shiftLeft
  shiftRight := Int16.shiftRight
  complement := Int16.complement
  neg := Int16.neg
  abs := Int16.abs
  decEq := fun left right => decide (left = right)
  decLt := fun left right => decide (left < right)
  decLe := fun left right => decide (left ≤ right)

private def int32Contract : SignedFixedWidthContract Int32 where
  typeName := ``Int32
  width := 32
  codec := int32Codec
  ofNat := Int32.ofNat
  ofInt := Int32.ofInt
  toInt := Int32.toInt
  add := Int32.add
  sub := Int32.sub
  mul := Int32.mul
  div := Int32.div
  modulo := Int32.mod
  land := Int32.land
  lor := Int32.lor
  xor := Int32.xor
  shiftLeft := Int32.shiftLeft
  shiftRight := Int32.shiftRight
  complement := Int32.complement
  neg := Int32.neg
  abs := Int32.abs
  decEq := fun left right => decide (left = right)
  decLt := fun left right => decide (left < right)
  decLe := fun left right => decide (left ≤ right)

private def int64Contract : SignedFixedWidthContract Int64 where
  typeName := ``Int64
  width := 64
  codec := int64Codec
  ofNat := Int64.ofNat
  ofInt := Int64.ofInt
  toInt := Int64.toInt
  add := Int64.add
  sub := Int64.sub
  mul := Int64.mul
  div := Int64.div
  modulo := Int64.mod
  land := Int64.land
  lor := Int64.lor
  xor := Int64.xor
  shiftLeft := Int64.shiftLeft
  shiftRight := Int64.shiftRight
  complement := Int64.complement
  neg := Int64.neg
  abs := Int64.abs
  decEq := fun left right => decide (left = right)
  decLt := fun left right => decide (left < right)
  decLe := fun left right => decide (left ≤ right)

private def isizeContract : SignedFixedWidthContract ISize where
  typeName := ``ISize
  width := System.Platform.numBits
  codec := isizeCodec
  ofNat := ISize.ofNat
  ofInt := ISize.ofInt
  toInt := ISize.toInt
  add := ISize.add
  sub := ISize.sub
  mul := ISize.mul
  div := ISize.div
  modulo := ISize.mod
  land := ISize.land
  lor := ISize.lor
  xor := ISize.xor
  shiftLeft := ISize.shiftLeft
  shiftRight := ISize.shiftRight
  complement := ISize.complement
  neg := ISize.neg
  abs := ISize.abs
  decEq := fun left right => decide (left = right)
  decLt := fun left right => decide (left < right)
  decLe := fun left right => decide (left ≤ right)

#guard signedFixedWidthContractGuard int8Contract
#guard signedFixedWidthContractGuard int16Contract
#guard signedFixedWidthContractGuard int32Contract
#guard signedFixedWidthContractGuard int64Contract
#guard signedFixedWidthContractGuard isizeContract

private def int8 (value : Int) : Int8 :=
  Int8.ofInt value

#guard int8Codec.decode? (.scalar (.uint16 1)) |>.isNone

#guard fixedWidthBinaryGuard int8Codec ``Int8.add Int8.add
  (int8 127) (int8 1) (int8 (-128))

#guard fixedWidthBinaryGuard int8Codec ``Int8.sub Int8.sub
  (int8 (-128)) (int8 1) (int8 127)

#guard fixedWidthBinaryGuard int8Codec ``Int8.mul Int8.mul
  (int8 64) (int8 2) (int8 (-128))

#guard fixedWidthBinaryGuard int8Codec ``Int8.div Int8.div
  (int8 (-7)) (int8 3) (int8 (-2))

#guard fixedWidthBinaryGuard int8Codec ``Int8.div Int8.div
  (int8 (-128)) (int8 (-1)) (int8 (-128))

#guard fixedWidthBinaryGuard int8Codec ``Int8.div Int8.div
  (int8 (-7)) (int8 0) (int8 0)

#guard fixedWidthBinaryGuard int8Codec ``Int8.mod Int8.mod
  (int8 (-7)) (int8 3) (int8 (-1))

#guard fixedWidthBinaryGuard int8Codec ``Int8.mod Int8.mod
  (int8 7) (int8 (-3)) (int8 1)

#guard fixedWidthBinaryGuard int8Codec ``Int8.mod Int8.mod
  (int8 (-7)) (int8 0) (int8 (-7))

#guard fixedWidthBinaryGuard int8Codec ``Int8.land Int8.land
  (int8 (-16)) (int8 60) (int8 48)

#guard fixedWidthBinaryGuard int8Codec ``Int8.lor Int8.lor
  (int8 (-64)) (int8 60) (int8 (-4))

#guard fixedWidthBinaryGuard int8Codec ``Int8.xor Int8.xor
  (int8 (-16)) (int8 60) (int8 (-52))

#guard fixedWidthBinaryGuard int8Codec ``Int8.shiftLeft Int8.shiftLeft
  (int8 (-127)) (int8 (-8)) (int8 (-127))

#guard fixedWidthBinaryGuard int8Codec ``Int8.shiftLeft Int8.shiftLeft
  (int8 (-127)) (int8 (-1)) (int8 (-128))

#guard fixedWidthBinaryGuard int8Codec ``Int8.shiftLeft Int8.shiftLeft
  (int8 (-127)) (int8 9) (int8 2)

#guard fixedWidthBinaryGuard int8Codec ``Int8.shiftRight Int8.shiftRight
  (int8 (-127)) (int8 (-8)) (int8 (-127))

#guard fixedWidthBinaryGuard int8Codec ``Int8.shiftRight Int8.shiftRight
  (int8 (-127)) (int8 (-1)) (int8 (-1))

#guard fixedWidthBinaryGuard int8Codec ``Int8.shiftRight Int8.shiftRight
  (int8 (-127)) (int8 9) (int8 (-64))

#guard fixedWidthUnaryGuard int8Codec ``Int8.complement Int8.complement
  (int8 0) (int8 (-1))

#guard fixedWidthUnaryGuard int8Codec ``Int8.neg Int8.neg
  (int8 (-128)) (int8 (-128))

#guard fixedWidthUnaryGuard int8Codec ``Int8.abs Int8.abs
  (int8 (-7)) (int8 7)

#guard fixedWidthUnaryGuard int8Codec ``Int8.abs Int8.abs
  (int8 (-128)) (int8 (-128))

#guard fixedWidthDecisionGuard int8Codec ``Int8.decEq
  (fun left right => decide (left = right))
  (int8 (-1)) (int8 (-1)) true

#guard fixedWidthDecisionGuard int8Codec ``Int8.decEq
  (fun left right => decide (left = right))
  (int8 (-1)) (int8 1) false

#guard fixedWidthDecisionGuard int8Codec ``Int8.decLt
  (fun left right => decide (left < right))
  (int8 (-1)) (int8 0) true

#guard fixedWidthDecisionGuard int8Codec ``Int8.decLt
  (fun left right => decide (left < right))
  (int8 127) (int8 (-128)) false

#guard fixedWidthDecisionGuard int8Codec ``Int8.decLe
  (fun left right => decide (left ≤ right))
  (int8 (-128)) (int8 (-128)) true

#guard fixedWidthDecisionGuard int8Codec ``Int8.decLe
  (fun left right => decide (left ≤ right))
  (int8 0) (int8 (-1)) false

#guard natToFixedWidthGuard int8Codec ``Int8.ofNat
  Int8.ofNat 255 (int8 (-1))

#guard natToFixedWidthGuard int8Codec ``Int8.ofNat
  Int8.ofNat 256 (int8 0)

#guard natToFixedWidthGuard int8Codec ``Int8.ofNat
  Int8.ofNat multiLimbNat (int8 17)

#guard intToFixedWidthGuard int8Codec ``Int8.ofInt
  Int8.ofInt 128 (int8 (-128))

#guard intToFixedWidthGuard int8Codec ``Int8.ofInt
  Int8.ofInt (-129) (int8 127)

#guard intToFixedWidthGuard int8Codec ``Int8.ofInt
  Int8.ofInt multiLimbInt (int8 17)

#guard intToFixedWidthGuard int8Codec ``Int8.ofInt
  Int8.ofInt (-multiLimbInt) (int8 (-17))

#guard fixedWidthToIntGuard int8Codec ``Int8.toInt
  Int8.toInt (int8 (-128)) (-128)

#guard fixedWidthToIntGuard int8Codec ``Int8.toInt
  Int8.toInt (int8 127) 127

#guard natToFixedWidthGuard uint64Codec ``UInt64.ofNat
  UInt64.ofNat 0 0

#guard natToFixedWidthGuard uint64Codec ``UInt64.ofNat
  UInt64.ofNat 18446744073709551615 0xffffffffffffffff

#guard natToFixedWidthGuard uint64Codec ``UInt64.ofNat
  UInt64.ofNat 18446744073709551616 0

#guard natToFixedWidthGuard uint64Codec ``UInt64.ofNat
  UInt64.ofNat multiLimbNat 17

#guard fixedWidthToNatGuard uint64Codec ``UInt64.toNat
  UInt64.toNat 0 0

#guard fixedWidthToNatGuard uint64Codec ``UInt64.toNat
  UInt64.toNat 0x7fffffffffffffff 9223372036854775807

#guard fixedWidthToNatGuard uint64Codec ``UInt64.toNat
  UInt64.toNat 0x8000000000000000 9223372036854775808

#guard fixedWidthToNatGuard uint64Codec ``UInt64.toNat
  UInt64.toNat 0xffffffffffffffff 18446744073709551615

#guard System.Platform.numBits == 64

#guard natToFixedWidthGuard usizeCodec ``USize.ofNat
  USize.ofNat 0 0

#guard natToFixedWidthGuard usizeCodec ``USize.ofNat
  USize.ofNat 18446744073709551615 0xffffffffffffffff

#guard natToFixedWidthGuard usizeCodec ``USize.ofNat
  USize.ofNat 18446744073709551616 0

#guard natToFixedWidthGuard usizeCodec ``USize.ofNat
  USize.ofNat multiLimbNat 17

#guard fixedWidthToNatGuard usizeCodec ``USize.toNat
  USize.toNat 0 0

#guard fixedWidthToNatGuard usizeCodec ``USize.toNat
  USize.toNat 0x7fffffffffffffff 9223372036854775807

#guard fixedWidthToNatGuard usizeCodec ``USize.toNat
  USize.toNat 0x8000000000000000 9223372036854775808

#guard fixedWidthToNatGuard usizeCodec ``USize.toNat
  USize.toNat 0xffffffffffffffff 18446744073709551615

#guard natToFixedWidthGuard uint8Codec ``UInt8.ofNat
  UInt8.ofNat 255 255

#guard natToFixedWidthGuard uint8Codec ``UInt8.ofNat
  UInt8.ofNat 256 0

#guard natToFixedWidthGuard uint8Codec ``UInt8.ofNat
  UInt8.ofNat multiLimbNat 17

#guard fixedWidthToNatGuard uint8Codec ``UInt8.toNat
  UInt8.toNat 255 255

#guard natToFixedWidthGuard uint16Codec ``UInt16.ofNat
  UInt16.ofNat 65535 65535

#guard natToFixedWidthGuard uint16Codec ``UInt16.ofNat
  UInt16.ofNat 65536 0

#guard natToFixedWidthGuard uint16Codec ``UInt16.ofNat
  UInt16.ofNat multiLimbNat 17

#guard fixedWidthToNatGuard uint16Codec ``UInt16.toNat
  UInt16.toNat 65535 65535

#guard natToFixedWidthGuard uint32Codec ``UInt32.ofNat
  UInt32.ofNat 4294967295 4294967295

#guard natToFixedWidthGuard uint32Codec ``UInt32.ofNat
  UInt32.ofNat 4294967296 0

#guard natToFixedWidthGuard uint32Codec ``UInt32.ofNat
  UInt32.ofNat multiLimbNat 17

#guard fixedWidthToNatGuard uint32Codec ``UInt32.toNat
  UInt32.toNat 4294967295 4294967295

#guard fixedWidthConversionGuard uint8Codec uint16Codec ``UInt8.toUInt16
  UInt8.toUInt16 255 255

#guard fixedWidthConversionGuard uint8Codec uint32Codec ``UInt8.toUInt32
  UInt8.toUInt32 255 255

#guard fixedWidthConversionGuard uint8Codec uint64Codec ``UInt8.toUInt64
  UInt8.toUInt64 255 255

#guard fixedWidthConversionGuard uint8Codec usizeCodec ``UInt8.toUSize
  UInt8.toUSize 255 255

#guard fixedWidthConversionGuard uint16Codec uint8Codec ``UInt16.toUInt8
  UInt16.toUInt8 65535 255

#guard fixedWidthConversionGuard uint16Codec uint32Codec ``UInt16.toUInt32
  UInt16.toUInt32 65535 65535

#guard fixedWidthConversionGuard uint16Codec uint64Codec ``UInt16.toUInt64
  UInt16.toUInt64 65535 65535

#guard fixedWidthConversionGuard uint16Codec usizeCodec ``UInt16.toUSize
  UInt16.toUSize 65535 65535

#guard fixedWidthConversionGuard uint32Codec uint8Codec ``UInt32.toUInt8
  UInt32.toUInt8 4294967295 255

#guard fixedWidthConversionGuard uint32Codec uint16Codec ``UInt32.toUInt16
  UInt32.toUInt16 4294967295 65535

#guard fixedWidthConversionGuard uint32Codec uint64Codec ``UInt32.toUInt64
  UInt32.toUInt64 4294967295 4294967295

#guard fixedWidthConversionGuard uint32Codec usizeCodec ``UInt32.toUSize
  UInt32.toUSize 4294967295 4294967295

#guard fixedWidthConversionGuard uint64Codec uint8Codec ``UInt64.toUInt8
  UInt64.toUInt8 0xffffffffffffffff 255

#guard fixedWidthConversionGuard uint64Codec uint16Codec ``UInt64.toUInt16
  UInt64.toUInt16 0xffffffffffffffff 65535

#guard fixedWidthConversionGuard uint64Codec uint32Codec ``UInt64.toUInt32
  UInt64.toUInt32 0xffffffffffffffff 4294967295

#guard fixedWidthConversionGuard uint64Codec usizeCodec ``UInt64.toUSize
  UInt64.toUSize 0xffffffffffffffff 0xffffffffffffffff

#guard fixedWidthConversionGuard usizeCodec uint8Codec ``USize.toUInt8
  USize.toUInt8 0xffffffffffffffff 255

#guard fixedWidthConversionGuard usizeCodec uint16Codec ``USize.toUInt16
  USize.toUInt16 0xffffffffffffffff 65535

#guard fixedWidthConversionGuard usizeCodec uint32Codec ``USize.toUInt32
  USize.toUInt32 0xffffffffffffffff 4294967295

#guard fixedWidthConversionGuard usizeCodec uint64Codec ``USize.toUInt64
  USize.toUInt64 0xffffffffffffffff 0xffffffffffffffff

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.add UInt8.add 255 1 0

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.sub UInt8.sub 0 1 255

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.mul UInt8.mul 128 2 0

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.div UInt8.div 255 3 85

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.div UInt8.div 255 0 0

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.mod UInt8.mod 255 16 15

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.mod UInt8.mod 255 0 255

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.land UInt8.land 0xf0 0x3c 0x30

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.lor UInt8.lor 0xc0 0x3c 0xfc

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.xor UInt8.xor 0xf0 0x3c 0xcc

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.shiftLeft UInt8.shiftLeft 0x81 8 0x81

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.shiftLeft UInt8.shiftLeft 0x81 9 2

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.shiftRight UInt8.shiftRight 0x81 8 0x81

#guard fixedWidthBinaryGuard uint8Codec ``UInt8.shiftRight UInt8.shiftRight 0x81 9 0x40

#guard fixedWidthUnaryGuard uint8Codec ``UInt8.complement UInt8.complement 0 255

#guard fixedWidthUnaryGuard uint8Codec ``UInt8.neg UInt8.neg 1 255

#guard fixedWidthDecisionGuard uint8Codec ``UInt8.decEq
  (fun left right => decide (left = right)) 255 255 true

#guard fixedWidthDecisionGuard uint8Codec ``UInt8.decEq
  (fun left right => decide (left = right)) 255 0 false

#guard fixedWidthDecisionGuard uint8Codec ``UInt8.decLt
  (fun left right => decide (left < right)) 0 255 true

#guard fixedWidthDecisionGuard uint8Codec ``UInt8.decLt
  (fun left right => decide (left < right)) 255 0 false

#guard fixedWidthDecisionGuard uint8Codec ``UInt8.decLe
  (fun left right => decide (left ≤ right)) 255 255 true

#guard fixedWidthDecisionGuard uint8Codec ``UInt8.decLe
  (fun left right => decide (left ≤ right)) 255 0 false

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.add UInt16.add 0xffff 1 0

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.sub UInt16.sub 0 1 0xffff

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.mul UInt16.mul 0x8000 2 0

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.div UInt16.div 0xffff 3 0x5555

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.div UInt16.div 0xffff 0 0

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.mod UInt16.mod 0xffff 16 15

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.mod UInt16.mod 0xffff 0 0xffff

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.land UInt16.land
  0xf0f0 0x0ff0 0x00f0

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.lor UInt16.lor
  0xf00f 0x0ff0 0xffff

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.xor UInt16.xor
  0xf0f0 0x0ff0 0xff00

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.shiftLeft UInt16.shiftLeft
  0x8001 16 0x8001

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.shiftLeft UInt16.shiftLeft
  0x8001 17 2

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.shiftRight UInt16.shiftRight
  0x8001 16 0x8001

#guard fixedWidthBinaryGuard uint16Codec ``UInt16.shiftRight UInt16.shiftRight
  0x8001 17 0x4000

#guard fixedWidthUnaryGuard uint16Codec ``UInt16.complement UInt16.complement
  0 0xffff

#guard fixedWidthUnaryGuard uint16Codec ``UInt16.neg UInt16.neg 1 0xffff

#guard fixedWidthDecisionGuard uint16Codec ``UInt16.decEq
  (fun left right => decide (left = right)) 0xffff 0xffff true

#guard fixedWidthDecisionGuard uint16Codec ``UInt16.decEq
  (fun left right => decide (left = right)) 0xffff 0 false

#guard fixedWidthDecisionGuard uint16Codec ``UInt16.decLt
  (fun left right => decide (left < right)) 0 0xffff true

#guard fixedWidthDecisionGuard uint16Codec ``UInt16.decLt
  (fun left right => decide (left < right)) 0xffff 0 false

#guard fixedWidthDecisionGuard uint16Codec ``UInt16.decLe
  (fun left right => decide (left ≤ right)) 0xffff 0xffff true

#guard fixedWidthDecisionGuard uint16Codec ``UInt16.decLe
  (fun left right => decide (left ≤ right)) 0xffff 0 false

private def uint32BinaryGuard (name : Name) (operation : UInt32 → UInt32 → UInt32)
    (left right expected : UInt32) : Bool :=
  fixedWidthBinaryGuard uint32Codec name operation left right expected

private def uint32UnaryGuard (name : Name) (operation : UInt32 → UInt32)
    (input expected : UInt32) : Bool :=
  fixedWidthUnaryGuard uint32Codec name operation input expected

private def uint32DecisionGuard (name : Name) (operation : UInt32 → UInt32 → Bool)
    (left right : UInt32) (expected : Bool) : Bool :=
  fixedWidthDecisionGuard uint32Codec name operation left right expected

#guard uint32BinaryGuard ``UInt32.add UInt32.add 4294967295 1 0

#guard uint32BinaryGuard ``UInt32.sub UInt32.sub 0 1 4294967295

#guard uint32BinaryGuard ``UInt32.mul UInt32.mul 2147483648 2 0

#guard uint32BinaryGuard ``UInt32.div UInt32.div 4294967295 3 1431655765

#guard uint32BinaryGuard ``UInt32.div UInt32.div 4294967295 0 0

#guard uint32BinaryGuard ``UInt32.mod UInt32.mod 4294967295 16 15

#guard uint32BinaryGuard ``UInt32.mod UInt32.mod 4294967295 0 4294967295

#guard uint32BinaryGuard ``UInt32.land UInt32.land 0xf0f0f0f0 0x0ff00ff0 0x00f000f0

#guard uint32BinaryGuard ``UInt32.lor UInt32.lor 0xf000000f 0x0ff00ff0 0xfff00fff

#guard uint32BinaryGuard ``UInt32.xor UInt32.xor 0xf0f0f0f0 0x0ff00ff0 0xff00ff00

#guard uint32BinaryGuard ``UInt32.shiftLeft UInt32.shiftLeft 0x80000001 32 0x80000001

#guard uint32BinaryGuard ``UInt32.shiftLeft UInt32.shiftLeft 0x80000001 33 2

#guard uint32BinaryGuard ``UInt32.shiftRight UInt32.shiftRight 0x80000001 32 0x80000001

#guard uint32BinaryGuard ``UInt32.shiftRight UInt32.shiftRight 0x80000001 33 0x40000000

#guard uint32UnaryGuard ``UInt32.complement UInt32.complement 0 4294967295

#guard uint32UnaryGuard ``UInt32.neg UInt32.neg 1 4294967295

#guard uint32DecisionGuard ``UInt32.decEq
  (fun left right => decide (left = right)) 4294967295 4294967295 true

#guard uint32DecisionGuard ``UInt32.decEq
  (fun left right => decide (left = right)) 4294967295 0 false

#guard uint32DecisionGuard ``UInt32.decLt
  (fun left right => decide (left < right)) 0 4294967295 true

#guard uint32DecisionGuard ``UInt32.decLt
  (fun left right => decide (left < right)) 4294967295 0 false

#guard uint32DecisionGuard ``UInt32.decLe
  (fun left right => decide (left ≤ right)) 4294967295 4294967295 true

#guard uint32DecisionGuard ``UInt32.decLe
  (fun left right => decide (left ≤ right)) 4294967295 0 false

private def uint64BinaryGuard (name : Name) (operation : UInt64 → UInt64 → UInt64)
    (left right expected : UInt64) : Bool :=
  fixedWidthBinaryGuard uint64Codec name operation left right expected

private def uint64UnaryGuard (name : Name) (operation : UInt64 → UInt64)
    (input expected : UInt64) : Bool :=
  fixedWidthUnaryGuard uint64Codec name operation input expected

private def uint64DecisionGuard (name : Name) (operation : UInt64 → UInt64 → Bool)
    (left right : UInt64) (expected : Bool) : Bool :=
  fixedWidthDecisionGuard uint64Codec name operation left right expected

#guard uint64BinaryGuard ``UInt64.add UInt64.add 0xffffffffffffffff 1 0

#guard uint64BinaryGuard ``UInt64.sub UInt64.sub 0 1 0xffffffffffffffff

#guard uint64BinaryGuard ``UInt64.mul UInt64.mul 0x8000000000000000 2 0

#guard uint64BinaryGuard ``UInt64.div UInt64.div
  0xffffffffffffffff 3 0x5555555555555555

#guard uint64BinaryGuard ``UInt64.div UInt64.div 0xffffffffffffffff 0 0

#guard uint64BinaryGuard ``UInt64.mod UInt64.mod 0xffffffffffffffff 16 15

#guard uint64BinaryGuard ``UInt64.mod UInt64.mod
  0xffffffffffffffff 0 0xffffffffffffffff

#guard uint64BinaryGuard ``UInt64.land UInt64.land
  0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0 0x00f000f000f000f0

#guard uint64BinaryGuard ``UInt64.lor UInt64.lor
  0xf00000000000000f 0x0ff00ff00ff00ff0 0xfff00ff00ff00fff

#guard uint64BinaryGuard ``UInt64.xor UInt64.xor
  0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0 0xff00ff00ff00ff00

#guard uint64BinaryGuard ``UInt64.shiftLeft UInt64.shiftLeft
  0x8000000000000001 64 0x8000000000000001

#guard uint64BinaryGuard ``UInt64.shiftLeft UInt64.shiftLeft
  0x8000000000000001 65 2

#guard uint64BinaryGuard ``UInt64.shiftRight UInt64.shiftRight
  0x8000000000000001 64 0x8000000000000001

#guard uint64BinaryGuard ``UInt64.shiftRight UInt64.shiftRight
  0x8000000000000001 65 0x4000000000000000

#guard uint64UnaryGuard ``UInt64.complement UInt64.complement 0 0xffffffffffffffff

#guard uint64UnaryGuard ``UInt64.neg UInt64.neg 1 0xffffffffffffffff

#guard uint64DecisionGuard ``UInt64.decEq
  (fun left right => decide (left = right))
  0xffffffffffffffff 0xffffffffffffffff true

#guard uint64DecisionGuard ``UInt64.decEq
  (fun left right => decide (left = right)) 0xffffffffffffffff 0 false

#guard uint64DecisionGuard ``UInt64.decLt
  (fun left right => decide (left < right)) 0 0xffffffffffffffff true

#guard uint64DecisionGuard ``UInt64.decLt
  (fun left right => decide (left < right)) 0xffffffffffffffff 0 false

#guard uint64DecisionGuard ``UInt64.decLe
  (fun left right => decide (left ≤ right))
  0xffffffffffffffff 0xffffffffffffffff true

#guard uint64DecisionGuard ``UInt64.decLe
  (fun left right => decide (left ≤ right)) 0xffffffffffffffff 0 false

#guard System.Platform.numBits == 64

private def usizeBinaryGuard (name : Name) (operation : USize → USize → USize)
    (left right expected : USize) : Bool :=
  fixedWidthBinaryGuard usizeCodec name operation left right expected

private def usizeUnaryGuard (name : Name) (operation : USize → USize)
    (input expected : USize) : Bool :=
  fixedWidthUnaryGuard usizeCodec name operation input expected

private def usizeDecisionGuard (name : Name) (operation : USize → USize → Bool)
    (left right : USize) (expected : Bool) : Bool :=
  fixedWidthDecisionGuard usizeCodec name operation left right expected

#guard usizeBinaryGuard ``USize.add USize.add 0xffffffffffffffff 1 0

#guard usizeBinaryGuard ``USize.sub USize.sub 0 1 0xffffffffffffffff

#guard usizeBinaryGuard ``USize.mul USize.mul 0x8000000000000000 2 0

#guard usizeBinaryGuard ``USize.div USize.div
  0xffffffffffffffff 3 0x5555555555555555

#guard usizeBinaryGuard ``USize.div USize.div 0xffffffffffffffff 0 0

#guard usizeBinaryGuard ``USize.mod USize.mod 0xffffffffffffffff 16 15

#guard usizeBinaryGuard ``USize.mod USize.mod
  0xffffffffffffffff 0 0xffffffffffffffff

#guard usizeBinaryGuard ``USize.land USize.land
  0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0 0x00f000f000f000f0

#guard usizeBinaryGuard ``USize.lor USize.lor
  0xf00000000000000f 0x0ff00ff00ff00ff0 0xfff00ff00ff00fff

#guard usizeBinaryGuard ``USize.xor USize.xor
  0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0 0xff00ff00ff00ff00

#guard usizeBinaryGuard ``USize.shiftLeft USize.shiftLeft
  0x8000000000000001 64 0x8000000000000001

#guard usizeBinaryGuard ``USize.shiftLeft USize.shiftLeft
  0x8000000000000001 65 2

#guard usizeBinaryGuard ``USize.shiftRight USize.shiftRight
  0x8000000000000001 64 0x8000000000000001

#guard usizeBinaryGuard ``USize.shiftRight USize.shiftRight
  0x8000000000000001 65 0x4000000000000000

#guard usizeUnaryGuard ``USize.complement USize.complement 0 0xffffffffffffffff

#guard usizeUnaryGuard ``USize.neg USize.neg 1 0xffffffffffffffff

#guard usizeDecisionGuard ``USize.decEq
  (fun left right => decide (left = right))
  0xffffffffffffffff 0xffffffffffffffff true

#guard usizeDecisionGuard ``USize.decEq
  (fun left right => decide (left = right)) 0xffffffffffffffff 0 false

#guard usizeDecisionGuard ``USize.decLt
  (fun left right => decide (left < right)) 0 0xffffffffffffffff true

#guard usizeDecisionGuard ``USize.decLt
  (fun left right => decide (left < right)) 0xffffffffffffffff 0 false

#guard usizeDecisionGuard ``USize.decLe
  (fun left right => decide (left ≤ right))
  0xffffffffffffffff 0xffffffffffffffff true

#guard usizeDecisionGuard ``USize.decLe
  (fun left right => decide (left ≤ right)) 0xffffffffffffffff 0 false

private abbrev ExternalHandler :=
  ExternalRequest → RuntimeState → Except RuntimeFault ExternalResponse

private structure NamedExternalHandler where
  name : Name
  call : ExternalHandler

private def fixedWidthBinaryHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : α → α → α) : NamedExternalHandler :=
  { name, call := fixedWidthBinaryExternal codec operation }

private def fixedWidthUnaryHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : α → α) : NamedExternalHandler :=
  { name, call := fixedWidthUnaryExternal codec operation }

private def fixedWidthDecisionHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : α → α → Bool) : NamedExternalHandler :=
  { name, call := fixedWidthDecisionExternal codec operation }

private def natToFixedWidthHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : Nat → α) : NamedExternalHandler :=
  { name, call := natToFixedWidthExternal codec operation }

private def intToFixedWidthHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : Int → α) : NamedExternalHandler :=
  { name, call := intToFixedWidthExternal codec operation }

private def fixedWidthToNatHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : α → Nat) : NamedExternalHandler :=
  { name, call := fixedWidthToNatExternal codec operation }

private def fixedWidthToIntHandler (name : Name) (codec : FixedWidthValueCodec α)
    (operation : α → Int) : NamedExternalHandler :=
  { name, call := fixedWidthToIntExternal codec operation }

private def fixedWidthConversionHandler (name : Name)
    (sourceCodec : FixedWidthValueCodec α) (targetCodec : FixedWidthValueCodec β)
    (operation : α → β) : NamedExternalHandler :=
  { name, call := fixedWidthConversionExternal sourceCodec targetCodec operation }

private def signedFixedWidthExternalHandlers
    (contract : SignedFixedWidthContract α) : List NamedExternalHandler :=
  let externalName (suffix : String) := Name.str contract.typeName suffix
  [
    fixedWidthBinaryHandler (externalName "add") contract.codec contract.add,
    fixedWidthBinaryHandler (externalName "sub") contract.codec contract.sub,
    fixedWidthBinaryHandler (externalName "mul") contract.codec contract.mul,
    fixedWidthBinaryHandler (externalName "div") contract.codec contract.div,
    fixedWidthBinaryHandler (externalName "mod") contract.codec contract.modulo,
    fixedWidthBinaryHandler (externalName "land") contract.codec contract.land,
    fixedWidthBinaryHandler (externalName "lor") contract.codec contract.lor,
    fixedWidthBinaryHandler (externalName "xor") contract.codec contract.xor,
    fixedWidthBinaryHandler (externalName "shiftLeft") contract.codec contract.shiftLeft,
    fixedWidthBinaryHandler (externalName "shiftRight") contract.codec contract.shiftRight,
    fixedWidthUnaryHandler (externalName "complement") contract.codec contract.complement,
    fixedWidthUnaryHandler (externalName "neg") contract.codec contract.neg,
    fixedWidthUnaryHandler (externalName "abs") contract.codec contract.abs,
    fixedWidthDecisionHandler (externalName "decEq") contract.codec contract.decEq,
    fixedWidthDecisionHandler (externalName "decLt") contract.codec contract.decLt,
    fixedWidthDecisionHandler (externalName "decLe") contract.codec contract.decLe,
    natToFixedWidthHandler (externalName "ofNat") contract.codec contract.ofNat,
    intToFixedWidthHandler (externalName "ofInt") contract.codec contract.ofInt,
    fixedWidthToIntHandler (externalName "toInt") contract.codec contract.toInt
  ]

private def int8ExternalHandlers : List NamedExternalHandler :=
  signedFixedWidthExternalHandlers int8Contract

private def int16ExternalHandlers : List NamedExternalHandler :=
  signedFixedWidthExternalHandlers int16Contract

private def int32ExternalHandlers : List NamedExternalHandler :=
  signedFixedWidthExternalHandlers int32Contract

private def int64ExternalHandlers : List NamedExternalHandler :=
  signedFixedWidthExternalHandlers int64Contract

private def isizeExternalHandlers : List NamedExternalHandler :=
  signedFixedWidthExternalHandlers isizeContract

private def signedFixedWidthConversionHandlers : List NamedExternalHandler := [
  fixedWidthConversionHandler ``Int8.toInt16 int8Codec int16Codec Int8.toInt16,
  fixedWidthConversionHandler ``Int8.toInt32 int8Codec int32Codec Int8.toInt32,
  fixedWidthConversionHandler ``Int8.toInt64 int8Codec int64Codec Int8.toInt64,
  fixedWidthConversionHandler ``Int8.toISize int8Codec isizeCodec Int8.toISize,
  fixedWidthConversionHandler ``Int16.toInt8 int16Codec int8Codec Int16.toInt8,
  fixedWidthConversionHandler ``Int16.toInt32 int16Codec int32Codec Int16.toInt32,
  fixedWidthConversionHandler ``Int16.toInt64 int16Codec int64Codec Int16.toInt64,
  fixedWidthConversionHandler ``Int16.toISize int16Codec isizeCodec Int16.toISize,
  fixedWidthConversionHandler ``Int32.toInt8 int32Codec int8Codec Int32.toInt8,
  fixedWidthConversionHandler ``Int32.toInt16 int32Codec int16Codec Int32.toInt16,
  fixedWidthConversionHandler ``Int32.toInt64 int32Codec int64Codec Int32.toInt64,
  fixedWidthConversionHandler ``Int32.toISize int32Codec isizeCodec Int32.toISize,
  fixedWidthConversionHandler ``Int64.toInt8 int64Codec int8Codec Int64.toInt8,
  fixedWidthConversionHandler ``Int64.toInt16 int64Codec int16Codec Int64.toInt16,
  fixedWidthConversionHandler ``Int64.toInt32 int64Codec int32Codec Int64.toInt32,
  fixedWidthConversionHandler ``Int64.toISize int64Codec isizeCodec Int64.toISize,
  fixedWidthConversionHandler ``ISize.toInt8 isizeCodec int8Codec ISize.toInt8,
  fixedWidthConversionHandler ``ISize.toInt16 isizeCodec int16Codec ISize.toInt16,
  fixedWidthConversionHandler ``ISize.toInt32 isizeCodec int32Codec ISize.toInt32,
  fixedWidthConversionHandler ``ISize.toInt64 isizeCodec int64Codec ISize.toInt64
]

private def uint8ExternalHandlers : List NamedExternalHandler := [
  fixedWidthBinaryHandler ``UInt8.add uint8Codec UInt8.add,
  fixedWidthBinaryHandler ``UInt8.sub uint8Codec UInt8.sub,
  fixedWidthBinaryHandler ``UInt8.mul uint8Codec UInt8.mul,
  fixedWidthBinaryHandler ``UInt8.div uint8Codec UInt8.div,
  fixedWidthBinaryHandler ``UInt8.mod uint8Codec UInt8.mod,
  fixedWidthBinaryHandler ``UInt8.land uint8Codec UInt8.land,
  fixedWidthBinaryHandler ``UInt8.lor uint8Codec UInt8.lor,
  fixedWidthBinaryHandler ``UInt8.xor uint8Codec UInt8.xor,
  fixedWidthBinaryHandler ``UInt8.shiftLeft uint8Codec UInt8.shiftLeft,
  fixedWidthBinaryHandler ``UInt8.shiftRight uint8Codec UInt8.shiftRight,
  fixedWidthUnaryHandler ``UInt8.complement uint8Codec UInt8.complement,
  fixedWidthUnaryHandler ``UInt8.neg uint8Codec UInt8.neg,
  fixedWidthDecisionHandler ``UInt8.decEq uint8Codec
    (fun left right => decide (left = right)),
  fixedWidthDecisionHandler ``UInt8.decLt uint8Codec
    (fun left right => decide (left < right)),
  fixedWidthDecisionHandler ``UInt8.decLe uint8Codec
    (fun left right => decide (left ≤ right)),
  natToFixedWidthHandler ``UInt8.ofNat uint8Codec UInt8.ofNat,
  fixedWidthToNatHandler ``UInt8.toNat uint8Codec UInt8.toNat,
  fixedWidthConversionHandler ``UInt8.toUInt16 uint8Codec uint16Codec UInt8.toUInt16,
  fixedWidthConversionHandler ``UInt8.toUInt32 uint8Codec uint32Codec UInt8.toUInt32,
  fixedWidthConversionHandler ``UInt8.toUInt64 uint8Codec uint64Codec UInt8.toUInt64,
  fixedWidthConversionHandler ``UInt8.toUSize uint8Codec usizeCodec UInt8.toUSize
]

private def uint16ExternalHandlers : List NamedExternalHandler := [
  fixedWidthBinaryHandler ``UInt16.add uint16Codec UInt16.add,
  fixedWidthBinaryHandler ``UInt16.sub uint16Codec UInt16.sub,
  fixedWidthBinaryHandler ``UInt16.mul uint16Codec UInt16.mul,
  fixedWidthBinaryHandler ``UInt16.div uint16Codec UInt16.div,
  fixedWidthBinaryHandler ``UInt16.mod uint16Codec UInt16.mod,
  fixedWidthBinaryHandler ``UInt16.land uint16Codec UInt16.land,
  fixedWidthBinaryHandler ``UInt16.lor uint16Codec UInt16.lor,
  fixedWidthBinaryHandler ``UInt16.xor uint16Codec UInt16.xor,
  fixedWidthBinaryHandler ``UInt16.shiftLeft uint16Codec UInt16.shiftLeft,
  fixedWidthBinaryHandler ``UInt16.shiftRight uint16Codec UInt16.shiftRight,
  fixedWidthUnaryHandler ``UInt16.complement uint16Codec UInt16.complement,
  fixedWidthUnaryHandler ``UInt16.neg uint16Codec UInt16.neg,
  fixedWidthDecisionHandler ``UInt16.decEq uint16Codec
    (fun left right => decide (left = right)),
  fixedWidthDecisionHandler ``UInt16.decLt uint16Codec
    (fun left right => decide (left < right)),
  fixedWidthDecisionHandler ``UInt16.decLe uint16Codec
    (fun left right => decide (left ≤ right)),
  natToFixedWidthHandler ``UInt16.ofNat uint16Codec UInt16.ofNat,
  fixedWidthToNatHandler ``UInt16.toNat uint16Codec UInt16.toNat,
  fixedWidthConversionHandler ``UInt16.toUInt8 uint16Codec uint8Codec UInt16.toUInt8,
  fixedWidthConversionHandler ``UInt16.toUInt32 uint16Codec uint32Codec UInt16.toUInt32,
  fixedWidthConversionHandler ``UInt16.toUInt64 uint16Codec uint64Codec UInt16.toUInt64,
  fixedWidthConversionHandler ``UInt16.toUSize uint16Codec usizeCodec UInt16.toUSize
]

private def uint32ExternalHandlers : List NamedExternalHandler := [
  fixedWidthBinaryHandler ``UInt32.add uint32Codec UInt32.add,
  fixedWidthBinaryHandler ``UInt32.sub uint32Codec UInt32.sub,
  fixedWidthBinaryHandler ``UInt32.mul uint32Codec UInt32.mul,
  fixedWidthBinaryHandler ``UInt32.div uint32Codec UInt32.div,
  fixedWidthBinaryHandler ``UInt32.mod uint32Codec UInt32.mod,
  fixedWidthBinaryHandler ``UInt32.land uint32Codec UInt32.land,
  fixedWidthBinaryHandler ``UInt32.lor uint32Codec UInt32.lor,
  fixedWidthBinaryHandler ``UInt32.xor uint32Codec UInt32.xor,
  fixedWidthBinaryHandler ``UInt32.shiftLeft uint32Codec UInt32.shiftLeft,
  fixedWidthBinaryHandler ``UInt32.shiftRight uint32Codec UInt32.shiftRight,
  fixedWidthUnaryHandler ``UInt32.complement uint32Codec UInt32.complement,
  fixedWidthUnaryHandler ``UInt32.neg uint32Codec UInt32.neg,
  fixedWidthDecisionHandler ``UInt32.decEq uint32Codec
    (fun left right => decide (left = right)),
  fixedWidthDecisionHandler ``UInt32.decLt uint32Codec
    (fun left right => decide (left < right)),
  fixedWidthDecisionHandler ``UInt32.decLe uint32Codec
    (fun left right => decide (left ≤ right)),
  natToFixedWidthHandler ``UInt32.ofNat uint32Codec UInt32.ofNat,
  fixedWidthToNatHandler ``UInt32.toNat uint32Codec UInt32.toNat,
  fixedWidthConversionHandler ``UInt32.toUInt8 uint32Codec uint8Codec UInt32.toUInt8,
  fixedWidthConversionHandler ``UInt32.toUInt16 uint32Codec uint16Codec UInt32.toUInt16,
  fixedWidthConversionHandler ``UInt32.toUInt64 uint32Codec uint64Codec UInt32.toUInt64,
  fixedWidthConversionHandler ``UInt32.toUSize uint32Codec usizeCodec UInt32.toUSize
]

private def uint64ExternalHandlers : List NamedExternalHandler := [
  fixedWidthBinaryHandler ``UInt64.add uint64Codec UInt64.add,
  fixedWidthBinaryHandler ``UInt64.sub uint64Codec UInt64.sub,
  fixedWidthBinaryHandler ``UInt64.mul uint64Codec UInt64.mul,
  fixedWidthBinaryHandler ``UInt64.div uint64Codec UInt64.div,
  fixedWidthBinaryHandler ``UInt64.mod uint64Codec UInt64.mod,
  fixedWidthBinaryHandler ``UInt64.land uint64Codec UInt64.land,
  fixedWidthBinaryHandler ``UInt64.lor uint64Codec UInt64.lor,
  fixedWidthBinaryHandler ``UInt64.xor uint64Codec UInt64.xor,
  fixedWidthBinaryHandler ``UInt64.shiftLeft uint64Codec UInt64.shiftLeft,
  fixedWidthBinaryHandler ``UInt64.shiftRight uint64Codec UInt64.shiftRight,
  fixedWidthUnaryHandler ``UInt64.complement uint64Codec UInt64.complement,
  fixedWidthUnaryHandler ``UInt64.neg uint64Codec UInt64.neg,
  fixedWidthDecisionHandler ``UInt64.decEq uint64Codec
    (fun left right => decide (left = right)),
  fixedWidthDecisionHandler ``UInt64.decLt uint64Codec
    (fun left right => decide (left < right)),
  fixedWidthDecisionHandler ``UInt64.decLe uint64Codec
    (fun left right => decide (left ≤ right)),
  natToFixedWidthHandler ``UInt64.ofNat uint64Codec UInt64.ofNat,
  fixedWidthToNatHandler ``UInt64.toNat uint64Codec UInt64.toNat,
  fixedWidthConversionHandler ``UInt64.toUInt8 uint64Codec uint8Codec UInt64.toUInt8,
  fixedWidthConversionHandler ``UInt64.toUInt16 uint64Codec uint16Codec UInt64.toUInt16,
  fixedWidthConversionHandler ``UInt64.toUInt32 uint64Codec uint32Codec UInt64.toUInt32,
  fixedWidthConversionHandler ``UInt64.toUSize uint64Codec usizeCodec UInt64.toUSize
]

private def usizeExternalHandlers : List NamedExternalHandler := [
  fixedWidthBinaryHandler ``USize.add usizeCodec USize.add,
  fixedWidthBinaryHandler ``USize.sub usizeCodec USize.sub,
  fixedWidthBinaryHandler ``USize.mul usizeCodec USize.mul,
  fixedWidthBinaryHandler ``USize.div usizeCodec USize.div,
  fixedWidthBinaryHandler ``USize.mod usizeCodec USize.mod,
  fixedWidthBinaryHandler ``USize.land usizeCodec USize.land,
  fixedWidthBinaryHandler ``USize.lor usizeCodec USize.lor,
  fixedWidthBinaryHandler ``USize.xor usizeCodec USize.xor,
  fixedWidthBinaryHandler ``USize.shiftLeft usizeCodec USize.shiftLeft,
  fixedWidthBinaryHandler ``USize.shiftRight usizeCodec USize.shiftRight,
  fixedWidthUnaryHandler ``USize.complement usizeCodec USize.complement,
  fixedWidthUnaryHandler ``USize.neg usizeCodec USize.neg,
  fixedWidthDecisionHandler ``USize.decEq usizeCodec
    (fun left right => decide (left = right)),
  fixedWidthDecisionHandler ``USize.decLt usizeCodec
    (fun left right => decide (left < right)),
  fixedWidthDecisionHandler ``USize.decLe usizeCodec
    (fun left right => decide (left ≤ right)),
  natToFixedWidthHandler ``USize.ofNat usizeCodec USize.ofNat,
  fixedWidthToNatHandler ``USize.toNat usizeCodec USize.toNat,
  fixedWidthConversionHandler ``USize.toUInt8 usizeCodec uint8Codec USize.toUInt8,
  fixedWidthConversionHandler ``USize.toUInt16 usizeCodec uint16Codec USize.toUInt16,
  fixedWidthConversionHandler ``USize.toUInt32 usizeCodec uint32Codec USize.toUInt32,
  fixedWidthConversionHandler ``USize.toUInt64 usizeCodec uint64Codec USize.toUInt64
]

private def fixedWidthExternalHandlers : List NamedExternalHandler :=
  int8ExternalHandlers ++ int16ExternalHandlers ++ int32ExternalHandlers ++
    int64ExternalHandlers ++ isizeExternalHandlers ++ signedFixedWidthConversionHandlers ++
    uint8ExternalHandlers ++ uint16ExternalHandlers ++ uint32ExternalHandlers ++
    uint64ExternalHandlers ++ usizeExternalHandlers

#guard fixedWidthExternalHandlers.length == 220

#guard fixedWidthExternalHandlers.all fun handler =>
  (fixedWidthExternalHandlers.filter fun candidate =>
    candidate.name == handler.name).length == 1

private def dispatchNamedExternal? : List NamedExternalHandler → ExternalRequest →
    RuntimeState → Option (Except RuntimeFault ExternalResponse)
  | [], _, _ => none
  | handler :: handlers, request, runtime =>
      if handler.name == request.name then
        some (handler.call request runtime)
      else
        dispatchNamedExternal? handlers request runtime

/-- Pure runtime primitives explicitly modeled by the validation backend. -/
private def validationExternals : ExternalImpl where
  call request runtime :=
    if request.name == ``Nat.add then
      natAddExternal request runtime
    else if request.name == ``Nat.sub then
      natSubExternal request runtime
    else if request.name == ``Nat.mul then
      natMulExternal request runtime
    else if request.name == ``Nat.div then
      natDivExternal request runtime
    else if request.name == ``Nat.mod then
      natModExternal request runtime
    else if request.name == ``Nat.land then
      natLandExternal request runtime
    else if request.name == ``Nat.lor then
      natLorExternal request runtime
    else if request.name == ``Nat.xor then
      natXorExternal request runtime
    else if request.name == ``Nat.shiftLeft then
      natShiftLeftExternal request runtime
    else if request.name == ``Nat.shiftRight then
      natShiftRightExternal request runtime
    else if request.name == ``Nat.decEq then
      natDecEqExternal request runtime
    else if request.name == ``Nat.decLt then
      natDecLtExternal request runtime
    else if request.name == ``Nat.decLe then
      natDecLeExternal request runtime
    else if request.name == ``String.Internal.length then
      stringLengthExternal request runtime
    else if request.name == ``String.utf8ByteSize then
      stringUtf8ByteSizeExternal request runtime
    else if request.name == ``String.Internal.posOf then
      stringPosOfExternal request runtime
    else if request.name == ``String.Internal.offsetOfPos then
      stringOffsetOfPosExternal request runtime
    else if request.name == ``String.Internal.next then
      stringNextExternal request runtime
    else if request.name == ``String.Internal.extract then
      stringExtractExternal request runtime
    else if request.name == ``String.Internal.append then
      stringAppendExternal request runtime
    else if request.name == ``String.Internal.pushn then
      stringPushnExternal request runtime
    else if request.name == ``String.decEq then
      stringDecEqExternal request runtime
    else if request.name == ``String.decidableLT then
      stringDecLtExternal request runtime
    else if request.name == ``String.compare then
      stringCompareExternal request runtime
    else if request.name == ``Corpus.NativeEffects.recordImpl then
      recordEffectExternal request runtime
    else if request.name == ``Corpus.NativeEffects.recordByteArrayImpl then
      recordByteArrayExternal request runtime
    else if request.name == ``ByteArray.size then
      byteArraySizeExternal request runtime
    else if request.name == ``ByteArray.get! then
      byteArrayGetExternal request runtime
    else if request.name == ``ByteArray.set! then
      byteArraySetExternal request runtime
    else if request.name == ``Int.ofNat then
      intOfNatExternal request runtime
    else if request.name == ``Int.neg then
      intNegExternal request runtime
    else if request.name == ``Int.natAbs then
      intNatAbsExternal request runtime
    else if request.name == ``Int.add then
      intAddExternal request runtime
    else if request.name == ``Int.sub then
      intSubExternal request runtime
    else if request.name == ``Int.mul then
      intMulExternal request runtime
    else if request.name == ``Int.ediv then
      intEDivExternal request runtime
    else if request.name == ``Int.emod then
      intEModExternal request runtime
    else if request.name == ``Int.shiftLeft then
      intShiftLeftExternal request runtime
    else if request.name == ``Int.shiftRight then
      intShiftRightExternal request runtime
    else if request.name == ``Int.decEq then
      intDecEqExternal request runtime
    else if request.name == ``Int.decLt then
      intDecLtExternal request runtime
    else if request.name == ``Int.decLe then
      intDecLeExternal request runtime
    else
      match dispatchNamedExternal? fixedWidthExternalHandlers request runtime with
      | some response => response
      | none =>
          .error (.externalFailure request.name
            "external is not in the validation allowlist")

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
  | .int, .int value => return encodeIntValue runtime value
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
  | .bool, .scalar (.uint8 value) =>
      if value == 0 then return .bool false
      else if value == 1 then return .bool true
      else throw s!"invalid scalar Bool value {value}"
  | .nat, .object (.tagged value) => return .nat value.toNat
  | .nat, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .natural value := cell.object | throw "expected a natural heap object"
      return .nat value
  | .int, .object (.tagged payload) => return .int (← decodeImmediateInt payload)
  | .int, .object (.heap location) =>
      let cell ← getLiveCell runtime location |>.mapError (fun fault => toString (repr fault))
      let .integer value := cell.object | throw "expected a signed-integer heap object"
      return .int value
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

private def decodeEffect (projection : Corpus.EffectProjection)
    (snapshot : ExternalSnapshot) : Except String EffectEvent := do
  let event := snapshot.event
  if projection.argSchemas.size != event.args.size then
    throw (s!"effect projection {projection.operation} expected {projection.argSchemas.size} " ++
      s!"arguments, got {event.args.size}")
  let args ← projection.argSchemas.zip event.args |>.mapM fun (schema, value) =>
    decodeValue snapshot.before schema value
  let result ← match projection.resultSchema with
    | none => pure none
    | some schema => some <$> decodeValue snapshot.after schema event.result
  return { operation := projection.operation, args, result }

private def decodeEffects (projections : Array Corpus.EffectProjection)
    (snapshots : Array ExternalSnapshot) :
    Except String (Array EffectEvent) :=
  snapshots.foldlM (init := #[]) fun effects snapshot => do
    let some projection := projections.find? (·.external == snapshot.event.name)
      | return effects
    return effects.push (← decodeEffect projection snapshot)

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
      value := String.intercalate "," (artifact.missingForms case.requiredLcnfForms).toList },
    { key := "missing-externals",
      value := String.intercalate ","
        ((artifact.missingExternals case.requiredExternals).toList.map toString) }]
  match encodeArgs case.argSchemas case.args with
  | .error message =>
      { caseId := case.id, backend := "lcnf", outcome := .failure message,
        diagnostics := staticDiagnostics }
  | .ok (runtime, args) =>
      let execution :=
        runProgramInstrumented case.fuel validationExternals artifact.program case.entry args runtime
      let missingExecuted := case.requiredExecutedLcnfForms.filter
        (!execution.executedForms.contains ·)
      let missingExecutedExternals := case.requiredExecutedExternals.filter
        (!execution.executedExternals.contains ·)
      let diagnostics := staticDiagnostics ++ #[
        { key := "executed-lcnf-forms",
          value := String.intercalate "," execution.executedForms.toList },
        { key := "executed-lcnf-form-trace",
          value := (toJson execution.executedFormTrace).compress },
        { key := "executed-step-trace",
          value := (toJson execution.executedStepTrace).compress },
        { key := "executed-lcnf-form-counts",
          value := (toJson execution.executedFormCounts).compress },
        { key := "missing-executed-lcnf-forms",
          value := String.intercalate "," missingExecuted.toList },
        { key := "executed-externals",
          value := String.intercalate "," (execution.executedExternals.toList.map toString) },
        { key := "executed-external-trace",
          value := (toJson (execution.executedExternalTrace.map toString)).compress },
        { key := "executed-external-counts",
          value := (toJson execution.executedExternalCounts).compress },
        { key := "missing-executed-externals",
          value := String.intercalate "," (missingExecutedExternals.toList.map toString) },
        { key := "external-events", value := toString execution.externalSnapshots.size },
        { key := "interpreter-steps", value := toString execution.steps }]
      match execution.result with
      | .outOfFuel _ =>
          { caseId := case.id, backend := "lcnf", outcome := .outOfFuel case.fuel, diagnostics }
      | .done observation =>
          if execution.externalSnapshots.size != observation.trace.size then
            { caseId := case.id, backend := "lcnf",
              outcome := .failure "external event-time snapshot telemetry diverged from the trace",
              diagnostics }
          else
            let finalRuntime : RuntimeState := {
              runtime with
              heap := observation.heap
              world := observation.world
              trace := observation.trace }
            match decodeEffects case.effectProjections execution.externalSnapshots with
            | .error message =>
                { caseId := case.id, backend := "lcnf", outcome := .failure message, diagnostics }
            | .ok effects =>
                match observation.outcome with
                | .fault fault =>
                    { caseId := case.id, backend := "lcnf",
                      outcome := .success {
                        termination := .runtimeFault (faultKind fault) (toString (repr fault))
                        effects },
                      diagnostics }
                | .returned value =>
                    match decodeValue finalRuntime case.resultSchema value with
                    | .error message =>
                        { caseId := case.id, backend := "lcnf", outcome := .failure message,
                          diagnostics }
                    | .ok datum =>
                        { caseId := case.id, backend := "lcnf",
                          outcome := .success { termination := .returned datum, effects }, diagnostics }

def runCase (case : Corpus.Case) : CoreM (BackendResult × Artifact) := do
  let artifact ← compileEntry case.entry case.dependencies
  return (execute case artifact, artifact)

end Fir.Validation.Lcnf
