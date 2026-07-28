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

private def externalUInt8 (request : ExternalRequest) (value : Value) : Except RuntimeFault UInt8 :=
  match value with
  | .scalar (.uint8 value) => .ok value
  | _ => .error (.externalFailure request.name "expected a UInt8 scalar")

private def externalUInt32 (request : ExternalRequest) (value : Value) :
    Except RuntimeFault UInt32 :=
  match value with
  | .scalar (.uint32 value) => .ok value
  | _ => .error (.externalFailure request.name "expected a UInt32 scalar")

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
    else if request.name == ``Int.decEq then
      intDecEqExternal request runtime
    else if request.name == ``Int.decLt then
      intDecLtExternal request runtime
    else if request.name == ``Int.decLe then
      intDecLeExternal request runtime
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
