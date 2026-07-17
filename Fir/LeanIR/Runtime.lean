import Fir.LeanIR.Phase

namespace Fir.LeanIR

namespace Impure

open Lean
open Lean.Compiler

abbrev Location := Nat

inductive ObjectRef where
  | tagged (payload : UInt64)
  | heap (location : Location)
  deriving Inhabited, BEq, Repr

inductive ScalarValue where
  | uint8 (value : UInt8)
  | uint16 (value : UInt16)
  | uint32 (value : UInt32)
  | uint64 (value : UInt64)
  deriving Inhabited, BEq, Repr

/-- Values in final impure LCNF, including the internal reset/reuse token. -/
inductive Value where
  | object (reference : ObjectRef)
  | usize (value : UInt64)
  | scalar (value : ScalarValue)
  | erased
  | reuseToken (location? : Option Location)
  deriving Inhabited, BEq, Repr

structure ScalarField where
  width : Nat
  offset : Nat
  value : ScalarValue
  deriving Inhabited, BEq, Repr

structure ConstructorObject where
  tag : Nat
  objectFields : Array Value
  usizeFields : Array UInt64
  scalarFields : List ScalarField
  deriving Inhabited, BEq, Repr

inductive HeapObject where
  | ctor (object : ConstructorObject)
  | closure (function : Name) (arity : Nat) (fixed : Array Value)
  | boxed (type : Expr) (value : Value)
  | string (value : String)
  | natural (value : Nat)
  | integer (value : Int)
  | byteArray (value : Array UInt8)
  | opaque (typeName : Name)
  deriving Inhabited, BEq

structure HeapCell where
  object : HeapObject
  rc : Nat := 1
  persistent : Bool := false
  live : Bool := true
  deriving Inhabited, BEq

abbrev Heap := List (Location × HeapCell)
abbrev Globals := List (Name × Value)
abbrev Env := List (FVarId × Value)

structure ExternalEvent where
  name : Name
  args : Array Value
  result : Value
  deriving Inhabited, BEq, Repr

structure RuntimeState where
  heap : Heap := []
  nextLocation : Location := 0
  globals : Globals := []
  world : Nat := 0
  trace : Array ExternalEvent := #[]
  deriving Inhabited, BEq

inductive RuntimeFault where
  | unknownVar (fvarId : FVarId)
  | unknownDecl (name : Name)
  | unknownJoinPoint (fvarId : FVarId)
  | arityMismatch (expected actual : Nat)
  | deadObject (location : Location)
  | expectedObject
  | expectedConstructor
  | expectedClosure
  | expectedScalar
  | expectedUSize
  | expectedReuseToken
  | objectFieldOutOfBounds (index size : Nat)
  | usizeFieldOutOfBounds (index size : Nat)
  | scalarFieldMissing (width offset : Nat)
  | invalidCases
  | referenceCountUnderflow (location : Location)
  | expectedHeapReference
  | externalFailure (name : Name) (message : String)
  | unreachable
  | malformed (message : String)
  deriving Inhabited, BEq, Repr

def bind (env : Env) (fvarId : FVarId) (value : Value) : Env :=
  (fvarId, value) :: env

def lookup : Env → FVarId → Option Value
  | [], _ => none
  | (candidate, value) :: rest, fvarId =>
      if candidate.name == fvarId.name then some value else lookup rest fvarId

@[simp] theorem lookup_bind_self (env : Env) (fvarId : FVarId) (value : Value) :
    lookup (bind env fvarId value) fvarId = some value := by
  cases fvarId
  simp [bind, lookup]

def bindParams (params : Array (LCNF.Param .impure)) (args : Array Value) :
    Except RuntimeFault Env :=
  if params.size == args.size then
    .ok <| (params.toList.zip args.toList).foldl
      (fun env pair => bind env pair.fst.fvarId pair.snd) []
  else
    .error (.arityMismatch params.size args.size)

def evalArg (env : Env) : LCNF.Arg .impure → Except RuntimeFault Value
  | .erased => .ok .erased
  | .fvar fvarId =>
      match lookup env fvarId with
      | some value => .ok value
      | none => .error (.unknownVar fvarId)
  | .type _ h => nomatch h

def evalArgs (env : Env) (args : Array (LCNF.Arg .impure)) :
    Except RuntimeFault (Array Value) :=
  args.mapM (evalArg env)

def findCell? : Heap → Location → Option HeapCell
  | [], _ => none
  | (candidate, cell) :: rest, location =>
      if candidate == location then some cell else findCell? rest location

def replaceCell : Heap → Location → HeapCell → Option Heap
  | [], _, _ => none
  | (candidate, current) :: rest, location, replacement =>
      if candidate == location then
        some ((candidate, replacement) :: rest)
      else
        ((candidate, current) :: ·) <$> replaceCell rest location replacement

def getLiveCell (runtime : RuntimeState) (location : Location) :
    Except RuntimeFault HeapCell :=
  match findCell? runtime.heap location with
  | some cell => if cell.live then .ok cell else .error (.deadObject location)
  | none => .error (.deadObject location)

def setCell (runtime : RuntimeState) (location : Location) (cell : HeapCell) :
    Except RuntimeFault RuntimeState :=
  match replaceCell runtime.heap location cell with
  | some heap => .ok { runtime with heap }
  | none => .error (.deadObject location)

def alloc (runtime : RuntimeState) (object : HeapObject) (persistent := false) :
    RuntimeState × ObjectRef :=
  let location := runtime.nextLocation
  let cell : HeapCell := { object, persistent, rc := if persistent then 0 else 1 }
  ({ runtime with
      heap := (location, cell) :: runtime.heap
      nextLocation := location + 1 },
    .heap location)

def findGlobal? : Globals → Name → Option Value
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate == name then some value else findGlobal? rest name

def insertGlobal (globals : Globals) (name : Name) (value : Value) : Globals :=
  (name, value) :: globals.filter fun entry => entry.fst != name

def RuntimeState.setGlobal (runtime : RuntimeState) (name : Name) (value : Value) : RuntimeState :=
  { runtime with globals := insertGlobal runtime.globals name value }

def maxTaggedPayload : Nat := 9223372036854775807

def ScalarValue.toUInt64 : ScalarValue → UInt64
  | .uint8 value => UInt64.ofNat value.toNat
  | .uint16 value => UInt64.ofNat value.toNat
  | .uint32 value => UInt64.ofNat value.toNat
  | .uint64 value => value

def Value.objectReference? : Value → Option ObjectRef
  | .object reference => some reference
  | _ => none

def HeapObject.ownedValues : HeapObject → Array Value
  | .ctor object => object.objectFields
  | .closure _ _ fixed => fixed
  | .boxed _ value => #[value]
  | .string _ | .natural _ | .integer _ | .byteArray _ | .opaque _ => #[]

def incLocation (runtime : RuntimeState) (location amount : Nat) :
    Except RuntimeFault RuntimeState := do
  let cell ← getLiveCell runtime location
  if cell.persistent then
    return runtime
  setCell runtime location { cell with rc := cell.rc + amount }

partial def decLocation (runtime : RuntimeState) (location : Location) :
    Except RuntimeFault RuntimeState := do
  let cell ← getLiveCell runtime location
  if cell.persistent then
    return runtime
  if cell.rc = 0 then
    throw (.referenceCountUnderflow location)
  if cell.rc > 1 then
    setCell runtime location { cell with rc := cell.rc - 1 }
  else
    let runtime ← setCell runtime location { cell with rc := 0, live := false }
    cell.object.ownedValues.foldlM (init := runtime) fun runtime value =>
      match value with
      | .object (.heap child) => decLocation runtime child
      | _ => .ok runtime

def incValue (runtime : RuntimeState) (value : Value) (amount : Nat) (check : Bool) :
    Except RuntimeFault RuntimeState :=
  match value with
  | .object (.heap location) => incLocation runtime location amount
  | .object (.tagged _) => if check then .ok runtime else .error .expectedHeapReference
  | _ => .error .expectedObject

def decValueOnce (runtime : RuntimeState) (value : Value) (check : Bool) :
    Except RuntimeFault RuntimeState :=
  match value with
  | .object (.heap location) => decLocation runtime location
  | .object (.tagged _) => if check then .ok runtime else .error .expectedHeapReference
  | _ => .error .expectedObject

def decValue (runtime : RuntimeState) (value : Value) (amount : Nat) (check : Bool) :
    Except RuntimeFault RuntimeState :=
  List.replicate amount value |>.foldlM (init := runtime) fun runtime value =>
    decValueOnce runtime value check

def deleteValue (runtime : RuntimeState) (value : Value) : Except RuntimeFault RuntimeState := do
  let .object (.heap location) := value | throw .expectedHeapReference
  let cell ← getLiveCell runtime location
  setCell runtime location { cell with rc := 0, live := false }

def literal (runtime : RuntimeState) : LCNF.LitValue → RuntimeState × Value
  | .nat value =>
      if value ≤ maxTaggedPayload then
        (runtime, .object (.tagged (UInt64.ofNat value)))
      else
        let (runtime, reference) := alloc runtime (.natural value)
        (runtime, .object reference)
  | .str value =>
      let (runtime, reference) := alloc runtime (.string value)
      (runtime, .object reference)
  | .uint8 value => (runtime, .scalar (.uint8 value))
  | .uint16 value => (runtime, .scalar (.uint16 value))
  | .uint32 value => (runtime, .scalar (.uint32 value))
  | .uint64 value => (runtime, .scalar (.uint64 value))
  | .usize value => (runtime, .usize value)

def allocCtor (runtime : RuntimeState) (info : LCNF.CtorInfo) (args : Array Value) :
    Except RuntimeFault (RuntimeState × Value) := do
  if args.size != info.size then
    throw (.malformed s!"constructor {info.name} expected {info.size} object fields, got {args.size}")
  if info.size == 0 && info.usize == 0 && info.ssize == 0 then
    return (runtime, .object (.tagged (UInt64.ofNat info.cidx)))
  let object : ConstructorObject := {
    tag := info.cidx
    objectFields := args
    usizeFields := Array.replicate info.usize 0
    scalarFields := [] }
  let (runtime, reference) := alloc runtime (.ctor object)
  return (runtime, .object reference)

def getConstructor (runtime : RuntimeState) (value : Value) :
    Except RuntimeFault (Location × HeapCell × ConstructorObject) := do
  let .object (.heap location) := value | throw .expectedConstructor
  let cell ← getLiveCell runtime location
  let .ctor object := cell.object | throw .expectedConstructor
  return (location, cell, object)

def getTag (runtime : RuntimeState) (value : Value) : Except RuntimeFault Nat :=
  match value with
  | .object (.tagged payload) => .ok payload.toNat
  | .object (.heap location) => do
      let cell ← getLiveCell runtime location
      let .ctor object := cell.object | throw .expectedConstructor
      return object.tag
  | .scalar value => .ok value.toUInt64.toNat
  | .usize value => .ok value.toNat
  | _ => .error .expectedConstructor

def getObjectField (runtime : RuntimeState) (value : Value) (index : Nat) :
    Except RuntimeFault Value := do
  let (_, _, object) ← getConstructor runtime value
  match object.objectFields[index]? with
  | some field => return field
  | none => throw (.objectFieldOutOfBounds index object.objectFields.size)

def getUSizeField (runtime : RuntimeState) (value : Value) (index : Nat) :
    Except RuntimeFault Value := do
  let (_, _, object) ← getConstructor runtime value
  match object.usizeFields[index]? with
  | some field => return .usize field
  | none => throw (.usizeFieldOutOfBounds index object.usizeFields.size)

def getScalarField (runtime : RuntimeState) (value : Value) (width offset : Nat) :
    Except RuntimeFault Value := do
  let (_, _, object) ← getConstructor runtime value
  match object.scalarFields.find? fun field => field.width == width && field.offset == offset with
  | some field => return .scalar field.value
  | none => throw (.scalarFieldMissing width offset)

def modifyConstructor (runtime : RuntimeState) (value : Value)
    (modify : ConstructorObject → Except RuntimeFault ConstructorObject) :
    Except RuntimeFault RuntimeState := do
  let (location, cell, object) ← getConstructor runtime value
  let object ← modify object
  setCell runtime location { cell with object := .ctor object }

def setObjectField (runtime : RuntimeState) (value : Value) (index : Nat) (field : Value) :
    Except RuntimeFault RuntimeState :=
  modifyConstructor runtime value fun object =>
    if h : index < object.objectFields.size then
      .ok { object with objectFields := object.objectFields.set index field }
    else
      .error (.objectFieldOutOfBounds index object.objectFields.size)

def setUSizeField (runtime : RuntimeState) (value : Value) (index : Nat) (field : Value) :
    Except RuntimeFault RuntimeState := do
  let .usize field := field | throw .expectedUSize
  modifyConstructor runtime value fun object =>
    if h : index < object.usizeFields.size then
      .ok { object with usizeFields := object.usizeFields.set index field }
    else
      .error (.usizeFieldOutOfBounds index object.usizeFields.size)

def setScalarField (runtime : RuntimeState) (value : Value) (width offset : Nat) (field : Value) :
    Except RuntimeFault RuntimeState := do
  let .scalar field := field | throw .expectedScalar
  modifyConstructor runtime value fun object =>
    let entry : ScalarField := { width, offset, value := field }
    let fields := entry :: object.scalarFields.filter fun old =>
      old.width != width || old.offset != offset
    .ok { object with scalarFields := fields }

def setTag (runtime : RuntimeState) (value : Value) (tag : Nat) : Except RuntimeFault RuntimeState :=
  modifyConstructor runtime value fun object => .ok { object with tag }

def scalarFromType (type : Expr) (payload : UInt64) : Except RuntimeFault Value :=
  if type == LCNF.ImpureType.uint8 then
    .ok (.scalar (.uint8 payload.toUInt8))
  else if type == LCNF.ImpureType.uint16 then
    .ok (.scalar (.uint16 payload.toUInt16))
  else if type == LCNF.ImpureType.uint32 then
    .ok (.scalar (.uint32 payload.toUInt32))
  else if type == LCNF.ImpureType.uint64 then
    .ok (.scalar (.uint64 payload))
  else if type == LCNF.ImpureType.usize then
    .ok (.usize payload)
  else
    .error (.malformed "unbox has an unknown scalar result type")

def box (runtime : RuntimeState) (type : Expr) (value : Value) :
    Except RuntimeFault (RuntimeState × Value) := do
  let payload ←
    match value with
    | .scalar scalar => .ok scalar.toUInt64
    | .usize value => .ok value
    | _ => .error .expectedScalar
  if payload.toNat ≤ maxTaggedPayload then
    return (runtime, .object (.tagged payload))
  let (runtime, reference) := alloc runtime (.boxed type value)
  return (runtime, .object reference)

def unbox (runtime : RuntimeState) (type : Expr) (value : Value) : Except RuntimeFault Value :=
  match value with
  | .object (.tagged payload) => scalarFromType type payload
  | .object (.heap location) => do
      let cell ← getLiveCell runtime location
      let .boxed _ value := cell.object | throw .expectedScalar
      return value
  | _ => .error .expectedObject

def isShared (runtime : RuntimeState) (value : Value) : Except RuntimeFault Value :=
  match value with
  | .object (.tagged _) => .ok (.scalar (.uint8 1))
  | .object (.heap location) => do
      let cell ← getLiveCell runtime location
      let shared := cell.persistent || cell.rc != 1
      return .scalar (.uint8 (if shared then 1 else 0))
  | _ => .error .expectedObject

def reset (runtime : RuntimeState) (count : Nat) (value : Value) :
    Except RuntimeFault (RuntimeState × Value) :=
  match value with
  | .object (.tagged _) => .ok (runtime, .reuseToken none)
  | .object (.heap location) => do
      let cell ← getLiveCell runtime location
      if cell.persistent || cell.rc != 1 then
        let runtime ← decLocation runtime location
        return (runtime, .reuseToken none)
      let .ctor object := cell.object | throw .expectedConstructor
      if count > object.objectFields.size then
        throw (.objectFieldOutOfBounds count object.objectFields.size)
      let released := object.objectFields.extract 0 count
      let cleared := object.objectFields.mapIdx fun index field =>
        if index < count then .object (.tagged 0) else field
      let runtime ← setCell runtime location { cell with object := .ctor { object with objectFields := cleared } }
      let runtime ← released.foldlM (init := runtime) fun runtime field =>
        decValueOnce runtime field true
      return (runtime, .reuseToken (some location))
  | _ => .error .expectedObject

def reuse (runtime : RuntimeState) (token : Value) (info : LCNF.CtorInfo)
    (updateHeader : Bool) (args : Array Value) : Except RuntimeFault (RuntimeState × Value) := do
  let .reuseToken location? := token | throw .expectedReuseToken
  match location? with
  | none => allocCtor runtime info args
  | some location =>
      if args.size != info.size then
        throw (.malformed s!"reuse for {info.name} expected {info.size} object fields, got {args.size}")
      let cell ← getLiveCell runtime location
      let .ctor old := cell.object | throw .expectedConstructor
      let tag := if updateHeader then info.cidx else old.tag
      let object : ConstructorObject := {
        tag
        objectFields := args
        usizeFields := Array.replicate info.usize 0
        scalarFields := [] }
      let runtime ← setCell runtime location { cell with object := .ctor object }
      return (runtime, .object (.heap location))

structure ExternalRequest where
  name : Name
  paramTypes : Array Expr
  resultType : Expr
  args : Array Value
  deriving Inhabited, BEq

structure ExternalResponse where
  value : Value
  heap : Heap
  nextLocation : Location
  world : Nat
  deriving Inhabited, BEq

/-- Relational semantics for runtime and foreign calls. -/
abbrev ExternalSpec := ExternalRequest → RuntimeState → ExternalResponse → Prop

/-- Deterministic implementation used by the fuelled interpreter and tests. -/
structure ExternalImpl where
  call : ExternalRequest → RuntimeState → Except RuntimeFault ExternalResponse

def ExternalImpl.Implements (implementation : ExternalImpl) (specification : ExternalSpec) : Prop :=
  ∀ request before response,
    implementation.call request before = .ok response → specification request before response

def rejectExternals : ExternalImpl where
  call request _ := .error (.externalFailure request.name "no external implementation installed")

inductive Outcome where
  | returned (value : Value)
  | fault (fault : RuntimeFault)
  deriving Inhabited, BEq, Repr

structure Observation where
  outcome : Outcome
  heap : Heap
  world : Nat
  trace : Array ExternalEvent
  deriving Inhabited, BEq

end Impure

end Fir.LeanIR
