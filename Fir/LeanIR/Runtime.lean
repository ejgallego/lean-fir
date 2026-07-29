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
  /-- An IEEE-754 binary32 value, represented by its exact physical bits. -/
  | float32Bits (bits : UInt32)
  /-- An IEEE-754 binary64 value, represented by its exact physical bits. -/
  | float64Bits (bits : UInt64)
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

/-- Exact semantic-heap frame produced by replacing the first cell at one
location. Besides recording the successful replacement, this packages the
target lookup, every other lookup, and the unchanged heap length. -/
structure HeapReplacePost (before after : Heap) (location : Location)
    (replacement : HeapCell) : Prop where
  replaced : replaceCell before location replacement = some after
  target : findCell? after location = some replacement
  frame : ∀ other, other ≠ location →
    findCell? after other = findCell? before other
  length : after.length = before.length

/-- Replacing a location known to occur in the semantic heap succeeds and
exposes its complete lookup frame. -/
theorem replaceCell_spec_of_find
    (heap : Heap) (location : Location) (current replacement : HeapCell)
    (found : findCell? heap location = some current) :
    ∃ after, HeapReplacePost heap after location replacement := by
  induction heap with
  | nil => simp [findCell?] at found
  | cons entry rest ih =>
      obtain ⟨candidate, cell⟩ := entry
      by_cases here : candidate = location
      · subst candidate
        refine ⟨(location, replacement) :: rest, ?_, ?_, ?_, rfl⟩
        · simp [replaceCell]
        · simp [findCell?]
        · intro other different
          simp [findCell?, Ne.symm different]
      · have tailFound : findCell? rest location = some current := by
          simpa [findCell?, here] using found
        obtain ⟨after, post⟩ := ih tailFound
        refine ⟨(candidate, cell) :: after, ?_, ?_, ?_, ?_⟩
        · simp [replaceCell, here, post.replaced]
        · simp [findCell?, here, post.target]
        · intro other different
          by_cases atHead : candidate = other
          · subst candidate
            simp [findCell?]
          · simp [findCell?, atHead, post.frame other different]
        · simp [post.length]

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

/-- `setCell` succeeds whenever its source lookup succeeded, changing only
the requested cell while preserving heap length and the non-heap runtime
components. -/
theorem setCell_spec_of_find
    (runtime : RuntimeState) (location : Location) (current replacement : HeapCell)
    (found : findCell? runtime.heap location = some current) :
    ∃ result,
      setCell runtime location replacement = .ok result ∧
      findCell? result.heap location = some replacement ∧
      (∀ other, other ≠ location →
        findCell? result.heap other = findCell? runtime.heap other) ∧
      result.heap.length = runtime.heap.length ∧
      result.nextLocation = runtime.nextLocation ∧
      result.globals = runtime.globals ∧
      result.world = runtime.world ∧
      result.trace = runtime.trace := by
  obtain ⟨after, post⟩ := replaceCell_spec_of_find runtime.heap location current
    replacement found
  refine ⟨{ runtime with heap := after }, ?_, post.target, post.frame,
    post.length, rfl, rfl, rfl, rfl⟩
  unfold setCell
  rw [post.replaced]

def alloc (runtime : RuntimeState) (object : HeapObject) (persistent := false) :
    RuntimeState × ObjectRef :=
  let location := runtime.nextLocation
  let cell : HeapCell := { object, persistent, rc := if persistent then 0 else 1 }
  ({ runtime with
      heap := (location, cell) :: runtime.heap
      nextLocation := location + 1 },
    .heap location)

def HeapObject.ownedValues : HeapObject → Array Value
  | .ctor object => object.objectFields
  | .closure _ _ fixed => fixed
  | .boxed _ value => #[value]
  | .string _ | .natural _ | .integer _ | .byteArray _ | .opaque _ => #[]

/-- Mark one live heap object and its reachable object graph persistent.

The cell is marked before its owned fields are traversed, so revisiting a
cycle is a no-op. The heap length bounds every simple path through live cells;
the explicit fuel makes that bound proof-visible without changing the total
runtime operation into a possible fault. -/
def markPersistentLocationFuel : Nat → Heap → Location → Heap
  | 0, heap, _ => heap
  | fuel + 1, heap, location =>
      match findCell? heap location with
      | some cell =>
          if !cell.live || cell.persistent then
            heap
          else
            match replaceCell heap location
                { cell with rc := 0, persistent := true } with
            | none => heap
            | some heap =>
                cell.object.ownedValues.foldl (init := heap)
                  fun heap value =>
                    match value with
                    | .object (.heap child) =>
                        markPersistentLocationFuel fuel heap child
                    | _ => heap
      | none => heap

/-- Recursive persistence rewrites cell metadata in place and therefore
preserves the semantic heap's allocation count. -/
@[simp] theorem markPersistentLocationFuel_length
    (fuel : Nat) (heap : Heap) (location : Location) :
    (markPersistentLocationFuel fuel heap location).length = heap.length := by
  induction fuel generalizing heap location with
  | zero => rfl
  | succ fuel ih =>
      rw [markPersistentLocationFuel]
      cases found : findCell? heap location with
      | none => rfl
      | some cell =>
          by_cases skip : !cell.live || cell.persistent
          · simp [found, skip]
          · simp only [found, skip, Bool.false_eq_true, if_false]
            let replacement : HeapCell :=
              { cell with rc := 0, persistent := true }
            obtain ⟨after, post⟩ := replaceCell_spec_of_find heap location cell
              replacement found
            have replaced : replaceCell heap location replacement = some after :=
              post.replaced
            rw [replaced]
            have foldLength (values : Array Value) (start : Heap) :
                (values.foldl (init := start) fun next value =>
                  match value with
                  | .object (.heap child) =>
                      markPersistentLocationFuel fuel next child
                  | _ => next).length = start.length := by
              rw [← Array.foldl_toList]
              generalize values.toList = items
              induction items generalizing start with
              | nil => rfl
              | cons value items itemsIH =>
                  simp only [List.foldl]
                  calc
                    _ = (match value with
                        | .object (.heap child) =>
                            markPersistentLocationFuel fuel start child
                        | _ => start).length := itemsIH _
                    _ = start.length := by
                          cases value with
                          | object reference =>
                              cases reference with
                              | tagged => rfl
                              | heap child => exact ih _ child
                          | usize | scalar | erased | reuseToken => rfl
            exact (foldLength cell.object.ownedValues after).trans post.length

/-- Mirror Lean's `lean_mark_persistent`: heap objects reachable from the
value become live process-lifetime roots with reference count zero. Immediate
and non-object values require no heap transition. -/
def RuntimeState.markPersistent (runtime : RuntimeState) : Value → RuntimeState
  | .object (.heap location) =>
      { runtime with heap :=
          markPersistentLocationFuel (runtime.heap.length + 1) runtime.heap location }
  | _ => runtime

@[simp] theorem RuntimeState.markPersistent_heap_length
    (runtime : RuntimeState) (value : Value) :
    (runtime.markPersistent value).heap.length = runtime.heap.length := by
  cases value with
  | object reference =>
      cases reference <;> simp [RuntimeState.markPersistent]
  | usize | scalar | erased | reuseToken => rfl

@[simp] theorem RuntimeState.markPersistent_nextLocation
    (runtime : RuntimeState) (value : Value) :
    (runtime.markPersistent value).nextLocation = runtime.nextLocation := by
  cases value <;> try rfl
  next reference => cases reference <;> rfl

@[simp] theorem RuntimeState.markPersistent_globals
    (runtime : RuntimeState) (value : Value) :
    (runtime.markPersistent value).globals = runtime.globals := by
  cases value <;> try rfl
  next reference => cases reference <;> rfl

@[simp] theorem RuntimeState.markPersistent_world
    (runtime : RuntimeState) (value : Value) :
    (runtime.markPersistent value).world = runtime.world := by
  cases value <;> try rfl
  next reference => cases reference <;> rfl

@[simp] theorem RuntimeState.markPersistent_trace
    (runtime : RuntimeState) (value : Value) :
    (runtime.markPersistent value).trace = runtime.trace := by
  cases value <;> try rfl
  next reference => cases reference <;> rfl

def findGlobal? : Globals → Name → Option Value
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate == name then some value else findGlobal? rest name

def insertGlobal (globals : Globals) (name : Name) (value : Value) : Globals :=
  (name, value) :: globals.filter fun entry => entry.fst != name

def RuntimeState.setGlobal (runtime : RuntimeState) (name : Name) (value : Value) : RuntimeState :=
  let runtime := runtime.markPersistent value
  { runtime with globals := insertGlobal runtime.globals name value }

def maxTaggedPayload : Nat := 9223372036854775807

def ScalarValue.rawBits : ScalarValue → UInt64
  | .uint8 value => UInt64.ofNat value.toNat
  | .uint16 value => UInt64.ofNat value.toNat
  | .uint32 value => UInt64.ofNat value.toNat
  | .uint64 value => value
  | .float32Bits bits => UInt64.ofNat bits.toNat
  | .float64Bits bits => bits

/--
The physical scalar payload as a `UInt64`.

Kept as the established interface for concrete-runtime consumers; unlike the
old integer-only domain, float cases return their raw IEEE bits.
-/
def ScalarValue.toUInt64 (value : ScalarValue) : UInt64 :=
  value.rawBits

#guard ScalarValue.rawBits (.float32Bits 0x80000000) == 0x80000000
#guard ScalarValue.rawBits (.float64Bits 0x7ff8000000000001) == 0x7ff8000000000001

def Value.objectReference? : Value → Option ObjectRef
  | .object reference => some reference
  | _ => none

def incLocation (runtime : RuntimeState) (location amount : Nat) :
    Except RuntimeFault RuntimeState := do
  let cell ← getLiveCell runtime location
  if cell.persistent then
    return runtime
  setCell runtime location { cell with rc := cell.rc + amount }

/-- Proof-visible recursive decrement. Every nested release consumes one unit
of depth; siblings reuse the remaining depth while threading heap updates. -/
def decLocationFuel : Nat → RuntimeState → Location → Except RuntimeFault RuntimeState
  | 0, _, _ => .error (.malformed "reference-count release fuel exhausted")
  | fuel + 1, runtime, location => do
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
          | .object (.heap child) => decLocationFuel fuel runtime child
          | _ => .ok runtime

/-- The heap length bounds the depth of any successful release chain: a
visited cell is marked dead before its children, so a cycle faults rather than
revisiting a live node. -/
def decLocation (runtime : RuntimeState) (location : Location) :
    Except RuntimeFault RuntimeState :=
  decLocationFuel (runtime.heap.length + 1) runtime location

/-- Regression boundary for W6 ownership refinement: the nonrecursive
above-one branch exposes its exact semantic state update. -/
theorem decLocation_above_one
    (runtime : RuntimeState) (location : Location) (cell : HeapCell)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true) (ordinary : cell.persistent = false)
    (oneLt : 1 < cell.rc) :
    decLocation runtime location =
      setCell runtime location { cell with rc := cell.rc - 1 } := by
  have nonzero : cell.rc ≠ 0 := by omega
  unfold decLocation
  simp only [decLocationFuel, getLiveCell, found, live, ↓reduceIte,
    Bind.bind, Except.bind]
  rw [if_neg (by simp [ordinary])]
  rw [if_neg nonzero, if_pos oneLt]

def incValue (runtime : RuntimeState) (value : Value) (amount : Nat) (check : Bool) :
    Except RuntimeFault RuntimeState :=
  match value with
  | .object (.heap location) => incLocation runtime location amount
  | .object (.tagged _) => if check then .ok runtime else .error .expectedHeapReference
  | _ => .error .expectedObject

/-- Retain one ownership unit when a runtime object transfers an owned field.
Unlike the final-LCNF `inc` instruction, Lean's internal object operation is a
no-op for non-heap values. -/
def retainOwnedValue (runtime : RuntimeState) : Value → Except RuntimeFault RuntimeState
  | .object (.heap location) => incLocation runtime location 1
  | _ => .ok runtime

/--
Consume one reference to a closure and expose its fixed arguments with one
owned reference each, matching Lean's `lean_apply_*` ownership boundary.

An exclusive closure transfers its fixed arguments and is freed without
recursively releasing them. A shared closure keeps its remaining owned fixed
arguments, so the application retains each fixed argument before it runs.
Persistent closures and their recursively persistent captures need no update.
-/
def takeClosureApplication (runtime : RuntimeState) (location : Location) :
    Except RuntimeFault (RuntimeState × Name × Nat × Array Value) := do
  let cell ← getLiveCell runtime location
  let .closure function arity fixed := cell.object | throw .expectedClosure
  if cell.persistent then
    return (runtime, function, arity, fixed)
  if cell.rc = 0 then
    throw (.referenceCountUnderflow location)
  if cell.rc = 1 then
    let runtime ← setCell runtime location { cell with rc := 0, live := false }
    return (runtime, function, arity, fixed)
  let runtime ← setCell runtime location { cell with rc := cell.rc - 1 }
  let runtime ← fixed.foldlM (init := runtime) retainOwnedValue
  return (runtime, function, arity, fixed)

private def takeClosureApplicationGuard (shared : Bool) : Bool :=
  let (runtime, capture) := alloc {} (.natural 1)
  let (runtime, closure) := alloc runtime (.closure `closureTarget 2 #[.object capture])
  match capture, closure with
  | .heap captureLocation, .heap closureLocation =>
      let runtime :=
        if shared then incLocation runtime closureLocation 1 else .ok runtime
      match runtime >>= (takeClosureApplication · closureLocation) with
      | .ok (runtime, function, arity, fixed) =>
          match findCell? runtime.heap captureLocation,
              findCell? runtime.heap closureLocation with
          | some captureCell, some closureCell =>
              function == `closureTarget && arity == 2 &&
                fixed == #[.object capture] &&
                captureCell.live && captureCell.rc == (if shared then 2 else 1) &&
                closureCell.live == shared &&
                closureCell.rc == (if shared then 1 else 0)
          | _, _ => false
      | .error _ => false
  | _, _ => false

#guard takeClosureApplicationGuard false
#guard takeClosureApplicationGuard true

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

/--
Delete one compiler-owned heap object without recursively releasing its fields.

`ExpandResetReuse` passes `.erased` as the failed-reset token and may retain a
rewritten `del` on that path. Lean's native `lean_del_object` treats that zero
sentinel as a no-op. This is an operation-specific exception: tagged objects,
scalars, and reuse tokens remain invalid delete operands.
 -/
def deleteValue (runtime : RuntimeState) (value : Value) : Except RuntimeFault RuntimeState :=
  match value with
  | .erased => .ok runtime
  | .object (.heap location) => do
      let cell ← getLiveCell runtime location
      setCell runtime location { cell with rc := 0, live := false }
  | _ => .error .expectedHeapReference

@[simp] theorem deleteValue_erased (runtime : RuntimeState) :
    deleteValue runtime .erased = .ok runtime := rfl

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

/-- Read one type-local entry from the semantic `USize` field array.

This is a representation-level helper. Final impure LCNF carries an absolute
fixed-slot coordinate; instruction interpreters should use `getUSizeSlot`. -/
def getUSizeField (runtime : RuntimeState) (value : Value) (index : Nat) :
    Except RuntimeFault Value := do
  let (_, _, object) ← getConstructor runtime value
  match object.usizeFields[index]? with
  | some field => return .usize field
  | none => throw (.usizeFieldOutOfBounds index object.usizeFields.size)

/-- Translate Lean final-LCNF's absolute fixed-slot coordinate to FIR's
type-local `usizeFields` representation. Object fields occupy the fixed-slot
prefix; packed scalars follow the `USize` interval. -/
def getUSizeSlot (runtime : RuntimeState) (value : Value) (slot : Nat) :
    Except RuntimeFault Value := do
  let (_, _, object) ← getConstructor runtime value
  let start := object.objectFields.size
  if start ≤ slot then
    let index := slot - start
    match object.usizeFields[index]? with
    | some field => return .usize field
    | none => throw (.usizeFieldOutOfBounds slot (start + object.usizeFields.size))
  else
    throw (.usizeFieldOutOfBounds slot (start + object.usizeFields.size))

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

/-- Write one type-local entry in the semantic `USize` field array.

This is a representation-level helper. Final impure LCNF carries an absolute
fixed-slot coordinate; instruction interpreters should use `setUSizeSlot`. -/
def setUSizeField (runtime : RuntimeState) (value : Value) (index : Nat) (field : Value) :
    Except RuntimeFault RuntimeState := do
  let .usize field := field | throw .expectedUSize
  modifyConstructor runtime value fun object =>
    if h : index < object.usizeFields.size then
      .ok { object with usizeFields := object.usizeFields.set index field }
    else
      .error (.usizeFieldOutOfBounds index object.usizeFields.size)

/-- Write a `USize` field addressed by Lean final-LCNF's absolute fixed-slot
coordinate. -/
def setUSizeSlot (runtime : RuntimeState) (value : Value) (slot : Nat) (field : Value) :
    Except RuntimeFault RuntimeState := do
  let .usize field := field | throw .expectedUSize
  modifyConstructor runtime value fun object =>
    let start := object.objectFields.size
    if start ≤ slot then
      let index := slot - start
      if h : index < object.usizeFields.size then
        .ok { object with usizeFields := object.usizeFields.set index field }
      else
        .error (.usizeFieldOutOfBounds slot (start + object.usizeFields.size))
    else
      .error (.usizeFieldOutOfBounds slot (start + object.usizeFields.size))

private def absoluteUSizeSlotGuard : Bool :=
  let info : LCNF.CtorInfo := {
    name := `MixedLayout
    cidx := 0
    size := 3
    usize := 1
    ssize := 4 }
  match allocCtor {} info #[.object (.tagged 1), .object (.tagged 2), .object (.tagged 3)] with
  | .error _ => false
  | .ok (runtime, object) =>
      match setUSizeSlot runtime object 3 (.usize 77) with
      | .error _ => false
      | .ok runtime =>
          match getUSizeSlot runtime object 3, getUSizeSlot runtime object 2 with
          | .ok (.usize 77), .error (.usizeFieldOutOfBounds 2 4) => true
          | _, _ => false

#guard absoluteUSizeSlotGuard

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

/--
Whether final-LCNF `box` may use Lean's tagged immediate representation.

Float32 and Float boxes are always heap objects: compiler-generated boxed
wrappers release them with unchecked `dec[ref]`. Integer and `USize` boxes
retain the payload-size split.
-/
def boxUsesTaggedRepresentation (type : Expr) (payload : UInt64) : Bool :=
  !(type == LCNF.ImpureType.float32 || type == LCNF.ImpureType.float) &&
    decide (payload.toNat ≤ maxTaggedPayload)

#guard boxUsesTaggedRepresentation LCNF.ImpureType.uint32 0xdeadbeef
#guard !boxUsesTaggedRepresentation LCNF.ImpureType.uint64 0xffffffffffffffff
#guard !boxUsesTaggedRepresentation LCNF.ImpureType.float32 0
#guard !boxUsesTaggedRepresentation LCNF.ImpureType.float 0

def box (runtime : RuntimeState) (type : Expr) (value : Value) :
    Except RuntimeFault (RuntimeState × Value) := do
  let payload ←
    match value with
    | .scalar scalar => .ok scalar.toUInt64
    | .usize value => .ok value
    | _ => .error .expectedScalar
  if boxUsesTaggedRepresentation type payload then
    return (runtime, .object (.tagged payload))
  let (runtime, reference) := alloc runtime (.boxed type value)
  return (runtime, .object reference)

private def floatingBoxGuard : Bool :=
  match box {} LCNF.ImpureType.float32 (.scalar (.float32Bits 0)),
      box {} LCNF.ImpureType.float (.scalar (.float64Bits 0)) with
  | .ok (_, .object (.heap _)), .ok (_, .object (.heap _)) => true
  | _, _ => false

#guard floatingBoxGuard

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

/-- Release one constructor ownership slot while executing reset.

Erased is the canonical non-owning object-field sentinel, so clearing such a
slot performs no reference-count transition. Other values retain the checked
decrement behavior, including faults for invalid scalar and reuse-token slots.
-/
def releaseResetField (runtime : RuntimeState) (value : Value) :
    Except RuntimeFault RuntimeState :=
  match value with
  | .erased => .ok runtime
  | _ => decValueOnce runtime value true

@[simp] theorem releaseResetField_erased (runtime : RuntimeState) :
    releaseResetField runtime .erased = .ok runtime := rfl

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
        releaseResetField runtime field
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
