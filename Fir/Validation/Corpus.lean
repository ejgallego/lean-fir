import Fir.Validation.Protocol

namespace Fir.Validation.Corpus

/-!
Source-level fixtures shared by the native oracle and candidate backends.

The functions in `Source` are deliberately small, but each non-trivial helper is
marked `noinline` so the final impure LCNF retains the operation that its case is
intended to exercise.  The native oracle calls these exact declarations; expected
answers are not stored in the corpus.
-/

namespace NativeEffects

private initialize effectLog : IO.Ref (Array EffectEvent) ← IO.mkRef #[]

private def byteArrayDatum (value : ByteArray) : ValidationDatum :=
  .bytes (value.data.map (UInt8.toNat ·))

def reset : IO Unit :=
  effectLog.set #[]

def take : IO (Array EffectEvent) :=
  effectLog.modifyGet fun effects => (effects, #[])

unsafe def recordImpl (value : Nat) : Nat :=
  unsafeBaseIO do
    let result := value + 1
    effectLog.modify (·.push {
      operation := "validation.record"
      args := #[.nat value]
      result := some (.nat result) })
    return result

unsafe def recordByteArrayImpl (value : ByteArray) (byte : UInt8) : ByteArray :=
  unsafeBaseIO do
    let argument := byteArrayDatum value
    let result := value.set! 0 byte
    let resultDatum := byteArrayDatum result
    effectLog.modify (·.push {
      operation := "validation.recordByteArray"
      args := #[argument, .bits 8 (UInt64.ofNat byte.toNat)]
      result := some resultDatum })
    return result

end NativeEffects

namespace Source

def litNat : Nat :=
  42

def idNat (x : Nat) : Nat :=
  x

def branchNat (b : Bool) : Nat :=
  if b then 1 else 0

def pairFirst (p : Nat × Nat) : Nat :=
  p.1

@[noinline]
def directTarget (x : Nat) : Nat :=
  x

def directCall (x : Nat) : Nat :=
  directTarget x

@[noinline]
def firstNat (x _y : Nat) : Nat :=
  x

@[noinline]
def applyNat (f : Nat → Nat) (x : Nat) : Nat :=
  f x

def capturedPartial (captured x : Nat) : Nat :=
  applyNat (firstNat captured) x

@[noinline]
def lastOr (fallback : Nat) : List Nat → Nat
  | [] => fallback
  | x :: xs => lastOr x xs

def recursiveTraversal (xs : List Nat) : Nat :=
  lastOr 0 xs

def localTailControl (xs : List Nat) : Nat :=
  let rec loop : List Nat → Nat → Nat
    | [], acc => acc
    | x :: tail, _ => loop tail x
  loop xs 0

def largeNat : Nat :=
  18446744073709551616

def idNatList (xs : List Nat) : List Nat :=
  xs

def classifyNatList (xs : List Nat) : UInt64 :=
  match xs with
  | [] => 0
  | _ :: _ => 1

def hasNatListElements (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | _ :: _ => true

def idString (value : String) : String :=
  value

def idUInt8 (value : UInt8) : UInt8 :=
  value

def idUInt16 (value : UInt16) : UInt16 :=
  value

def idUInt32 (value : UInt32) : UInt32 :=
  value

def idUInt64 (value : UInt64) : UInt64 :=
  value

def maxUInt8 : UInt8 := 255

def maxUInt16 : UInt16 := 65535

def maxUInt32 : UInt32 := 4294967295

def maxUInt64 : UInt64 := 18446744073709551615

def maxUSize : USize := 18446744073709551615

@[noinline]
def polyId (α : Type) (value : α) : α :=
  value

def boxedUInt32 (value : UInt32) : UInt32 :=
  polyId UInt32 value

structure PackedPoint where
  x : USize
  y : UInt32

@[noinline]
def PackedPoint.setX (point : PackedPoint) : PackedPoint :=
  { point with x := 1 }

@[noinline]
def PackedPoint.getX (point : PackedPoint) : USize :=
  point.x

def packedPreserve (y : UInt32) : UInt32 :=
  (PackedPoint.setX { x := 0, y }).y

def packedProjectUSize (value : USize) : USize :=
  PackedPoint.getX { x := value, y := 0 }

/-- A source-level aggregate spanning every final-LCNF constructor storage class. -/
structure MixedLayout where
  natural : Nat
  text : String
  bytes : ByteArray
  usize : USize
  scalar : UInt32

@[noinline]
def mkMixedLayout (natural : Nat) (text : String) (bytes : ByteArray)
    (usize : USize) (scalar : UInt32) : MixedLayout :=
  { natural, text, bytes, usize, scalar }

def mixedLayoutNatural (natural : Nat) (text : String) (bytes : ByteArray)
    (usize : USize) (scalar : UInt32) : Nat :=
  (mkMixedLayout natural text bytes usize scalar).natural

def mixedLayoutText (natural : Nat) (text : String) (bytes : ByteArray)
    (usize : USize) (scalar : UInt32) : String :=
  (mkMixedLayout natural text bytes usize scalar).text

def mixedLayoutBytes (natural : Nat) (text : String) (bytes : ByteArray)
    (usize : USize) (scalar : UInt32) : ByteArray :=
  (mkMixedLayout natural text bytes usize scalar).bytes

def mixedLayoutUSize (natural : Nat) (text : String) (bytes : ByteArray)
    (usize : USize) (scalar : UInt32) : USize :=
  (mkMixedLayout natural text bytes usize scalar).usize

def mixedLayoutUInt32 (natural : Nat) (text : String) (bytes : ByteArray)
    (usize : USize) (scalar : UInt32) : UInt32 :=
  (mkMixedLayout natural text bytes usize scalar).scalar

/-- Two adjacent `USize` fields after a nonempty object-field prefix. -/
structure MultiUSizeLayout where
  natural : Nat
  text : String
  first : USize
  second : USize
  scalar : UInt32

@[noinline]
def mkMultiUSizeLayout (natural : Nat) (text : String) (first second : USize)
    (scalar : UInt32) : MultiUSizeLayout :=
  { natural, text, first, second, scalar }

@[noinline]
def MultiUSizeLayout.setFirst (value : MultiUSizeLayout)
    (replacement : USize) : MultiUSizeLayout :=
  { value with first := replacement }

@[noinline]
def MultiUSizeLayout.setSecond (value : MultiUSizeLayout)
    (replacement : USize) : MultiUSizeLayout :=
  { value with second := replacement }

def multiUSizeUpdateFirstPreservesSecond (natural : Nat) (text : String)
    (first second : USize) (scalar : UInt32) (replacement : USize) : USize :=
  (MultiUSizeLayout.setFirst
    (mkMultiUSizeLayout natural text first second scalar) replacement).second

def multiUSizeUpdateSecondPreservesFirst (natural : Nat) (text : String)
    (first second : USize) (scalar : UInt32) (replacement : USize) : USize :=
  (MultiUSizeLayout.setSecond
    (mkMultiUSizeLayout natural text first second scalar) replacement).first

@[noinline]
def chooseUSize (selectUpdated : Bool) (updated original : USize) : USize :=
  if selectUpdated then updated else original

def multiUSizeSharedUpdate (natural : Nat) (text : String)
    (first second : USize) (scalar : UInt32) (replacement : USize)
    (selectUpdated : Bool) : USize :=
  let original := mkMultiUSizeLayout natural text first second scalar
  let updated := MultiUSizeLayout.setFirst original replacement
  chooseUSize selectUpdated updated.first original.first

/-- Every packed scalar width after one object field and one `USize` field. -/
structure MultiScalarLayout where
  natural : Nat
  usize : USize
  byte : UInt8
  half : UInt16
  word : UInt32
  wide : UInt64

@[noinline]
def mkMultiScalarLayout (natural : Nat) (usize : USize) (byte : UInt8)
    (half : UInt16) (word : UInt32) (wide : UInt64) : MultiScalarLayout :=
  { natural, usize, byte, half, word, wide }

@[noinline]
def MultiScalarLayout.setByte (value : MultiScalarLayout)
    (replacement : UInt8) : MultiScalarLayout :=
  { value with byte := replacement }

@[noinline]
def MultiScalarLayout.setHalf (value : MultiScalarLayout)
    (replacement : UInt16) : MultiScalarLayout :=
  { value with half := replacement }

@[noinline]
def MultiScalarLayout.setWord (value : MultiScalarLayout)
    (replacement : UInt32) : MultiScalarLayout :=
  { value with word := replacement }

@[noinline]
def MultiScalarLayout.setWide (value : MultiScalarLayout)
    (replacement : UInt64) : MultiScalarLayout :=
  { value with wide := replacement }

def multiScalarUpdateBytePreservesWide (natural : Nat) (usize : USize)
    (byte : UInt8) (half : UInt16) (word : UInt32) (wide : UInt64)
    (replacement : UInt8) : UInt64 :=
  (MultiScalarLayout.setByte
    (mkMultiScalarLayout natural usize byte half word wide) replacement).wide

def multiScalarUpdateHalfPreservesWord (natural : Nat) (usize : USize)
    (byte : UInt8) (half : UInt16) (word : UInt32) (wide : UInt64)
    (replacement : UInt16) : UInt32 :=
  (MultiScalarLayout.setHalf
    (mkMultiScalarLayout natural usize byte half word wide) replacement).word

def multiScalarUpdateWidePreservesByte (natural : Nat) (usize : USize)
    (byte : UInt8) (half : UInt16) (word : UInt32) (wide : UInt64)
    (replacement : UInt64) : UInt8 :=
  (MultiScalarLayout.setWide
    (mkMultiScalarLayout natural usize byte half word wide) replacement).byte

@[noinline]
def chooseUInt32 (selectUpdated : Bool) (updated original : UInt32) : UInt32 :=
  if selectUpdated then updated else original

def multiScalarSharedWordUpdate (natural : Nat) (usize : USize)
    (byte : UInt8) (half : UInt16) (word : UInt32) (wide : UInt64)
    (replacement : UInt32) (selectUpdated : Bool) : UInt32 :=
  let original := mkMultiScalarLayout natural usize byte half word wide
  let updated := MultiScalarLayout.setWord original replacement
  chooseUInt32 selectUpdated updated.word original.word

/-- Three heap fields before `USize` and scalar neighbors. -/
structure MultiObjectLayout where
  first : Nat
  middle : String
  last : ByteArray
  usize : USize
  scalar : UInt32

@[noinline]
def mkMultiObjectLayout (first : Nat) (middle : String) (last : ByteArray)
    (usize : USize) (scalar : UInt32) : MultiObjectLayout :=
  { first, middle, last, usize, scalar }

@[noinline]
def MultiObjectLayout.setFirst (value : MultiObjectLayout)
    (replacement : Nat) : MultiObjectLayout :=
  { value with first := replacement }

@[noinline]
def MultiObjectLayout.setMiddle (value : MultiObjectLayout)
    (replacement : String) : MultiObjectLayout :=
  { value with middle := replacement }

@[noinline]
def MultiObjectLayout.setLast (value : MultiObjectLayout)
    (replacement : ByteArray) : MultiObjectLayout :=
  { value with last := replacement }

def multiObjectUpdateFirstPreservesLast (first : Nat) (middle : String)
    (last : ByteArray) (usize : USize) (scalar : UInt32)
    (replacement : Nat) : ByteArray :=
  (MultiObjectLayout.setFirst
    (mkMultiObjectLayout first middle last usize scalar) replacement).last

def multiObjectUpdateMiddlePreservesFirst (first : Nat) (middle : String)
    (last : ByteArray) (usize : USize) (scalar : UInt32)
    (replacement : String) : Nat :=
  (MultiObjectLayout.setMiddle
    (mkMultiObjectLayout first middle last usize scalar) replacement).first

def multiObjectUpdateLastPreservesMiddle (first : Nat) (middle : String)
    (last : ByteArray) (usize : USize) (scalar : UInt32)
    (replacement : ByteArray) : String :=
  (MultiObjectLayout.setLast
    (mkMultiObjectLayout first middle last usize scalar) replacement).middle

@[noinline]
def chooseNat (selectUpdated : Bool) (updated original : Nat) : Nat :=
  if selectUpdated then updated else original

def multiObjectSharedFirstUpdate (first : Nat) (middle : String)
    (last : ByteArray) (usize : USize) (scalar : UInt32)
    (replacement : Nat) (selectUpdated : Bool) : Nat :=
  let original := mkMultiObjectLayout first middle last usize scalar
  let updated := MultiObjectLayout.setFirst original replacement
  chooseNat selectUpdated updated.first original.first

/-- Two object fields sharing one `ByteArray`, followed by fixed-width neighbors. -/
structure AliasedByteArrayLayout where
  first : ByteArray
  second : ByteArray
  usize : USize
  scalar : UInt32

@[noinline]
def mkAliasedByteArrayLayout (shared : ByteArray) (usize : USize)
    (scalar : UInt32) : AliasedByteArrayLayout :=
  { first := shared, second := shared, usize, scalar }

@[noinline]
def AliasedByteArrayLayout.setFirst (value : AliasedByteArrayLayout)
    (replacement : ByteArray) : AliasedByteArrayLayout :=
  { value with first := replacement }

@[noinline]
def AliasedByteArrayLayout.setSecond (value : AliasedByteArrayLayout)
    (replacement : ByteArray) : AliasedByteArrayLayout :=
  { value with second := replacement }

def aliasedByteArrayUpdateFirst (shared : ByteArray) (usize : USize)
    (scalar : UInt32) (replacement : ByteArray) : ByteArray × ByteArray :=
  let updated := AliasedByteArrayLayout.setFirst
    (mkAliasedByteArrayLayout shared usize scalar) replacement
  (updated.first, updated.second)

def aliasedByteArrayUpdateSecond (shared : ByteArray) (usize : USize)
    (scalar : UInt32) (replacement : ByteArray) : ByteArray × ByteArray :=
  let updated := AliasedByteArrayLayout.setSecond
    (mkAliasedByteArrayLayout shared usize scalar) replacement
  (updated.first, updated.second)

def aliasedByteArraySharedFirstUpdate (shared : ByteArray) (usize : USize)
    (scalar : UInt32) (replacement : ByteArray) :
    (ByteArray × ByteArray) × (ByteArray × ByteArray) :=
  let original := mkAliasedByteArrayLayout shared usize scalar
  let updated := AliasedByteArrayLayout.setFirst original replacement
  ((updated.first, updated.second), (original.first, original.second))

def aliasedByteArrayChildCopyOnWrite (shared : ByteArray) (usize : USize)
    (scalar : UInt32) (replacement : ByteArray) : ByteArray × ByteArray :=
  let layout := AliasedByteArrayLayout.setFirst
    (mkAliasedByteArrayLayout shared usize scalar) replacement
  let original := layout.second
  let updated := original.set! 0 42
  (original, updated)

def tupleRotate (value : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (value.2.2, value.1, value.2.1)

def idUSize (value : USize) : USize :=
  value

inductive Assoc where
  | atom (value : Nat)
  | node (left right : Assoc)

namespace Assoc

@[noinline] partial def reassoc : Assoc → Assoc
  | .node (.node a b) c => reassoc (.node a (.node b c))
  | value => value

end Assoc

inductive GrowSwitch where
  | left (value : Nat)
  | right (value : Nat)
  | big (first second : Nat)

@[noinline]
def holdNat (value : Nat) : Nat :=
  value

@[noinline]
def changeOrGrow (change : Bool) : GrowSwitch → GrowSwitch
  | .left value =>
      let value := holdNat value
      if change then .right value else .big value value
  | value => value

@[noinline]
def changeOrGrowShared (change : Bool) (value : GrowSwitch) : GrowSwitch × GrowSwitch :=
  let updated := changeOrGrow change value
  (value, updated)

@[noinline]
def applyCaptureList (f : Nat → List Nat) (y : Nat) : List Nat :=
  f y

def capture17List
    (x01 x02 x03 x04 x05 x06 x07 x08 x09 : Nat)
    (x10 x11 x12 x13 x14 x15 x16 x17 : Nat)
    (y : Nat) : List Nat :=
  applyCaptureList
    (fun z =>
      [x01, x02, x03, x04, x05, x06, x07, x08, x09,
       x10, x11, x12, x13, x14, x15, x16, x17, z])
    y

set_option genInjectivity false in
structure BigCtor where
  f01 : Nat := 0
  f02 : Nat := 0
  f03 : Nat := 0
  f04 : Nat := 0
  f05 : Nat := 0
  f06 : Nat := 0
  f07 : Nat := 0
  f08 : Nat := 0
  f09 : Nat := 0
  f10 : Nat := 0
  f11 : Nat := 0
  f12 : Nat := 0
  f13 : Nat := 0
  f14 : Nat := 0
  f15 : Nat := 0
  f16 : Nat := 0
  f17 : Nat := 0
  f18 : Nat := 0
  f19 : Nat := 0
  f20 : Nat := 0
  f21 : Nat := 0
  f22 : Nat := 0
  f23 : Nat := 0
  f24 : Nat := 0
  f25 : Nat := 0
  f26 : Nat := 0
  f27 : Nat := 0
  f28 : Nat := 0
  f29 : Nat := 0
  f30 : Nat := 0
  f31 : Nat := 0
  f32 : Nat := 0
  f33 : Nat := 0
  f34 : Nat := 0
  f35 : Nat := 0
  f36 : Nat := 0
  f37 : Nat := 0
  f38 : Nat := 0
  f39 : Nat := 0
  f40 : Nat := 0
  f41 : Nat := 0
  f42 : Nat := 0
  f43 : Nat := 0
  f44 : Nat := 0
  f45 : Nat := 0
  f46 : Nat := 0
  f47 : Nat := 0
  f48 : Nat := 0
  f49 : Nat := 0
  f50 : Nat := 0
  f51 : Nat := 0
  f52 : Nat := 0
  f53 : Nat := 0
  f54 : Nat := 0
  f55 : Nat := 0
  f56 : Nat := 0
  f57 : Nat := 0
  f58 : Nat := 0
  f59 : Nat := 0
  f60 : Nat := 0
  f61 : Nat := 0
  f62 : Nat := 0
  f63 : Nat := 0
  f64 : Nat := 0
  f65 : Nat := 0
  f66 : Nat := 0
  f67 : Nat := 0
  f68 : Nat := 0
  f69 : Nat := 0
  f70 : Nat := 0

@[noinline]
def mkBigCtor (x : Nat) : BigCtor :=
  { f70 := x }

def bigCtorField (x : Nat) : Nat :=
  (mkBigCtor x).f70

inductive ScalarChoice where
  | first
  | second
  | third

@[noinline]
def selectScalarChoice : ScalarChoice → Nat
  | .first => 10
  | .second => 20
  | .third => 30

def scalarCasesInternal : Nat :=
  selectScalarChoice .third

@[noinline]
def idInt (value : Int) : Int :=
  value

@[noinline]
def intPosImmediate : Int :=
  2147483647

@[noinline]
def intPosHeap : Int :=
  2147483648

@[noinline]
def intNegImmediate : Int :=
  -2147483648

@[noinline]
def intNegHeap : Int :=
  -2147483649

@[noinline]
def classifyInt : Int → Nat
  | .ofNat _ => 10
  | .negSucc _ => 20

@[noinline]
def addNat (left right : Nat) : Nat :=
  left + right

@[implemented_by NativeEffects.recordImpl]
def record (value : Nat) : Nat :=
  value + 1

@[noinline]
def recordOnce (value : Nat) : Nat :=
  record value

@[noinline]
def recordTwice (value : Nat) : Nat :=
  record (record value)

@[implemented_by NativeEffects.recordByteArrayImpl]
def recordByteArray (value : ByteArray) (byte : UInt8) : ByteArray :=
  value.set! 0 byte

@[noinline]
def recordByteArrayTwice (value : ByteArray) : ByteArray :=
  recordByteArray (recordByteArray value 1) 2

@[noinline]
def idByteArray (value : ByteArray) : ByteArray :=
  value

@[noinline]
def byteArraySize (value : ByteArray) : Nat :=
  value.size

@[noinline]
def byteArrayGet (value : ByteArray) (index : Nat) : UInt8 :=
  value.get! index

@[noinline]
def byteArraySetUnique (value : ByteArray) : ByteArray :=
  value.set! 0 255

@[noinline]
def byteArraySetShared (value : ByteArray) : ByteArray × ByteArray :=
  let updated := value.set! 2 255
  (value, updated)

end Source

/-- Stable provenance for a fixture, suitable for carrying into backend reports. -/
structure Provenance where
  suite : String
  path : String
  revision : String := ""
  note : String := ""
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

def firProvenance (note : String) : Provenance := {
  suite := "fir"
  path := "Fir/Validation/Corpus.lean"
  note }

def leanCompileProvenance (path note : String) : Provenance := {
  suite := "lean-tests-compile"
  path
  revision := "b4812ae53eea93439ad5dce5a5c26591c31cb697"
  note }

/-- Select and decode one runtime external as a backend-neutral semantic effect. -/
structure EffectProjection where
  external : Lean.Name
  operation : String
  argSchemas : Array ValidationSchema := #[]
  resultSchema : Option ValidationSchema := none
  deriving Inhabited, BEq, Repr

/-- Closure-free form of `EffectProjection` carried by the corpus manifest. -/
structure EffectProjectionDescriptor where
  external : String
  operation : String
  argSchemas : Array ValidationSchema
  resultSchema : Option ValidationSchema
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

def EffectProjection.descriptor (projection : EffectProjection) : EffectProjectionDescriptor := {
  external := toString projection.external
  operation := projection.operation
  argSchemas := projection.argSchemas
  resultSchema := projection.resultSchema }

/-- A source case and the backend-neutral metadata needed to run it. -/
structure Case where
  id : String
  entry : Lean.Name
  /-- Source helpers that must be compiled with the entry instead of treated as imported externs. -/
  dependencies : Array Lean.Name := #[]
  args : Array ValidationDatum := #[]
  argSchemas : Array ValidationSchema := #[]
  resultSchema : ValidationSchema
  native : Unit → ValidationDatum
  /-- Reset native observation state immediately before running the source case. -/
  nativeBefore : IO Unit := pure ()
  /-- Drain semantic effects after, and data-dependent on, the native execution. -/
  nativeEffects : ValidationDatum → IO (Array EffectEvent) := fun _ => pure #[]
  tags : Array String := #[]
  fuel : Nat := 10000
  requiredLcnfForms : Array String := #[]
  /-- Forms that this fixture must actually step through, not merely retain in the artifact. -/
  requiredExecutedLcnfForms : Array String
  /-- Imported declarations that must remain in the compiled dependency closure. -/
  requiredExternals : Array Lean.Name := #[]
  /-- Imported declarations that this fixture must actually call. -/
  requiredExecutedExternals : Array Lean.Name := #[]
  /-- External events promoted from backend telemetry into the semantic observation. -/
  effectProjections : Array EffectProjection := #[]
  provenance : Provenance := firProvenance "FIR validation fixture"

/-- Closure-free case metadata consumed by runners and future backend adapters. -/
structure CaseDescriptor where
  version : Nat := protocolVersion
  id : String
  entry : String
  dependencies : Array String
  args : Array ValidationDatum
  argSchemas : Array ValidationSchema
  resultSchema : ValidationSchema
  tags : Array String
  fuel : Nat
  requiredLcnfForms : Array String
  requiredExecutedLcnfForms : Array String
  requiredExternals : Array String
  requiredExecutedExternals : Array String
  effectProjections : Array EffectProjectionDescriptor
  provenance : Provenance
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

def Case.descriptor (validationCase : Case) : CaseDescriptor := {
  id := validationCase.id
  entry := toString validationCase.entry
  dependencies := validationCase.dependencies.map toString
  args := validationCase.args
  argSchemas := validationCase.argSchemas
  resultSchema := validationCase.resultSchema
  tags := validationCase.tags
  fuel := validationCase.fuel
  requiredLcnfForms := validationCase.requiredLcnfForms
  requiredExecutedLcnfForms := validationCase.requiredExecutedLcnfForms
  requiredExternals := validationCase.requiredExternals.map toString
  requiredExecutedExternals := validationCase.requiredExecutedExternals.map toString
  effectProjections := validationCase.effectProjections.map EffectProjection.descriptor
  provenance := validationCase.provenance }

private def natListDatum (xs : List Nat) : ValidationDatum :=
  .seq (xs.toArray.map .nat)

private def byteArrayDatum (value : ByteArray) : ValidationDatum :=
  .bytes (value.data.map (UInt8.toNat ·))

private def byteArrayPairDatum (value : ByteArray × ByteArray) : ValidationDatum :=
  .ctor "Prod.mk" 0 #[byteArrayDatum value.1, byteArrayDatum value.2]

private def byteArrayPairPairDatum
    (value : (ByteArray × ByteArray) × (ByteArray × ByteArray)) : ValidationDatum :=
  .ctor "Prod.mk" 0 #[byteArrayPairDatum value.1, byteArrayPairDatum value.2]

private def mixedLayoutText : String :=
  "FIR\nα🙂"

private def mixedLayoutBytes : ByteArray :=
  ⟨#[0, 127, 128, 255]⟩

private def mixedLayoutArgs : Array ValidationDatum :=
  #[.nat Source.largeNat, .string mixedLayoutText, byteArrayDatum mixedLayoutBytes,
    .usize (UInt64.ofNat Source.maxUSize.toNat),
    .bits 32 (UInt64.ofNat Source.maxUInt32.toNat)]

private def mixedLayoutArgSchemas : Array ValidationSchema :=
  #[.nat, .string, .bytes, .usize, .bits 32]

private def multiUSizeArgs : Array ValidationDatum :=
  #[.nat Source.largeNat, .string mixedLayoutText, .usize 17,
    .usize (UInt64.ofNat Source.maxUSize.toNat),
    .bits 32 (UInt64.ofNat Source.maxUInt32.toNat), .usize 42]

private def multiUSizeArgSchemas : Array ValidationSchema :=
  #[.nat, .string, .usize, .usize, .bits 32, .usize]

private def multiUSizeSharedArgs (selectUpdated : Bool) : Array ValidationDatum :=
  multiUSizeArgs.push (.bool selectUpdated)

private def multiUSizeSharedArgSchemas : Array ValidationSchema :=
  multiUSizeArgSchemas.push .bool

private def mixedUpdateForms : Array String :=
  #["cases", "ctor", "dec", "fap", "inc", "isShared", "join", "jump", "oproj",
    "return", "sproj", "sset", "uproj", "uset"]

private def mixedUniqueUpdateExecutedForms : Array String :=
  #["cases", "ctor", "dec", "fap", "isShared", "join", "jump", "oproj", "return",
    "sproj", "sset", "uproj", "uset"]

private def multiScalarBaseArgs : Array ValidationDatum :=
  #[.nat Source.largeNat, .usize (UInt64.ofNat Source.maxUSize.toNat),
    .bits 8 17, .bits 16 4660, .bits 32 (UInt64.ofNat Source.maxUInt32.toNat),
    .bits 64 Source.maxUInt64]

private def multiScalarBaseArgSchemas : Array ValidationSchema :=
  #[.nat, .usize, .bits 8, .bits 16, .bits 32, .bits 64]

private def multiScalarByteArgs : Array ValidationDatum :=
  multiScalarBaseArgs.push (.bits 8 255)

private def multiScalarByteArgSchemas : Array ValidationSchema :=
  multiScalarBaseArgSchemas.push (.bits 8)

private def multiScalarHalfArgs : Array ValidationDatum :=
  multiScalarBaseArgs.push (.bits 16 65535)

private def multiScalarHalfArgSchemas : Array ValidationSchema :=
  multiScalarBaseArgSchemas.push (.bits 16)

private def multiScalarWideArgs : Array ValidationDatum :=
  multiScalarBaseArgs.push (.bits 64 42)

private def multiScalarWideArgSchemas : Array ValidationSchema :=
  multiScalarBaseArgSchemas.push (.bits 64)

private def multiScalarSharedArgs (selectUpdated : Bool) : Array ValidationDatum :=
  multiScalarBaseArgs |>.push (.bits 32 42) |>.push (.bool selectUpdated)

private def multiScalarSharedArgSchemas : Array ValidationSchema :=
  multiScalarBaseArgSchemas |>.push (.bits 32) |>.push .bool

private def multiObjectReplacementNat : Nat :=
  18446744073709551617

private def multiObjectReplacementText : String :=
  "replacement\nβ🚀"

private def multiObjectReplacementBytes : ByteArray :=
  ⟨#[255, 128, 1, 0, 127]⟩

private def multiObjectBaseArgs : Array ValidationDatum :=
  mixedLayoutArgs

private def multiObjectBaseArgSchemas : Array ValidationSchema :=
  mixedLayoutArgSchemas

private def multiObjectFirstArgs : Array ValidationDatum :=
  multiObjectBaseArgs.push (.nat multiObjectReplacementNat)

private def multiObjectFirstArgSchemas : Array ValidationSchema :=
  multiObjectBaseArgSchemas.push .nat

private def multiObjectMiddleArgs : Array ValidationDatum :=
  multiObjectBaseArgs.push (.string multiObjectReplacementText)

private def multiObjectMiddleArgSchemas : Array ValidationSchema :=
  multiObjectBaseArgSchemas.push .string

private def multiObjectLastArgs : Array ValidationDatum :=
  multiObjectBaseArgs.push (byteArrayDatum multiObjectReplacementBytes)

private def multiObjectLastArgSchemas : Array ValidationSchema :=
  multiObjectBaseArgSchemas.push .bytes

private def multiObjectSharedArgs (selectUpdated : Bool) : Array ValidationDatum :=
  multiObjectFirstArgs.push (.bool selectUpdated)

private def multiObjectSharedArgSchemas : Array ValidationSchema :=
  multiObjectFirstArgSchemas.push .bool

private def objectUpdateForms : Array String :=
  mixedUpdateForms.push "oset"

private def objectUniqueUpdateExecutedForms : Array String :=
  mixedUniqueUpdateExecutedForms.push "oset"

private def aliasedByteArrayArgs : Array ValidationDatum :=
  #[byteArrayDatum mixedLayoutBytes, .usize (UInt64.ofNat Source.maxUSize.toNat),
    .bits 32 (UInt64.ofNat Source.maxUInt32.toNat),
    byteArrayDatum multiObjectReplacementBytes]

private def aliasedByteArrayArgSchemas : Array ValidationSchema :=
  #[.bytes, .usize, .bits 32, .bytes]

private def byteArrayPairSchema : ValidationSchema :=
  .ctor "Prod.mk" 0 #[.bytes, .bytes]

private def byteArrayPairPairSchema : ValidationSchema :=
  .ctor "Prod.mk" 0 #[byteArrayPairSchema, byteArrayPairSchema]

private def aliasedChildCopyOnWriteForms : Array String :=
  objectUpdateForms ++ #["extern", "lit"]

private partial def assocDatum : Source.Assoc → ValidationDatum
  | .atom value => .ctor "Assoc.atom" 0 #[.nat value]
  | .node left right => .ctor "Assoc.node" 1 #[assocDatum left, assocDatum right]

private partial def assocSchema : Source.Assoc → ValidationSchema
  | .atom _ => .ctor "Assoc.atom" 0 #[.nat]
  | .node left right => .ctor "Assoc.node" 1 #[assocSchema left, assocSchema right]

private def growSwitchDatum : Source.GrowSwitch → ValidationDatum
  | .left value => .ctor "GrowSwitch.left" 0 #[.nat value]
  | .right value => .ctor "GrowSwitch.right" 1 #[.nat value]
  | .big first second => .ctor "GrowSwitch.big" 2 #[.nat first, .nat second]

private def growSwitchPairDatum (value : Source.GrowSwitch × Source.GrowSwitch) :
    ValidationDatum :=
  .ctor "Prod.mk" 0 #[growSwitchDatum value.1, growSwitchDatum value.2]

private def assocInput : Source.Assoc :=
  .node (.node (.atom 1) (.atom 2)) (.node (.atom 3) (.atom 4))

private def assocExpected : Source.Assoc :=
  .node (.atom 1) (.node (.atom 2) (.node (.atom 3) (.atom 4)))

def cases : Array Case := #[
  { id := "lit-nat"
    entry := ``Source.litNat
    resultSchema := .nat
    native := fun _ => .nat Source.litNat
    tags := #["quick", "literal"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"] },
  { id := "id-nat"
    entry := ``Source.idNat
    args := #[.nat 42]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.idNat 42)
    tags := #["quick", "borrowed"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"] },
  { id := "branch-nat"
    entry := ``Source.branchNat
    args := #[.bool true]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat true)
    tags := #["quick", "control-flow"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"] },
  { id := "branch-nat-false"
    entry := ``Source.branchNat
    args := #[.bool false]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat false)
    tags := #["quick", "control-flow", "boundary"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"] },
  { id := "pair-first"
    entry := ``Source.pairFirst
    args := #[.ctor "Prod.mk" 0 #[.nat 41, .nat 42]]
    argSchemas := #[.ctor "Prod.mk" 0 #[.nat, .nat]]
    resultSchema := .nat
    native := fun _ => .nat (Source.pairFirst (41, 42))
    tags := #["quick", "constructor", "projection"]
    requiredLcnfForms := #["oproj", "inc", "return"]
    requiredExecutedLcnfForms := #["oproj", "inc", "return"] },
  { id := "direct-call"
    entry := ``Source.directCall
    dependencies := #[``Source.directTarget]
    args := #[.nat 41]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.directCall 41)
    tags := #["quick", "call"]
    requiredLcnfForms := #["fap", "return"]
    requiredExecutedLcnfForms := #["fap", "return"] },
  { id := "captured-partial"
    entry := ``Source.capturedPartial
    dependencies := #[``Source.firstNat, ``Source.applyNat]
    args := #[.nat 40, .nat 2]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.capturedPartial 40 2)
    tags := #["quick", "closure", "partial-application"]
    requiredLcnfForms := #["pap", "fap", "return"]
    requiredExecutedLcnfForms := #["pap", "fap", "return"] },
  { id := "recursive-traversal"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum [10, 20, 12]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [10, 20, 12])
    tags := #["quick", "constructor", "recursion"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "oproj", "inc", "fap", "return"] },
  { id := "recursive-empty"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum []]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [])
    tags := #["quick", "constructor", "recursion", "boundary"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "inc", "fap", "return"] },
  { id := "local-tail"
    entry := ``Source.localTailControl
    dependencies := #[`Fir.Validation.Corpus.Source.localTailControl.loop]
    args := #[natListDatum [10, 20, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.localTailControl [10, 20, 42])
    tags := #["quick", "tail-control"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "oproj", "inc", "fap", "return"] },
  { id := "large-nat"
    entry := ``Source.largeNat
    resultSchema := .nat
    native := fun _ => .nat Source.largeNat
    tags := #["quick", "literal", "boundary", "heap"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    provenance := firProvenance "Natural larger than the tagged immediate range" },
  { id := "nat-list-roundtrip"
    entry := ``Source.idNatList
    args := #[natListDatum [0, Source.largeNat, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .seq .nat
    native := fun _ => natListDatum (Source.idNatList [0, Source.largeNat, 42])
    tags := #["quick", "constructor", "boundary", "heap", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Recursive value round-trip containing a heap natural" },
  { id := "nat-list-nonempty"
    entry := ``Source.classifyNatList
    args := #[natListDatum [0, Source.largeNat, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .bits 64
    native := fun _ => .bits 64 (Source.classifyNatList [0, Source.largeNat, 42])
    tags := #["quick", "constructor", "control-flow", "boundary", "heap"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"]
    provenance := firProvenance "Nonempty constructor case over an initial heap graph" },
  { id := "nat-list-nonempty-bool"
    entry := ``Source.hasNatListElements
    args := #[natListDatum [0, Source.largeNat, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.hasNatListElements [0, Source.largeNat, 42])
    tags := #["quick", "constructor", "control-flow", "boundary", "heap", "bool"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"]
    provenance := firProvenance "Boolean result from a nonempty initial heap graph" },
  { id := "nat-list-empty-bool"
    entry := ``Source.hasNatListElements
    args := #[natListDatum []]
    argSchemas := #[.seq .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.hasNatListElements [])
    tags := #["quick", "constructor", "control-flow", "empty", "bool"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"]
    provenance := firProvenance "Scalar false result from the empty list constructor" },
  { id := "unicode-string-roundtrip"
    entry := ``Source.idString
    args := #[.string "hello α_world_β"]
    argSchemas := #[.string]
    resultSchema := .string
    native := fun _ => .string (Source.idString "hello α_world_β")
    tags := #["quick", "string", "unicode", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := leanCompileProvenance "tests/compile/str.lean"
      "Unicode fixture adapted to a pure source-level identity" },
  { id := "uint8-max"
    entry := ``Source.maxUInt8
    resultSchema := .bits 8
    native := fun _ => .bits 8 (UInt64.ofNat Source.maxUInt8.toNat)
    tags := #["quick", "scalar", "boundary"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    provenance := leanCompileProvenance "tests/compile/uint_fold.lean"
      "Maximum-width UInt8 literal" },
  { id := "uint16-max"
    entry := ``Source.maxUInt16
    resultSchema := .bits 16
    native := fun _ => .bits 16 (UInt64.ofNat Source.maxUInt16.toNat)
    tags := #["quick", "scalar", "boundary"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    provenance := leanCompileProvenance "tests/compile/uint_fold.lean"
      "Maximum-width UInt16 literal" },
  { id := "uint32-max"
    entry := ``Source.maxUInt32
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat Source.maxUInt32.toNat)
    tags := #["quick", "scalar", "boundary"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    provenance := leanCompileProvenance "tests/compile/uint_fold.lean"
      "Maximum-width UInt32 literal" },
  { id := "uint64-max"
    entry := ``Source.maxUInt64
    resultSchema := .bits 64
    native := fun _ => .bits 64 Source.maxUInt64
    tags := #["quick", "scalar", "boundary"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    provenance := leanCompileProvenance "tests/compile/uint_fold.lean"
      "Maximum-width UInt64 literal" },
  { id := "usize-max"
    entry := ``Source.maxUSize
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat Source.maxUSize.toNat)
    tags := #["quick", "scalar", "boundary"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    provenance := leanCompileProvenance "tests/compile/uint_fold.lean"
      "Maximum-width USize literal" },
  { id := "uint8-roundtrip"
    entry := ``Source.idUInt8
    args := #[.bits 8 255]
    argSchemas := #[.bits 8]
    resultSchema := .bits 8
    native := fun _ => .bits 8 (UInt64.ofNat (Source.idUInt8 255).toNat)
    tags := #["quick", "scalar", "roundtrip", "boundary"]
    requiredLcnfForms := #["return"]
    requiredExecutedLcnfForms := #["return"]
    provenance := firProvenance "Maximum-width UInt8 ABI round trip" },
  { id := "uint16-roundtrip"
    entry := ``Source.idUInt16
    args := #[.bits 16 65535]
    argSchemas := #[.bits 16]
    resultSchema := .bits 16
    native := fun _ => .bits 16 (UInt64.ofNat (Source.idUInt16 65535).toNat)
    tags := #["quick", "scalar", "roundtrip", "boundary"]
    requiredLcnfForms := #["return"]
    requiredExecutedLcnfForms := #["return"]
    provenance := firProvenance "Maximum-width UInt16 ABI round trip" },
  { id := "uint32-roundtrip"
    entry := ``Source.idUInt32
    args := #[.bits 32 4294967295]
    argSchemas := #[.bits 32]
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat (Source.idUInt32 4294967295).toNat)
    tags := #["quick", "scalar", "roundtrip", "boundary"]
    requiredLcnfForms := #["return"]
    requiredExecutedLcnfForms := #["return"]
    provenance := firProvenance "Maximum-width UInt32 ABI round trip" },
  { id := "uint64-roundtrip"
    entry := ``Source.idUInt64
    args := #[.bits 64 18446744073709551615]
    argSchemas := #[.bits 64]
    resultSchema := .bits 64
    native := fun _ => .bits 64 (Source.idUInt64 18446744073709551615)
    tags := #["quick", "scalar", "roundtrip", "boundary"]
    requiredLcnfForms := #["return"]
    requiredExecutedLcnfForms := #["return"]
    provenance := firProvenance "Maximum-width UInt64 ABI round trip" },
  { id := "boxed-uint32"
    entry := ``Source.boxedUInt32
    dependencies := #[``Source.polyId]
    args := #[.bits 32 4294967295]
    argSchemas := #[.bits 32]
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat (Source.boxedUInt32 4294967295).toNat)
    tags := #["quick", "scalar", "boxing", "polymorphism", "boundary"]
    requiredLcnfForms := #["box", "unbox", "fap", "return"]
    requiredExecutedLcnfForms := #["box", "unbox", "fap", "return"]
    provenance := leanCompileProvenance "tests/compile/typeFormerPolymorphism.lean"
      "Unboxed scalar passed through a noinline polymorphic identity" },
  { id := "packed-preserve"
    entry := ``Source.packedPreserve
    dependencies := #[``Source.PackedPoint.setX]
    args := #[.bits 32 4294967295]
    argSchemas := #[.bits 32]
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat (Source.packedPreserve 4294967295).toNat)
    tags := #["quick", "scalar", "packed-layout", "update", "boundary"]
    requiredLcnfForms := #["ctor", "uset", "sset", "sproj", "fap", "return"]
    requiredExecutedLcnfForms :=
      #["ctor", "uset", "sset", "sproj", "fap", "isShared", "cases", "jump", "return"]
    provenance := leanCompileProvenance "tests/compile/uset.lean"
      "Packed USize/UInt32 structure update preserving the scalar field" },
  { id := "packed-project-usize"
    entry := ``Source.packedProjectUSize
    dependencies := #[``Source.PackedPoint.getX]
    args := #[.usize 42]
    argSchemas := #[.usize]
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat (Source.packedProjectUSize 42).toNat)
    tags := #["quick", "scalar", "packed-layout", "usize", "projection"]
    requiredLcnfForms := #["lit", "ctor", "uset", "sset", "fap", "dec", "return", "uproj"]
    requiredExecutedLcnfForms :=
      #["lit", "ctor", "uset", "sset", "fap", "uproj", "return", "dec"]
    provenance := firProvenance "Project a USize field from a packed mixed-scalar structure" },
  { id := "mixed-layout-natural"
    entry := ``Source.mixedLayoutNatural
    dependencies := #[``Source.mkMixedLayout]
    args := mixedLayoutArgs
    argSchemas := mixedLayoutArgSchemas
    resultSchema := .nat
    native := fun _ => .nat
      (Source.mixedLayoutNatural Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32)
    tags := #["stress", "mixed-layout", "object", "projection", "heap", "boundary"]
    requiredLcnfForms := #["ctor", "uset", "sset", "fap", "oproj", "inc", "dec", "return"]
    requiredExecutedLcnfForms :=
      #["ctor", "uset", "sset", "fap", "oproj", "inc", "dec", "return"]
    provenance := firProvenance
      "Project a heap natural from an aggregate mixing object, USize, and scalar slots" },
  { id := "mixed-layout-string"
    entry := ``Source.mixedLayoutText
    dependencies := #[``Source.mkMixedLayout]
    args := mixedLayoutArgs
    argSchemas := mixedLayoutArgSchemas
    resultSchema := .string
    native := fun _ => .string
      (Source.mixedLayoutText Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32)
    tags := #["stress", "mixed-layout", "object", "projection", "string", "unicode"]
    requiredLcnfForms := #["ctor", "uset", "sset", "fap", "oproj", "inc", "dec", "return"]
    requiredExecutedLcnfForms :=
      #["ctor", "uset", "sset", "fap", "oproj", "inc", "dec", "return"]
    provenance := firProvenance
      "Project a newline and non-BMP Unicode string from a mixed-layout aggregate" },
  { id := "mixed-layout-byte-array"
    entry := ``Source.mixedLayoutBytes
    dependencies := #[``Source.mkMixedLayout]
    args := mixedLayoutArgs
    argSchemas := mixedLayoutArgSchemas
    resultSchema := .bytes
    native := fun _ => byteArrayDatum
      (Source.mixedLayoutBytes Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32)
    tags := #["stress", "mixed-layout", "object", "projection", "bytes", "boundary"]
    requiredLcnfForms := #["ctor", "uset", "sset", "fap", "oproj", "inc", "dec", "return"]
    requiredExecutedLcnfForms :=
      #["ctor", "uset", "sset", "fap", "oproj", "inc", "dec", "return"]
    provenance := firProvenance
      "Project packed boundary bytes from an aggregate with mixed storage classes" },
  { id := "mixed-layout-usize"
    entry := ``Source.mixedLayoutUSize
    dependencies := #[``Source.mkMixedLayout]
    args := mixedLayoutArgs
    argSchemas := mixedLayoutArgSchemas
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat
      (Source.mixedLayoutUSize Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32).toNat)
    tags := #["stress", "mixed-layout", "usize", "projection", "boundary"]
    requiredLcnfForms := #["ctor", "uset", "sset", "fap", "uproj", "dec", "return"]
    requiredExecutedLcnfForms := #["ctor", "uset", "sset", "fap", "uproj", "dec", "return"]
    provenance := firProvenance
      "Project maximum USize from an aggregate mixing object and scalar slots" },
  { id := "mixed-layout-uint32"
    entry := ``Source.mixedLayoutUInt32
    dependencies := #[``Source.mkMixedLayout]
    args := mixedLayoutArgs
    argSchemas := mixedLayoutArgSchemas
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat
      (Source.mixedLayoutUInt32 Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32).toNat)
    tags := #["stress", "mixed-layout", "scalar", "projection", "boundary"]
    requiredLcnfForms := #["ctor", "uset", "sset", "fap", "sproj", "dec", "return"]
    requiredExecutedLcnfForms := #["ctor", "uset", "sset", "fap", "sproj", "dec", "return"]
    provenance := firProvenance
      "Project maximum UInt32 from an aggregate mixing object and USize slots" },
  { id := "multi-usize-update-first-preserves-second"
    entry := ``Source.multiUSizeUpdateFirstPreservesSecond
    dependencies := #[``Source.mkMultiUSizeLayout, ``Source.MultiUSizeLayout.setFirst]
    args := multiUSizeArgs
    argSchemas := multiUSizeArgSchemas
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat
      (Source.multiUSizeUpdateFirstPreservesSecond Source.largeNat mixedLayoutText
        17 Source.maxUSize Source.maxUInt32 42).toNat)
    tags :=
      #["stress", "mixed-layout", "usize", "mutation", "unique", "neighbor", "boundary"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update absolute USize slot 2 while preserving adjacent slot 3 on the unique path" },
  { id := "multi-usize-update-second-preserves-first"
    entry := ``Source.multiUSizeUpdateSecondPreservesFirst
    dependencies := #[``Source.mkMultiUSizeLayout, ``Source.MultiUSizeLayout.setSecond]
    args := multiUSizeArgs
    argSchemas := multiUSizeArgSchemas
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat
      (Source.multiUSizeUpdateSecondPreservesFirst Source.largeNat mixedLayoutText
        17 Source.maxUSize Source.maxUInt32 42).toNat)
    tags :=
      #["stress", "mixed-layout", "usize", "mutation", "unique", "neighbor", "boundary"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update absolute USize slot 3 while preserving adjacent slot 2 on the unique path" },
  { id := "multi-usize-shared-updated"
    entry := ``Source.multiUSizeSharedUpdate
    dependencies :=
      #[``Source.mkMultiUSizeLayout, ``Source.MultiUSizeLayout.setFirst, ``Source.chooseUSize]
    args := multiUSizeSharedArgs true
    argSchemas := multiUSizeSharedArgSchemas
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat
      (Source.multiUSizeSharedUpdate Source.largeNat mixedLayoutText
        17 Source.maxUSize Source.maxUInt32 42 true).toNat)
    tags :=
      #["stress", "mixed-layout", "usize", "mutation", "shared", "copy-on-write", "updated"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Force shared update of absolute USize slot 2 and observe the replacement" },
  { id := "multi-usize-shared-original"
    entry := ``Source.multiUSizeSharedUpdate
    dependencies :=
      #[``Source.mkMultiUSizeLayout, ``Source.MultiUSizeLayout.setFirst, ``Source.chooseUSize]
    args := multiUSizeSharedArgs false
    argSchemas := multiUSizeSharedArgSchemas
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat
      (Source.multiUSizeSharedUpdate Source.largeNat mixedLayoutText
        17 Source.maxUSize Source.maxUInt32 42 false).toNat)
    tags :=
      #["stress", "mixed-layout", "usize", "mutation", "shared", "copy-on-write", "original"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Force shared update of absolute USize slot 2 while observing the retained original" },
  { id := "multi-scalar-update-byte-preserves-wide"
    entry := ``Source.multiScalarUpdateBytePreservesWide
    dependencies := #[``Source.mkMultiScalarLayout, ``Source.MultiScalarLayout.setByte]
    args := multiScalarByteArgs
    argSchemas := multiScalarByteArgSchemas
    resultSchema := .bits 64
    native := fun _ =>
      .bits 64 (Source.multiScalarUpdateBytePreservesWide Source.largeNat Source.maxUSize
        17 4660 Source.maxUInt32 Source.maxUInt64 255)
    tags :=
      #["stress", "mixed-layout", "scalar", "mutation", "unique", "neighbor", "uint8",
        "uint64", "boundary"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update source-leading UInt8 at scalar offset 14 while preserving UInt64 at offset 0" },
  { id := "multi-scalar-update-half-preserves-word"
    entry := ``Source.multiScalarUpdateHalfPreservesWord
    dependencies := #[``Source.mkMultiScalarLayout, ``Source.MultiScalarLayout.setHalf]
    args := multiScalarHalfArgs
    argSchemas := multiScalarHalfArgSchemas
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat
      (Source.multiScalarUpdateHalfPreservesWord Source.largeNat Source.maxUSize
        17 4660 Source.maxUInt32 Source.maxUInt64 65535).toNat)
    tags :=
      #["stress", "mixed-layout", "scalar", "mutation", "unique", "neighbor", "uint16",
        "uint32", "boundary"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update UInt16 at scalar offset 12 while preserving UInt32 at offset 8 on the unique path" },
  { id := "multi-scalar-update-wide-preserves-byte"
    entry := ``Source.multiScalarUpdateWidePreservesByte
    dependencies := #[``Source.mkMultiScalarLayout, ``Source.MultiScalarLayout.setWide]
    args := multiScalarWideArgs
    argSchemas := multiScalarWideArgSchemas
    resultSchema := .bits 8
    native := fun _ => .bits 8 (UInt64.ofNat
      (Source.multiScalarUpdateWidePreservesByte Source.largeNat Source.maxUSize
        17 4660 Source.maxUInt32 Source.maxUInt64 42).toNat)
    tags :=
      #["stress", "mixed-layout", "scalar", "mutation", "unique", "neighbor", "uint64",
        "uint8", "boundary"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update source-trailing UInt64 at scalar offset 0 while preserving UInt8 at offset 14" },
  { id := "multi-scalar-shared-updated"
    entry := ``Source.multiScalarSharedWordUpdate
    dependencies :=
      #[``Source.mkMultiScalarLayout, ``Source.MultiScalarLayout.setWord, ``Source.chooseUInt32]
    args := multiScalarSharedArgs true
    argSchemas := multiScalarSharedArgSchemas
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat
      (Source.multiScalarSharedWordUpdate Source.largeNat Source.maxUSize
        17 4660 Source.maxUInt32 Source.maxUInt64 42 true).toNat)
    tags :=
      #["stress", "mixed-layout", "scalar", "mutation", "shared", "copy-on-write", "uint32",
        "updated"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Force a shared UInt32 update at scalar offset 8 and observe the replacement" },
  { id := "multi-scalar-shared-original"
    entry := ``Source.multiScalarSharedWordUpdate
    dependencies :=
      #[``Source.mkMultiScalarLayout, ``Source.MultiScalarLayout.setWord, ``Source.chooseUInt32]
    args := multiScalarSharedArgs false
    argSchemas := multiScalarSharedArgSchemas
    resultSchema := .bits 32
    native := fun _ => .bits 32 (UInt64.ofNat
      (Source.multiScalarSharedWordUpdate Source.largeNat Source.maxUSize
        17 4660 Source.maxUInt32 Source.maxUInt64 42 false).toNat)
    tags :=
      #["stress", "mixed-layout", "scalar", "mutation", "shared", "copy-on-write", "uint32",
        "original"]
    requiredLcnfForms := mixedUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Force a shared UInt32 update at scalar offset 8 while observing the retained original" },
  { id := "multi-object-update-first-preserves-last"
    entry := ``Source.multiObjectUpdateFirstPreservesLast
    dependencies := #[``Source.mkMultiObjectLayout, ``Source.MultiObjectLayout.setFirst]
    args := multiObjectFirstArgs
    argSchemas := multiObjectFirstArgSchemas
    resultSchema := .bytes
    native := fun _ => byteArrayDatum
      (Source.multiObjectUpdateFirstPreservesLast Source.largeNat mixedLayoutText
        mixedLayoutBytes Source.maxUSize Source.maxUInt32 multiObjectReplacementNat)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "neighbor", "nat",
        "bytearray", "heap", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update object slot 0 with a heap natural while preserving ByteArray slot 2" },
  { id := "multi-object-update-middle-preserves-first"
    entry := ``Source.multiObjectUpdateMiddlePreservesFirst
    dependencies := #[``Source.mkMultiObjectLayout, ``Source.MultiObjectLayout.setMiddle]
    args := multiObjectMiddleArgs
    argSchemas := multiObjectMiddleArgSchemas
    resultSchema := .nat
    native := fun _ => .nat
      (Source.multiObjectUpdateMiddlePreservesFirst Source.largeNat mixedLayoutText
        mixedLayoutBytes Source.maxUSize Source.maxUInt32 multiObjectReplacementText)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "neighbor", "string",
        "nat", "heap", "unicode", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update object slot 1 with a Unicode string while preserving heap-natural slot 0" },
  { id := "multi-object-update-last-preserves-middle"
    entry := ``Source.multiObjectUpdateLastPreservesMiddle
    dependencies := #[``Source.mkMultiObjectLayout, ``Source.MultiObjectLayout.setLast]
    args := multiObjectLastArgs
    argSchemas := multiObjectLastArgSchemas
    resultSchema := .string
    native := fun _ => .string
      (Source.multiObjectUpdateLastPreservesMiddle Source.largeNat mixedLayoutText
        mixedLayoutBytes Source.maxUSize Source.maxUInt32 multiObjectReplacementBytes)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "neighbor", "bytearray",
        "string", "heap", "unicode", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUniqueUpdateExecutedForms
    provenance := firProvenance
      "Update object slot 2 with a ByteArray while preserving Unicode string slot 1" },
  { id := "multi-object-shared-first-updated"
    entry := ``Source.multiObjectSharedFirstUpdate
    dependencies :=
      #[``Source.mkMultiObjectLayout, ``Source.MultiObjectLayout.setFirst, ``Source.chooseNat]
    args := multiObjectSharedArgs true
    argSchemas := multiObjectSharedArgSchemas
    resultSchema := .nat
    native := fun _ => .nat
      (Source.multiObjectSharedFirstUpdate Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32 multiObjectReplacementNat true)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "shared", "copy-on-write", "nat",
        "heap", "boundary", "updated"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Force shared replacement of heap-natural object slot 0 and observe the updated copy" },
  { id := "multi-object-shared-first-original"
    entry := ``Source.multiObjectSharedFirstUpdate
    dependencies :=
      #[``Source.mkMultiObjectLayout, ``Source.MultiObjectLayout.setFirst, ``Source.chooseNat]
    args := multiObjectSharedArgs false
    argSchemas := multiObjectSharedArgSchemas
    resultSchema := .nat
    native := fun _ => .nat
      (Source.multiObjectSharedFirstUpdate Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize Source.maxUInt32 multiObjectReplacementNat false)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "shared", "copy-on-write", "nat",
        "heap", "boundary", "original"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Force shared replacement of heap-natural object slot 0 while retaining the original" },
  { id := "aliased-byte-array-update-first"
    entry := ``Source.aliasedByteArrayUpdateFirst
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setFirst]
    args := aliasedByteArrayArgs
    argSchemas := aliasedByteArrayArgSchemas
    resultSchema := byteArrayPairSchema
    native := fun _ => byteArrayPairDatum
      (Source.aliasedByteArrayUpdateFirst mixedLayoutBytes Source.maxUSize
        Source.maxUInt32 multiObjectReplacementBytes)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "alias", "refcount",
        "bytearray", "heap", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUpdateForms
    provenance := firProvenance
      "Replace aliased object slot 0 while returning its replacement and surviving slot-1 alias" },
  { id := "aliased-byte-array-update-second"
    entry := ``Source.aliasedByteArrayUpdateSecond
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setSecond]
    args := aliasedByteArrayArgs
    argSchemas := aliasedByteArrayArgSchemas
    resultSchema := byteArrayPairSchema
    native := fun _ => byteArrayPairDatum
      (Source.aliasedByteArrayUpdateSecond mixedLayoutBytes Source.maxUSize
        Source.maxUInt32 multiObjectReplacementBytes)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "alias", "refcount",
        "bytearray", "heap", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUpdateForms
    provenance := firProvenance
      "Replace aliased object slot 1 while returning the surviving slot-0 alias and replacement" },
  { id := "aliased-byte-array-shared-first"
    entry := ``Source.aliasedByteArraySharedFirstUpdate
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setFirst]
    args := aliasedByteArrayArgs
    argSchemas := aliasedByteArrayArgSchemas
    resultSchema := byteArrayPairPairSchema
    native := fun _ => byteArrayPairPairDatum
      (Source.aliasedByteArraySharedFirstUpdate mixedLayoutBytes Source.maxUSize
        Source.maxUInt32 multiObjectReplacementBytes)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "shared", "copy-on-write", "alias",
        "refcount", "bytearray", "heap", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    provenance := firProvenance
      "Return both updated and original field pairs after replacing slot 0 of a shared aggregate" },
  { id := "aliased-byte-array-child-copy-on-write"
    entry := ``Source.aliasedByteArrayChildCopyOnWrite
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setFirst]
    args := aliasedByteArrayArgs
    argSchemas := aliasedByteArrayArgSchemas
    resultSchema := byteArrayPairSchema
    native := fun _ => byteArrayPairDatum
      (Source.aliasedByteArrayChildCopyOnWrite mixedLayoutBytes Source.maxUSize
        Source.maxUInt32 multiObjectReplacementBytes)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "alias", "refcount",
        "bytearray", "external", "copy-on-write", "heap", "boundary"]
    requiredLcnfForms := aliasedChildCopyOnWriteForms
    requiredExecutedLcnfForms := aliasedChildCopyOnWriteForms
    requiredExternals := #[``ByteArray.set!]
    requiredExecutedExternals := #[``ByteArray.set!]
    provenance := firProvenance
      "Replace one alias, then retain and mutate the surviving child to test nested copy-on-write" },
  { id := "tuple-rotate"
    entry := ``Source.tupleRotate
    args := #[.ctor "Prod.mk" 0 #[.nat 1, .ctor "Prod.mk" 0 #[.nat 2, .nat 3]]]
    argSchemas := #[.ctor "Prod.mk" 0 #[.nat, .ctor "Prod.mk" 0 #[.nat, .nat]]]
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .ctor "Prod.mk" 0 #[.nat, .nat]]
    native := fun _ =>
      let result := Source.tupleRotate (1, 2, 3)
      .ctor "Prod.mk" 0 #[.nat result.1, .ctor "Prod.mk" 0 #[.nat result.2.1, .nat result.2.2]]
    tags := #["quick", "constructor", "projection", "allocation"]
    requiredLcnfForms := #["oproj", "ctor", "return"]
    requiredExecutedLcnfForms := #["oproj", "isShared", "cases", "oset", "jump", "return"]
    provenance := leanCompileProvenance "tests/compile/tuple.lean"
      "Tuple projection/allocation without IO" },
  { id := "usize-roundtrip"
    entry := ``Source.idUSize
    args := #[.usize 42]
    argSchemas := #[.usize]
    resultSchema := .usize
    native := fun _ => .usize (UInt64.ofNat (Source.idUSize 42).toNat)
    tags := #["quick", "usize", "roundtrip"]
    requiredLcnfForms := #["return"]
    requiredExecutedLcnfForms := #["return"]
    provenance := firProvenance "Portable USize fixture below the Wasm32 boundary" },
  { id := "reuse-assoc"
    entry := ``Source.Assoc.reassoc
    args := #[assocDatum assocInput]
    argSchemas := #[assocSchema assocInput]
    resultSchema := assocSchema assocExpected
    native := fun _ => assocDatum (Source.Assoc.reassoc assocInput)
    tags := #["stress", "ownership", "reuse", "recursion", "constructor"]
    fuel := 100000
    requiredLcnfForms :=
      #["cases", "oproj", "inc", "join", "fap", "oset", "jump", "ctor", "isShared",
        "dec", "return"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "inc", "join", "isShared", "dec", "jump", "oset", "fap",
        "return"]
    provenance := leanCompileProvenance "tests/compile/reusebug.lean"
      "Pure terminating reassociation adapted to execute the ownership/reuse path" },
  { id := "reuse-change-tag"
    entry := ``Source.changeOrGrow
    dependencies := #[``Source.holdNat]
    args := #[.bool true, .ctor "GrowSwitch.left" 0 #[.nat 7]]
    argSchemas := #[.bool, .ctor "GrowSwitch.left" 0 #[.nat]]
    resultSchema := .ctor "GrowSwitch.right" 1 #[.nat]
    native := fun _ => growSwitchDatum (Source.changeOrGrow true (.left 7))
    tags := #["stress", "ownership", "reuse", "constructor", "set-tag", "boundary"]
    requiredLcnfForms :=
      #["cases", "oproj", "join", "fap", "dec", "del", "inc", "ctor", "return",
        "setTag", "oset", "jump", "isShared"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "join", "isShared", "jump", "fap", "inc", "return", "dec",
        "setTag", "oset"]
    provenance := firProvenance
      "Reuse a unique constructor at the same size while changing its runtime tag" },
  { id := "reuse-grow-delete"
    entry := ``Source.changeOrGrow
    dependencies := #[``Source.holdNat]
    args := #[.bool false, .ctor "GrowSwitch.left" 0 #[.nat 7]]
    argSchemas := #[.bool, .ctor "GrowSwitch.left" 0 #[.nat]]
    resultSchema := .ctor "GrowSwitch.big" 2 #[.nat, .nat]
    native := fun _ => growSwitchDatum (Source.changeOrGrow false (.left 7))
    tags := #["stress", "ownership", "reuse", "constructor", "delete", "boundary"]
    requiredLcnfForms :=
      #["cases", "oproj", "join", "fap", "dec", "del", "inc", "ctor", "return",
        "setTag", "oset", "jump", "isShared"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "join", "isShared", "jump", "fap", "inc", "return", "dec",
        "del", "ctor"]
    provenance := firProvenance
      "Delete a unique constructor before allocating a larger replacement" },
  { id := "reuse-grow-delete-shared"
    entry := ``Source.changeOrGrowShared
    dependencies := #[``Source.changeOrGrow, ``Source.holdNat]
    args := #[.bool false, .ctor "GrowSwitch.left" 0 #[.nat 7]]
    argSchemas := #[.bool, .ctor "GrowSwitch.left" 0 #[.nat]]
    resultSchema := .ctor "Prod.mk" 0 #[
      .ctor "GrowSwitch.left" 0 #[.nat],
      .ctor "GrowSwitch.big" 2 #[.nat, .nat]]
    native := fun _ => growSwitchPairDatum
      (Source.changeOrGrowShared false (.left 7))
    tags := #["stress", "ownership", "reuse", "constructor", "delete", "shared"]
    requiredLcnfForms :=
      #["inc", "fap", "cases", "join", "isShared", "jump", "del", "ctor", "return"]
    requiredExecutedLcnfForms :=
      #["inc", "fap", "cases", "join", "isShared", "jump", "del", "ctor", "return"]
    provenance := firProvenance
      "Retain the original constructor while growing a shared replacement" },
  { id := "capture-17-list"
    entry := ``Source.capture17List
    dependencies := #[``Source.applyCaptureList]
    args := #[
      .nat 1, .nat 2, .nat 3, .nat 4, .nat 5, .nat 6, .nat 7, .nat 8, .nat 9,
      .nat 10, .nat 11, .nat 12, .nat 13, .nat 14, .nat 15, .nat 16, .nat 17,
      .nat 18]
    argSchemas := #[
      .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat,
      .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat, .nat]
    resultSchema := .seq .nat
    native := fun _ => natListDatum
      (Source.capture17List 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18)
    tags := #["stress", "closure", "capture", "boundary", "constructor"]
    requiredLcnfForms := #["pap", "fap", "fvar", "ctor", "return"]
    requiredExecutedLcnfForms := #["pap", "fap", "fvar", "ctor", "return"]
    provenance := leanCompileProvenance "tests/compile/closure_bug1.lean"
      "Pure list-valued adaptation retaining 17 captured values" },
  { id := "big-ctor-70"
    entry := ``Source.bigCtorField
    dependencies := #[``Source.mkBigCtor]
    args := #[.nat 70]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.bigCtorField 70)
    tags := #["stress", "constructor", "large-object", "boundary", "projection"]
    requiredLcnfForms := #["fap", "oproj", "inc", "dec", "lit", "ctor", "return"]
    requiredExecutedLcnfForms := #["fap", "oproj", "inc", "dec", "lit", "ctor", "return"]
    provenance := leanCompileProvenance "tests/compile/bigctor.lean"
      "70-object-field constructor preserving the original stress size" },
  { id := "scalar-enum-cases"
    entry := ``Source.scalarCasesInternal
    dependencies := #[``Source.selectScalarChoice]
    resultSchema := .nat
    native := fun _ => .nat Source.scalarCasesInternal
    tags := #["quick", "scalar", "control-flow", "enum", "regression"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "cases"]
    requiredExecutedLcnfForms := #["fap", "lit", "cases", "return", "inc"]
    provenance := firProvenance "Nullary enum lowered to UInt8 and matched internally" },
  { id := "int-positive-roundtrip"
    entry := ``Source.idInt
    args := #[.int 42]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt 42)
    tags := #["quick", "int", "signed", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Positive immediate Int ABI round-trip" },
  { id := "int-negative-roundtrip"
    entry := ``Source.idInt
    args := #[.int (-42)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt (-42))
    tags := #["quick", "int", "signed", "negative", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Negative immediate Int ABI round-trip" },
  { id := "int-immediate-max"
    entry := ``Source.idInt
    args := #[.int 2147483647]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt 2147483647)
    tags := #["stress", "int", "signed", "boundary", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Largest Lean immediate Int payload" },
  { id := "int-immediate-min"
    entry := ``Source.idInt
    args := #[.int (-2147483648)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt (-2147483648))
    tags := #["stress", "int", "signed", "negative", "boundary", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Smallest Lean immediate Int payload" },
  { id := "int-heap-positive-boundary"
    entry := ``Source.idInt
    args := #[.int 2147483648]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt 2147483648)
    tags := #["stress", "int", "signed", "boundary", "heap", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "First positive Int requiring a heap object" },
  { id := "int-heap-negative-boundary"
    entry := ``Source.idInt
    args := #[.int (-2147483649)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ => .int (Source.idInt (-2147483649))
    tags := #["stress", "int", "signed", "negative", "boundary", "heap", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "First negative Int requiring a heap object" },
  { id := "int-literal-immediate-positive"
    entry := ``Source.intPosImmediate
    resultSchema := .int
    native := fun _ => .int Source.intPosImmediate
    tags := #["stress", "int", "signed", "literal", "external", "boundary"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "inc"]
    requiredExternals := #[``Int.ofNat]
    requiredExecutedExternals := #[``Int.ofNat]
    provenance := firProvenance "Compiler-built largest positive immediate Int" },
  { id := "int-literal-heap-positive"
    entry := ``Source.intPosHeap
    resultSchema := .int
    native := fun _ => .int Source.intPosHeap
    tags := #["stress", "int", "signed", "literal", "external", "boundary", "heap"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "inc"]
    requiredExternals := #[``Int.ofNat]
    requiredExecutedExternals := #[``Int.ofNat]
    provenance := firProvenance "Compiler-built first positive heap Int" },
  { id := "int-literal-immediate-negative"
    entry := ``Source.intNegImmediate
    resultSchema := .int
    native := fun _ => .int Source.intNegImmediate
    tags := #["stress", "int", "signed", "negative", "literal", "external", "boundary"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "inc"]
    requiredExternals := #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.neg]
    provenance := firProvenance "Compiler-built smallest negative immediate Int" },
  { id := "int-literal-heap-negative"
    entry := ``Source.intNegHeap
    resultSchema := .int
    native := fun _ => .int Source.intNegHeap
    tags := #["stress", "int", "signed", "negative", "literal", "external", "boundary", "heap"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "inc"]
    requiredExternals := #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.neg]
    provenance := firProvenance "Compiler-built first negative heap Int" },
  { id := "int-classify-immediate-positive"
    entry := ``Source.classifyInt
    args := #[.int 2147483647]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ => .nat (Source.classifyInt 2147483647)
    tags := #["stress", "int", "signed", "cases", "external", "boundary"]
    requiredLcnfForms := #["fap", "cases", "lit", "return", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "cases"]
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify the largest positive immediate Int" },
  { id := "int-classify-heap-positive"
    entry := ``Source.classifyInt
    args := #[.int 2147483648]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ => .nat (Source.classifyInt 2147483648)
    tags := #["stress", "int", "signed", "cases", "external", "boundary", "heap"]
    requiredLcnfForms := #["fap", "cases", "lit", "return", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "cases"]
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify the first positive heap Int" },
  { id := "int-classify-immediate-negative"
    entry := ``Source.classifyInt
    args := #[.int (-2147483648)]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ => .nat (Source.classifyInt (-2147483648))
    tags := #["stress", "int", "signed", "negative", "cases", "external", "boundary"]
    requiredLcnfForms := #["fap", "cases", "lit", "return", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "cases"]
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify the smallest negative immediate Int" },
  { id := "int-classify-heap-negative"
    entry := ``Source.classifyInt
    args := #[.int (-2147483649)]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ => .nat (Source.classifyInt (-2147483649))
    tags := #["stress", "int", "signed", "negative", "cases", "external", "boundary", "heap"]
    requiredLcnfForms := #["fap", "cases", "lit", "return", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "cases"]
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify the first negative heap Int" },
  { id := "nat-add-small"
    entry := ``Source.addNat
    args := #[.nat 20, .nat 22]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.addNat 20 22)
    tags := #["quick", "external", "pure", "nat", "arithmetic"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``Nat.add]
    requiredExecutedExternals := #[``Nat.add]
    provenance := firProvenance "Controlled Nat.add external on tagged operands" },
  { id := "nat-add-tagged-to-heap"
    entry := ``Source.addNat
    args := #[.nat 9223372036854775807, .nat 1]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.addNat 9223372036854775807 1)
    tags := #["stress", "external", "pure", "nat", "arithmetic", "boundary", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``Nat.add]
    requiredExecutedExternals := #[``Nat.add]
    provenance := firProvenance "Nat.add crossing the tagged-to-heap result boundary" },
  { id := "nat-add-heap-input"
    entry := ``Source.addNat
    args := #[.nat Source.largeNat, .nat 7]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.addNat Source.largeNat 7)
    tags := #["stress", "external", "pure", "nat", "arithmetic", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``Nat.add]
    requiredExecutedExternals := #[``Nat.add]
    provenance := firProvenance "Nat.add decoding and returning heap natural values" },
  { id := "effect-record-nat"
    entry := ``Source.recordOnce
    args := #[.nat 7]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recordOnce 7)
    nativeBefore := NativeEffects.reset
    nativeEffects := fun _ => NativeEffects.take
    tags := #["quick", "effect", "external", "nat"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``NativeEffects.recordImpl]
    requiredExecutedExternals := #[``NativeEffects.recordImpl]
    effectProjections := #[{
      external := ``NativeEffects.recordImpl
      operation := "validation.record"
      argSchemas := #[.nat]
      resultSchema := some .nat }]
    provenance := firProvenance
      "Native-recorded effect projected from the matching final-impure external" },
  { id := "effect-record-twice"
    entry := ``Source.recordTwice
    args := #[.nat 7]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recordTwice 7)
    nativeBefore := NativeEffects.reset
    nativeEffects := fun _ => NativeEffects.take
    tags := #["quick", "effect", "external", "nat", "sequence"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``NativeEffects.recordImpl]
    requiredExecutedExternals := #[``NativeEffects.recordImpl]
    effectProjections := #[{
      external := ``NativeEffects.recordImpl
      operation := "validation.record"
      argSchemas := #[.nat]
      resultSchema := some .nat }]
    provenance := firProvenance
      "Preserve the count and order of two native-recorded external effects" },
  { id := "effect-record-byte-array-twice"
    entry := ``Source.recordByteArrayTwice
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .bytes
    native := fun _ => byteArrayDatum
      (Source.recordByteArrayTwice ⟨#[0, 127, 128, 255]⟩)
    nativeBefore := NativeEffects.reset
    nativeEffects := fun _ => NativeEffects.take
    tags :=
      #["stress", "effect", "external", "bytes", "heap", "mutation", "snapshot", "sequence"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExternals := #[``NativeEffects.recordByteArrayImpl]
    requiredExecutedExternals := #[``NativeEffects.recordByteArrayImpl]
    effectProjections := #[{
      external := ``NativeEffects.recordByteArrayImpl
      operation := "validation.recordByteArray"
      argSchemas := #[.bytes, .bits 8]
      resultSchema := some .bytes }]
    provenance := firProvenance
      "Preserve two mutable heap arguments and results at their external event-time states" },
  { id := "byte-array-roundtrip"
    entry := ``Source.idByteArray
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .bytes
    native := fun _ => byteArrayDatum
      (Source.idByteArray ⟨#[0, 127, 128, 255]⟩)
    tags := #["quick", "bytes", "packed-layout", "roundtrip", "boundary"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance "Runner-supplied packed ByteArray ABI round-trip" },
  { id := "byte-array-size"
    entry := ``Source.byteArraySize
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .nat
    native := fun _ => .nat (Source.byteArraySize ⟨#[0, 127, 128, 255]⟩)
    tags := #["quick", "bytes", "packed-layout", "external", "pure", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.size]
    requiredExecutedExternals := #[``ByteArray.size]
    provenance := firProvenance "Controlled ByteArray.size external on packed boundary bytes" },
  { id := "byte-array-get-zero"
    entry := ``Source.byteArrayGet
    args := #[.bytes #[0, 127, 128, 255], .nat 0]
    argSchemas := #[.bytes, .nat]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat (Source.byteArrayGet ⟨#[0, 127, 128, 255]⟩ 0).toNat)
    tags := #["quick", "bytes", "packed-layout", "external", "pure", "index", "scalar"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    provenance := firProvenance "Read a zero byte through ByteArray.get!" },
  { id := "byte-array-get-high-bit"
    entry := ``Source.byteArrayGet
    args := #[.bytes #[0, 127, 128, 255], .nat 2]
    argSchemas := #[.bytes, .nat]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat (Source.byteArrayGet ⟨#[0, 127, 128, 255]⟩ 2).toNat)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "pure", "index", "scalar", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    provenance := firProvenance "Read the first high-bit byte through ByteArray.get!" },
  { id := "byte-array-get-max"
    entry := ``Source.byteArrayGet
    args := #[.bytes #[0, 127, 128, 255], .nat 3]
    argSchemas := #[.bytes, .nat]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat (Source.byteArrayGet ⟨#[0, 127, 128, 255]⟩ 3).toNat)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "pure", "index", "scalar", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    provenance := firProvenance "Read the maximum byte through ByteArray.get!" },
  { id := "byte-array-get-empty"
    entry := ``Source.byteArrayGet
    args := #[.bytes #[], .nat 0]
    argSchemas := #[.bytes, .nat]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat (Source.byteArrayGet (⟨#[]⟩ : ByteArray) 0).toNat)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "pure", "index", "scalar",
        "boundary", "out-of-bounds", "default"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    provenance := firProvenance
      "Read the default byte at index zero from an empty ByteArray through ByteArray.get!" },
  { id := "byte-array-get-end"
    entry := ``Source.byteArrayGet
    args := #[.bytes #[0, 127, 128, 255], .nat 4]
    argSchemas := #[.bytes, .nat]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat (Source.byteArrayGet ⟨#[0, 127, 128, 255]⟩ 4).toNat)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "pure", "index", "scalar",
        "boundary", "out-of-bounds", "default"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    provenance := firProvenance
      "Read the default byte at the exact end boundary through ByteArray.get!" },
  { id := "byte-array-get-heap-oob"
    entry := ``Source.byteArrayGet
    args := #[.bytes #[0, 127, 128, 255], .nat Source.largeNat]
    argSchemas := #[.bytes, .nat]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8
        (UInt64.ofNat
          (Source.byteArrayGet ⟨#[0, 127, 128, 255]⟩ Source.largeNat).toNat)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "pure", "index", "scalar",
        "boundary", "out-of-bounds", "default", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    provenance := firProvenance
      "Read the default byte at a heap-natural index through ByteArray.get!" },
  { id := "byte-array-set-unique"
    entry := ``Source.byteArraySetUnique
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .bytes
    native := fun _ => byteArrayDatum
      (Source.byteArraySetUnique ⟨#[0, 127, 128, 255]⟩)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "mutation", "ownership", "unique"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExternals := #[``ByteArray.set!]
    requiredExecutedExternals := #[``ByteArray.set!]
    provenance := firProvenance
      "Mutate a uniquely owned byte array in place through ByteArray.set!" },
  { id := "byte-array-set-shared"
    entry := ``Source.byteArraySetShared
    args := #[.bytes #[0, 127, 128, 255]]
    argSchemas := #[.bytes]
    resultSchema := .ctor "Prod.mk" 0 #[.bytes, .bytes]
    native := fun _ => byteArrayPairDatum
      (Source.byteArraySetShared ⟨#[0, 127, 128, 255]⟩)
    tags :=
      #["stress", "bytes", "packed-layout", "external", "mutation", "ownership", "shared",
        "copy-on-write"]
    requiredLcnfForms := #["lit", "inc", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfForms := #["lit", "inc", "fap", "extern", "ctor", "return"]
    requiredExternals := #[``ByteArray.set!]
    requiredExecutedExternals := #[``ByteArray.set!]
    provenance := firProvenance
      "Copy a shared byte array while preserving its original alias through ByteArray.set!" }
]

/-- Source-reachable final-impure forms whose execution coverage the corpus must preserve. -/
def requiredFinalExecutedForms : Array String :=
  #["box", "cases", "ctor", "dec", "del", "extern", "fap", "fvar", "inc", "isShared",
    "join", "jump", "lit", "oproj", "oset", "pap", "return", "setTag", "sproj", "sset",
    "unbox", "uproj", "uset"]

#guard cases.all fun validationCase => !validationCase.requiredExecutedLcnfForms.isEmpty

#guard cases.all fun validationCase =>
  validationCase.effectProjections.all fun projection =>
    validationCase.requiredExternals.contains projection.external &&
    validationCase.requiredExecutedExternals.contains projection.external

#guard requiredFinalExecutedForms.all fun form =>
  cases.any fun validationCase => validationCase.requiredExecutedLcnfForms.contains form

def findCase? (id : String) : Option Case :=
  cases.find? (·.id == id)

def caseIds : Array String :=
  cases.map (·.id)

def descriptors : Array CaseDescriptor :=
  cases.map Case.descriptor

end Fir.Validation.Corpus
