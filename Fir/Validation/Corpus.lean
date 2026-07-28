import Fir.Validation.Protocol
import Init.Data.Ord.String

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

@[noinline]
def stringLength (value : String) : Nat :=
  String.Internal.length value

@[noinline]
def stringUtf8ByteSize (value : String) : Nat :=
  value.utf8ByteSize

@[noinline]
def stringPosOfNonBmp (value : String) : Nat :=
  (String.Internal.posOf value '😀').byteIdx

@[noinline]
def stringOffsetOfPos (value : String) (position : Nat) : Nat :=
  String.Internal.offsetOfPos value ⟨position⟩

@[noinline]
def stringNext (value : String) (position : Nat) : Nat :=
  (String.Internal.next value ⟨position⟩).byteIdx

@[noinline]
def stringExtract (value : String) (beginPos endPos : Nat) : String :=
  String.Internal.extract value ⟨beginPos⟩ ⟨endPos⟩

@[noinline]
def stringAppend (left right : String) : String :=
  String.Internal.append left right

@[noinline]
def stringAppendShared (left right : String) : String × String :=
  let result := String.Internal.append left right
  (left, result)

@[noinline]
def stringAppendSelfShared (value : String) : String × String :=
  let result := String.Internal.append value value
  (value, result)

@[noinline]
def stringPushnNonBmp (source : String) (count : Nat) : String :=
  String.Internal.pushn source '😀' count

@[noinline]
def stringPushnNonBmpShared (source : String) (count : Nat) : String × String :=
  let result := String.Internal.pushn source '😀' count
  (source, result)

@[noinline]
def stringDecEq (left right : String) : Bool :=
  decide (left = right)

@[noinline]
def stringDecLt (left right : String) : Bool :=
  decide (left < right)

@[noinline]
def stringCompareClassify (left right : String) : Nat :=
  match String.compare left right with
  | .lt => 0
  | .eq => 1
  | .gt => 2

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
def mkByteArrayPairLayout (first second : ByteArray) (usize : USize)
    (scalar : UInt32) : AliasedByteArrayLayout :=
  { first, second, usize, scalar }

@[noinline]
def AliasedByteArrayLayout.setFirst (value : AliasedByteArrayLayout)
    (replacement : ByteArray) : AliasedByteArrayLayout :=
  { value with first := replacement }

@[noinline]
def AliasedByteArrayLayout.setSecond (value : AliasedByteArrayLayout)
    (replacement : ByteArray) : AliasedByteArrayLayout :=
  { value with second := replacement }

@[noinline]
def AliasedByteArrayLayout.swap (value : AliasedByteArrayLayout) :
    AliasedByteArrayLayout :=
  { value with first := value.second, second := value.first }

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

def aliasedByteArraySelfReplace (shared : ByteArray) (usize : USize)
    (scalar : UInt32) : ByteArray × ByteArray :=
  let updated := AliasedByteArrayLayout.setFirst
    (mkAliasedByteArrayLayout shared usize scalar) shared
  (updated.first, updated.second)

def aliasedByteArraySharedSelfReplace (shared : ByteArray) (usize : USize)
    (scalar : UInt32) :
    (ByteArray × ByteArray) × (ByteArray × ByteArray) :=
  let original := mkAliasedByteArrayLayout shared usize scalar
  let updated := AliasedByteArrayLayout.setFirst original shared
  ((updated.first, updated.second), (original.first, original.second))

def aliasedByteArraySelfReplaceChildCopyOnWrite (shared : ByteArray)
    (usize : USize) (scalar : UInt32) : ByteArray × ByteArray :=
  let layout := AliasedByteArrayLayout.setFirst
    (mkAliasedByteArrayLayout shared usize scalar) shared
  let original := layout.second
  let updated := layout.first.set! 0 42
  (original, updated)

def byteArrayObjectSwap (first second : ByteArray) (usize : USize)
    (scalar : UInt32) : ByteArray × ByteArray :=
  let swapped := AliasedByteArrayLayout.swap
    (mkByteArrayPairLayout first second usize scalar)
  (swapped.first, swapped.second)

def byteArrayObjectSwapShared (first second : ByteArray) (usize : USize)
    (scalar : UInt32) :
    (ByteArray × ByteArray) × (ByteArray × ByteArray) :=
  let original := mkByteArrayPairLayout first second usize scalar
  let swapped := AliasedByteArrayLayout.swap original
  ((swapped.first, swapped.second), (original.first, original.second))

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
def negateInt (value : Int) : Int :=
  -value

@[noinline]
def intOfNat (value : Nat) : Int :=
  Int.ofNat value

@[noinline]
def negIntOfNat (value : Nat) : Int :=
  -(Int.ofNat value)

@[noinline]
def addInt (left right : Int) : Int :=
  left + right

@[noinline]
def subInt (left right : Int) : Int :=
  left - right

@[noinline]
def mulInt (left right : Int) : Int :=
  left * right

@[noinline]
def divModInt (left right : Int) : Int × Int :=
  (left / right, left % right)

@[noinline]
def decideIntEq (left right : Int) : Bool :=
  decide (left = right)

@[noinline]
def decideIntLt (left right : Int) : Bool :=
  decide (left < right)

@[noinline]
def decideIntLe (left right : Int) : Bool :=
  decide (left ≤ right)

@[noinline]
def natAbsInt (value : Int) : Nat :=
  value.natAbs

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

@[noinline]
def subNat (left right : Nat) : Nat :=
  left - right

@[noinline]
def mulNat (left right : Nat) : Nat :=
  left * right

@[noinline]
def divModNat (left right : Nat) : Nat × Nat :=
  (left / right, left % right)

@[noinline]
def landNat (left right : Nat) : Nat :=
  Nat.land left right

@[noinline]
def lorNat (left right : Nat) : Nat :=
  Nat.lor left right

@[noinline]
def xorNat (left right : Nat) : Nat :=
  Nat.xor left right

@[noinline]
def shiftLeftNat (value count : Nat) : Nat :=
  Nat.shiftLeft value count

@[noinline]
def shiftRightNat (value count : Nat) : Nat :=
  Nat.shiftRight value count

@[noinline]
def decideNatEq (left right : Nat) : Bool :=
  decide (left = right)

@[noinline]
def decideNatLt (left right : Nat) : Bool :=
  decide (left < right)

@[noinline]
def decideNatLe (left right : Nat) : Bool :=
  decide (left ≤ right)

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
def conditionalByteArrayGet (read : Bool) (value : ByteArray) : UInt8 :=
  if read then value.get! 0 else 42

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

/-- Minimum dynamic multiplicity required for one final-impure instruction form. -/
structure ExecutedFormCountRequirement where
  form : String
  minimum : Nat
  maximum : Option Nat := none
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

/-- Minimum dynamic dispatch count required for one imported external. -/
structure ExecutedExternalCountRequirement where
  external : Lean.Name
  minimum : Nat
  maximum : Option Nat := none
  deriving Inhabited, BEq, Repr

/-- Closure-free external-count obligation retained in the corpus manifest. -/
structure ExecutedExternalCountRequirementDescriptor where
  external : String
  minimum : Nat
  maximum : Option Nat
  deriving Inhabited, BEq, Repr, Lean.ToJson, Lean.FromJson

def ExecutedExternalCountRequirement.descriptor
    (requirement : ExecutedExternalCountRequirement) :
    ExecutedExternalCountRequirementDescriptor := {
  external := toString requirement.external
  minimum := requirement.minimum
  maximum := requirement.maximum }

private def exactlyOnceExternalCounts
    (externals : Array Lean.Name) : Array ExecutedExternalCountRequirement :=
  externals.map fun external => { external, minimum := 1, maximum := some 1 }

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
  /-- Minimum dynamic counts for forms whose multiplicity is semantically significant. -/
  requiredExecutedLcnfFormCounts : Array ExecutedFormCountRequirement := #[]
  /-- Exact ordered final-impure form sequence, when this fixture pins one. -/
  requiredExecutedLcnfFormTrace : Option (Array String) := none
  /-- Source-generated administrative interpreter transitions this fixture must execute. -/
  requiredAdministrativeStepKinds : Array String := #[]
  /-- Imported declarations that must remain in the compiled dependency closure. -/
  requiredExternals : Array Lean.Name := #[]
  /-- Imported declarations that this fixture must actually call. -/
  requiredExecutedExternals : Array Lean.Name := #[]
  /-- Minimum dynamic dispatch counts for externals whose multiplicity is significant. -/
  requiredExecutedExternalCounts : Array ExecutedExternalCountRequirement := #[]
  /-- Exact ordered external dispatch sequence, when this fixture pins one. -/
  requiredExecutedExternalTrace : Option (Array Lean.Name) := none
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
  requiredExecutedLcnfFormCounts : Array ExecutedFormCountRequirement
  requiredExecutedLcnfFormTrace : Option (Array String)
  requiredAdministrativeStepKinds : Array String
  requiredExternals : Array String
  requiredExecutedExternals : Array String
  requiredExecutedExternalCounts : Array ExecutedExternalCountRequirementDescriptor
  requiredExecutedExternalTrace : Option (Array String)
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
  requiredExecutedLcnfFormCounts := validationCase.requiredExecutedLcnfFormCounts
  requiredExecutedLcnfFormTrace := validationCase.requiredExecutedLcnfFormTrace
  requiredAdministrativeStepKinds :=
    validationCase.requiredAdministrativeStepKinds
  requiredExternals := validationCase.requiredExternals.map toString
  requiredExecutedExternals := validationCase.requiredExecutedExternals.map toString
  requiredExecutedExternalCounts :=
    validationCase.requiredExecutedExternalCounts.map
      ExecutedExternalCountRequirement.descriptor
  requiredExecutedExternalTrace :=
    validationCase.requiredExecutedExternalTrace.map fun trace =>
      trace.map toString
  effectProjections := validationCase.effectProjections.map EffectProjection.descriptor
  provenance := validationCase.provenance }

private def natListDatum (xs : List Nat) : ValidationDatum :=
  .seq (xs.toArray.map .nat)

private def byteArrayDatum (value : ByteArray) : ValidationDatum :=
  .bytes (value.data.map (UInt8.toNat ·))

private def byteArrayPairDatum (value : ByteArray × ByteArray) : ValidationDatum :=
  .ctor "Prod.mk" 0 #[byteArrayDatum value.1, byteArrayDatum value.2]

private def stringPairDatum (value : String × String) : ValidationDatum :=
  .ctor "Prod.mk" 0 #[.string value.1, .string value.2]

private def natPairDatum (value : Nat × Nat) : ValidationDatum :=
  .ctor "Prod.mk" 0 #[.nat value.1, .nat value.2]

private def intPairDatum (value : Int × Int) : ValidationDatum :=
  .ctor "Prod.mk" 0 #[.int value.1, .int value.2]

private def bmpPrivateUseString : String :=
  String.ofList [Char.ofNat 0xe000]

private def supplementaryPlaneString : String :=
  String.ofList [Char.ofNat 0x10000]

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

private def aliasedByteArraySelfArgs : Array ValidationDatum :=
  #[byteArrayDatum mixedLayoutBytes, .usize (UInt64.ofNat Source.maxUSize.toNat),
    .bits 32 (UInt64.ofNat Source.maxUInt32.toNat)]

private def aliasedByteArraySelfArgSchemas : Array ValidationSchema :=
  #[.bytes, .usize, .bits 32]

private def byteArrayObjectSwapArgs : Array ValidationDatum :=
  #[byteArrayDatum mixedLayoutBytes, byteArrayDatum multiObjectReplacementBytes,
    .usize (UInt64.ofNat Source.maxUSize.toNat),
    .bits 32 (UInt64.ofNat Source.maxUInt32.toNat)]

private def byteArrayObjectSwapArgSchemas : Array ValidationSchema :=
  #[.bytes, .bytes, .usize, .bits 32]

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

private def branchFormTrace : Array String :=
  #["cases", "lit", "return"]

private def recursiveListFormTrace : Array String :=
  #["lit", "fap", "cases", "oproj", "oproj",
    "fap", "cases", "oproj", "oproj",
    "fap", "cases", "oproj", "oproj",
    "fap", "cases", "inc", "return",
    "return", "return", "return", "return"]

private def recursiveEmptyFormTrace : Array String :=
  #["lit", "fap", "cases", "inc", "return", "return"]

private def scalarEnumFormTrace : Array String :=
  #["fap", "lit", "fap", "cases", "lit", "return", "return", "inc", "return"]

private def intClassifyFormTrace : Array String :=
  #["fap", "lit", "fap", "extern", "return",
    "fap", "extern", "cases", "lit", "return"]

private def intOfNatFormTrace : Array String :=
  #["fap", "extern", "return"]

private def externalCallFormTrace : Array String :=
  #["fap", "extern", "return"]

private def exactNatBinaryExternalCase
    (id : String) (entry : Lean.Name) (operation : Nat → Nat → Nat)
    (external : Lean.Name) (left right : Nat) (tags : Array String)
    (note : String) : Case := {
  id
  entry
  args := #[.nat left, .nat right]
  argSchemas := #[.nat, .nat]
  resultSchema := .nat
  native := fun _ => .nat (operation left right)
  tags
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def pairedExternalCallFormTrace : Array String :=
  #["fap", "extern", "fap", "extern", "ctor", "return"]

private def sharedStringAppendFormTrace : Array String :=
  #["inc", "fap", "extern", "ctor", "return"]

private def stringPushnFormTrace : Array String :=
  #["lit", "fap", "extern", "return"]

private def sharedStringPushnFormTrace : Array String :=
  #["lit", "inc", "fap", "extern", "ctor", "return"]

private def stringCompareClassifyFormTrace : Array String :=
  #["fap", "extern", "cases", "lit", "return"]

private def negIntOfNatFormTrace : Array String :=
  #["fap", "extern", "fap", "extern", "dec", "return"]

private def conditionalExternalTakenFormTrace : Array String :=
  #["cases", "lit", "fap", "extern", "return"]

private def reuseChangeTagFormTrace : Array String :=
  #["cases", "oproj", "join", "isShared", "cases", "jump", "fap", "inc", "return",
    "dec", "cases", "join", "cases", "setTag", "oset", "jump", "return"]

private def reuseGrowDeleteFormTrace : Array String :=
  #["cases", "oproj", "join", "isShared", "cases", "jump", "fap", "inc", "return",
    "dec", "cases", "del", "inc", "ctor", "return"]

private def reuseGrowDeleteSharedFormTrace : Array String :=
  #["inc", "fap", "cases", "oproj", "join", "isShared", "cases", "inc", "dec",
    "jump", "fap", "inc", "return", "dec", "cases", "del", "inc", "ctor",
    "return", "ctor", "return"]

def cases : Array Case := #[
  { id := "lit-nat"
    entry := ``Source.litNat
    resultSchema := .nat
    native := fun _ => .nat Source.litNat
    tags := #["quick", "literal"]
    requiredLcnfForms := #["lit", "return"]
    requiredExecutedLcnfForms := #["lit", "return"]
    requiredAdministrativeStepKinds :=
      #["admin:invoke-name", "admin:yield-cache", "admin:yield-done"] },
  { id := "id-nat"
    entry := ``Source.idNat
    args := #[.nat 42]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.idNat 42)
    tags := #["quick", "borrowed"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"] },
  { id := "nat-immediate-max-roundtrip"
    entry := ``Source.idNat
    args := #[.nat 9223372036854775807]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.idNat 9223372036854775807)
    tags := #["stress", "nat", "roundtrip", "boundary", "immediate"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip the maximum tagged immediate natural without an external" },
  { id := "nat-heap-boundary-roundtrip"
    entry := ``Source.idNat
    args := #[.nat 9223372036854775808]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.idNat 9223372036854775808)
    tags := #["stress", "nat", "roundtrip", "boundary", "heap"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip the first heap natural without an external" },
  { id := "nat-multi-limb-roundtrip"
    entry := ``Source.idNat
    args := #[.nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat]
    resultSchema := .nat
    native := fun _ =>
      .nat (Source.idNat 340282366920938463463374607431768211473)
    tags := #["stress", "nat", "roundtrip", "boundary", "heap", "multi-limb"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip 2^128 + 17 to exercise a multi-limb natural without an external" },
  { id := "branch-nat"
    entry := ``Source.branchNat
    args := #[.bool true]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat true)
    tags := #["quick", "control-flow"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfFormTrace := some branchFormTrace },
  { id := "branch-nat-false"
    entry := ``Source.branchNat
    args := #[.bool false]
    argSchemas := #[.bool]
    resultSchema := .nat
    native := fun _ => .nat (Source.branchNat false)
    tags := #["quick", "control-flow", "boundary"]
    requiredLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfFormTrace := some branchFormTrace },
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
    requiredExecutedLcnfForms := #["fap", "return"]
    requiredAdministrativeStepKinds := #["admin:yield-bind"] },
  { id := "captured-partial"
    entry := ``Source.capturedPartial
    dependencies := #[``Source.firstNat, ``Source.applyNat]
    args := #[.nat 40, .nat 2]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.capturedPartial 40 2)
    tags := #["quick", "closure", "partial-application"]
    requiredLcnfForms := #["pap", "fap", "return"]
    requiredExecutedLcnfForms := #["pap", "fap", "return"]
    requiredAdministrativeStepKinds := #["admin:invoke-value"] },
  { id := "recursive-traversal"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum [10, 20, 12]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [10, 20, 12])
    tags := #["quick", "constructor", "recursion", "multiplicity"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "cases", minimum := 4, maximum := some 4 },
        { form := "fap", minimum := 4, maximum := some 4 },
        { form := "oproj", minimum := 6, maximum := some 6 }]
    requiredExecutedLcnfFormTrace := some recursiveListFormTrace },
  { id := "recursive-empty"
    entry := ``Source.recursiveTraversal
    dependencies := #[``Source.lastOr]
    args := #[natListDatum []]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.recursiveTraversal [])
    tags := #["quick", "constructor", "recursion", "boundary", "path-exclusion"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "inc", "fap", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "cases", minimum := 1, maximum := some 1 },
        { form := "fap", minimum := 1, maximum := some 1 },
        { form := "oproj", minimum := 0, maximum := some 0 }]
    requiredExecutedLcnfFormTrace := some recursiveEmptyFormTrace },
  { id := "local-tail"
    entry := ``Source.localTailControl
    dependencies := #[`Fir.Validation.Corpus.Source.localTailControl.loop]
    args := #[natListDatum [10, 20, 42]]
    argSchemas := #[.seq .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.localTailControl [10, 20, 42])
    tags := #["quick", "tail-control", "multiplicity"]
    requiredLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfForms := #["cases", "oproj", "inc", "fap", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "cases", minimum := 4, maximum := some 4 },
        { form := "fap", minimum := 4, maximum := some 4 },
        { form := "oproj", minimum := 6, maximum := some 6 }]
    requiredExecutedLcnfFormTrace := some recursiveListFormTrace },
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
    requiredExecutedLcnfFormTrace := some branchFormTrace
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
    requiredExecutedLcnfFormTrace := some branchFormTrace
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
    requiredExecutedLcnfFormTrace := some branchFormTrace
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
  { id := "empty-string-roundtrip"
    entry := ``Source.idString
    args := #[.string ""]
    argSchemas := #[.string]
    resultSchema := .string
    native := fun _ => .string (Source.idString "")
    tags := #["stress", "string", "empty", "roundtrip", "boundary"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip the empty String heap representation without an external" },
  { id := "nul-nonbmp-string-roundtrip"
    entry := ``Source.idString
    args := #[.string "\u0000é😀"]
    argSchemas := #[.string]
    resultSchema := .string
    native := fun _ => .string (Source.idString "\u0000é😀")
    tags := #["stress", "string", "unicode", "nul", "non-bmp", "roundtrip",
      "boundary"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip embedded NUL and non-BMP UTF-8 without an external" },
  { id := "string-length-empty"
    entry := ``Source.stringLength
    args := #[.string ""]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringLength "")
    tags := #["stress", "string", "unicode", "measurement", "length", "empty",
      "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.length]
    requiredExecutedExternals := #[``String.Internal.length]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.length]
    requiredExecutedExternalTrace := some #[``String.Internal.length]
    provenance := firProvenance
      "Measure zero Unicode scalar values in the empty String heap object" },
  { id := "string-length-ascii"
    entry := ``Source.stringLength
    args := #[.string "Lean"]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringLength "Lean")
    tags := #["stress", "string", "unicode", "measurement", "length", "ascii",
      "external"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.length]
    requiredExecutedExternals := #[``String.Internal.length]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.length]
    requiredExecutedExternalTrace := some #[``String.Internal.length]
    provenance := firProvenance
      "Measure ASCII String character length through exact external dispatch" },
  { id := "string-length-nul-bmp-nonbmp"
    entry := ``Source.stringLength
    args := #[.string "\u0000é😀"]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringLength "\u0000é😀")
    tags := #["stress", "string", "unicode", "measurement", "length", "nul",
      "bmp", "non-bmp", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.length]
    requiredExecutedExternals := #[``String.Internal.length]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.length]
    requiredExecutedExternalTrace := some #[``String.Internal.length]
    provenance := firProvenance
      "Count embedded NUL, BMP, and non-BMP characters as three scalar values" },
  { id := "string-utf8-byte-size-empty"
    entry := ``Source.stringUtf8ByteSize
    args := #[.string ""]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringUtf8ByteSize "")
    tags := #["stress", "string", "unicode", "measurement", "utf8", "bytes",
      "empty", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.utf8ByteSize]
    requiredExecutedExternals := #[``String.utf8ByteSize]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.utf8ByteSize]
    requiredExecutedExternalTrace := some #[``String.utf8ByteSize]
    provenance := firProvenance
      "Measure zero UTF-8 bytes in the empty String heap object" },
  { id := "string-utf8-byte-size-ascii"
    entry := ``Source.stringUtf8ByteSize
    args := #[.string "Lean"]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringUtf8ByteSize "Lean")
    tags := #["stress", "string", "unicode", "measurement", "utf8", "bytes",
      "ascii", "external"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.utf8ByteSize]
    requiredExecutedExternals := #[``String.utf8ByteSize]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.utf8ByteSize]
    requiredExecutedExternalTrace := some #[``String.utf8ByteSize]
    provenance := firProvenance
      "Measure one UTF-8 byte per ASCII character through exact dispatch" },
  { id := "string-utf8-byte-size-nul-bmp-nonbmp"
    entry := ``Source.stringUtf8ByteSize
    args := #[.string "\u0000é😀"]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringUtf8ByteSize "\u0000é😀")
    tags := #["stress", "string", "unicode", "measurement", "utf8", "bytes",
      "nul", "bmp", "non-bmp", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.utf8ByteSize]
    requiredExecutedExternals := #[``String.utf8ByteSize]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.utf8ByteSize]
    requiredExecutedExternalTrace := some #[``String.utf8ByteSize]
    provenance := firProvenance
      "Measure NUL, BMP, and non-BMP UTF-8 widths as one, two, and four bytes" },
  { id := "string-pos-of-nonbmp-found"
    entry := ``Source.stringPosOfNonBmp
    args := #[.string "Aé😀Z"]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringPosOfNonBmp "Aé😀Z")
    tags := #["stress", "string", "unicode", "navigation", "search", "non-bmp",
      "found", "byte-position", "external", "boundary"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some #["lit", "fap", "extern", "return"]
    requiredExternals := #[``String.Internal.posOf]
    requiredExecutedExternals := #[``String.Internal.posOf]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.posOf]
    requiredExecutedExternalTrace := some #[``String.Internal.posOf]
    provenance := firProvenance
      "Find a non-BMP scalar at its raw UTF-8 byte position" },
  { id := "string-pos-of-nonbmp-missing"
    entry := ``Source.stringPosOfNonBmp
    args := #[.string "AéZ"]
    argSchemas := #[.string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringPosOfNonBmp "AéZ")
    tags := #["stress", "string", "unicode", "navigation", "search", "non-bmp",
      "missing", "end-position", "external", "boundary"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some #["lit", "fap", "extern", "return"]
    requiredExternals := #[``String.Internal.posOf]
    requiredExecutedExternals := #[``String.Internal.posOf]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.posOf]
    requiredExecutedExternalTrace := some #[``String.Internal.posOf]
    provenance := firProvenance
      "Return the UTF-8 end position when a non-BMP scalar is absent" },
  { id := "string-offset-of-pos-scalar-boundary"
    entry := ``Source.stringOffsetOfPos
    args := #[.string "Aé😀Z", .nat 3]
    argSchemas := #[.string, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringOffsetOfPos "Aé😀Z" 3)
    tags := #["stress", "string", "unicode", "navigation", "offset",
      "scalar-boundary", "byte-position", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.offsetOfPos]
    requiredExecutedExternals := #[``String.Internal.offsetOfPos]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.offsetOfPos]
    requiredExecutedExternalTrace := some #[``String.Internal.offsetOfPos]
    provenance := firProvenance
      "Convert the non-BMP scalar's exact UTF-8 boundary to character offset" },
  { id := "string-offset-of-pos-inside-nonbmp"
    entry := ``Source.stringOffsetOfPos
    args := #[.string "Aé😀Z", .nat 4]
    argSchemas := #[.string, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringOffsetOfPos "Aé😀Z" 4)
    tags := #["stress", "string", "unicode", "navigation", "offset", "non-bmp",
      "continuation-byte", "round-forward", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.offsetOfPos]
    requiredExecutedExternals := #[``String.Internal.offsetOfPos]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.offsetOfPos]
    requiredExecutedExternalTrace := some #[``String.Internal.offsetOfPos]
    provenance := firProvenance
      "Round a position inside a four-byte scalar to the following offset" },
  { id := "string-offset-of-pos-past-end"
    entry := ``Source.stringOffsetOfPos
    args := #[.string "Aé😀Z", .nat 50]
    argSchemas := #[.string, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringOffsetOfPos "Aé😀Z" 50)
    tags := #["stress", "string", "unicode", "navigation", "offset", "past-end",
      "character-length", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.offsetOfPos]
    requiredExecutedExternals := #[``String.Internal.offsetOfPos]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.offsetOfPos]
    requiredExecutedExternalTrace := some #[``String.Internal.offsetOfPos]
    provenance := firProvenance
      "Clamp a far past-end byte position to the String character length" },
  { id := "string-next-nonbmp-leader"
    entry := ``Source.stringNext
    args := #[.string "Aé😀Z", .nat 3]
    argSchemas := #[.string, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringNext "Aé😀Z" 3)
    tags := #["stress", "string", "unicode", "navigation", "next", "non-bmp",
      "leading-byte", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.next]
    requiredExecutedExternals := #[``String.Internal.next]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.next]
    requiredExecutedExternalTrace := some #[``String.Internal.next]
    provenance := firProvenance
      "Advance over all four UTF-8 bytes from a non-BMP leading byte" },
  { id := "string-next-continuation-byte"
    entry := ``Source.stringNext
    args := #[.string "Aé😀Z", .nat 4]
    argSchemas := #[.string, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringNext "Aé😀Z" 4)
    tags := #["stress", "string", "unicode", "navigation", "next", "non-bmp",
      "continuation-byte", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.next]
    requiredExecutedExternals := #[``String.Internal.next]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.next]
    requiredExecutedExternalTrace := some #[``String.Internal.next]
    provenance := firProvenance
      "Advance exactly one byte from inside a non-BMP UTF-8 scalar" },
  { id := "string-next-end"
    entry := ``Source.stringNext
    args := #[.string "Aé😀Z", .nat 8]
    argSchemas := #[.string, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringNext "Aé😀Z" 8)
    tags := #["stress", "string", "unicode", "navigation", "next", "end",
      "past-end", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.next]
    requiredExecutedExternals := #[``String.Internal.next]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.next]
    requiredExecutedExternalTrace := some #[``String.Internal.next]
    provenance := firProvenance
      "Advance one byte beyond the exact UTF-8 end position" },
  { id := "string-extract-full"
    entry := ``Source.stringExtract
    args := #[.string "Aé😀Z", .nat 0, .nat 8]
    argSchemas := #[.string, .nat, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringExtract "Aé😀Z" 0 8)
    tags := #["stress", "string", "unicode", "extract", "allocation", "full",
      "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.extract]
    requiredExecutedExternals := #[``String.Internal.extract]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.extract]
    requiredExecutedExternalTrace := some #[``String.Internal.extract]
    provenance := firProvenance
      "Allocate the complete String from exact start and end byte positions" },
  { id := "string-extract-nonbmp"
    entry := ``Source.stringExtract
    args := #[.string "Aé😀Z", .nat 3, .nat 7]
    argSchemas := #[.string, .nat, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringExtract "Aé😀Z" 3 7)
    tags := #["stress", "string", "unicode", "extract", "allocation", "non-bmp",
      "scalar-boundary", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.extract]
    requiredExecutedExternals := #[``String.Internal.extract]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.extract]
    requiredExecutedExternalTrace := some #[``String.Internal.extract]
    provenance := firProvenance
      "Extract exactly one non-BMP scalar across its four UTF-8 bytes" },
  { id := "string-extract-invalid-begin"
    entry := ``Source.stringExtract
    args := #[.string "Aé😀Z", .nat 4, .nat 7]
    argSchemas := #[.string, .nat, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringExtract "Aé😀Z" 4 7)
    tags := #["stress", "string", "unicode", "extract", "allocation", "non-bmp",
      "invalid-begin", "continuation-byte", "regression", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.extract]
    requiredExecutedExternals := #[``String.Internal.extract]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.extract]
    requiredExecutedExternalTrace := some #[``String.Internal.extract]
    provenance := firProvenance
      "Return empty when the begin position is inside a non-BMP scalar" },
  { id := "string-extract-invalid-end"
    entry := ``Source.stringExtract
    args := #[.string "Aé😀Z", .nat 3, .nat 4]
    argSchemas := #[.string, .nat, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringExtract "Aé😀Z" 3 4)
    tags := #["stress", "string", "unicode", "extract", "allocation", "non-bmp",
      "invalid-end", "continuation-byte", "suffix", "regression", "external",
      "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.extract]
    requiredExecutedExternals := #[``String.Internal.extract]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.extract]
    requiredExecutedExternalTrace := some #[``String.Internal.extract]
    provenance := firProvenance
      "Continue to String end when the end position is inside a scalar" },
  { id := "string-extract-past-end"
    entry := ``Source.stringExtract
    args := #[.string "Aé😀Z", .nat 1, .nat 50]
    argSchemas := #[.string, .nat, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringExtract "Aé😀Z" 1 50)
    tags := #["stress", "string", "unicode", "extract", "allocation", "past-end",
      "suffix", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.extract]
    requiredExecutedExternals := #[``String.Internal.extract]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.extract]
    requiredExecutedExternalTrace := some #[``String.Internal.extract]
    provenance := firProvenance
      "Extract the complete suffix when the end position is far past end" },
  { id := "string-extract-reversed"
    entry := ``Source.stringExtract
    args := #[.string "Aé😀Z", .nat 7, .nat 3]
    argSchemas := #[.string, .nat, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringExtract "Aé😀Z" 7 3)
    tags := #["stress", "string", "unicode", "extract", "allocation", "reversed",
      "empty", "external", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.extract]
    requiredExecutedExternals := #[``String.Internal.extract]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.extract]
    requiredExecutedExternalTrace := some #[``String.Internal.extract]
    provenance := firProvenance
      "Return empty for a begin position greater than the end position" },
  { id := "string-append-empty-right"
    entry := ``Source.stringAppend
    args := #[.string "Aé😀", .string ""]
    argSchemas := #[.string, .string]
    resultSchema := .string
    native := fun _ => .string (Source.stringAppend "Aé😀" "")
    tags := #["stress", "string", "unicode", "construction", "append", "empty",
      "external", "ownership", "unique", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.append]
    requiredExecutedExternals := #[``String.Internal.append]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.append]
    requiredExecutedExternalTrace := some #[``String.Internal.append]
    provenance := firProvenance
      "Append an empty borrowed right operand while consuming a unique Unicode source" },
  { id := "string-append-empty-left"
    entry := ``Source.stringAppend
    args := #[.string "", .string "\u0000é😀"]
    argSchemas := #[.string, .string]
    resultSchema := .string
    native := fun _ => .string (Source.stringAppend "" "\u0000é😀")
    tags := #["stress", "string", "unicode", "construction", "append", "empty",
      "nul", "non-bmp", "external", "ownership", "unique", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.append]
    requiredExecutedExternals := #[``String.Internal.append]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.append]
    requiredExecutedExternalTrace := some #[``String.Internal.append]
    provenance := firProvenance
      "Grow a consumed empty String with NUL, BMP, and non-BMP borrowed contents" },
  { id := "string-append-unicode"
    entry := ``Source.stringAppend
    args := #[.string "A\u0000é", .string "😀Z"]
    argSchemas := #[.string, .string]
    resultSchema := .string
    native := fun _ => .string (Source.stringAppend "A\u0000é" "😀Z")
    tags := #["stress", "string", "unicode", "construction", "append", "nul",
      "bmp", "non-bmp", "external", "ownership", "unique", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.Internal.append]
    requiredExecutedExternals := #[``String.Internal.append]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.append]
    requiredExecutedExternalTrace := some #[``String.Internal.append]
    provenance := firProvenance
      "Append NUL, BMP, and non-BMP contents across the consumed/borrowed boundary" },
  { id := "string-append-shared"
    entry := ``Source.stringAppendShared
    args := #[.string "Aé", .string "😀Z"]
    argSchemas := #[.string, .string]
    resultSchema := .ctor "Prod.mk" 0 #[.string, .string]
    native := fun _ => stringPairDatum (Source.stringAppendShared "Aé" "😀Z")
    tags := #["stress", "string", "unicode", "construction", "append", "external",
      "ownership", "shared", "copy-on-write", "alias", "non-bmp"]
    requiredLcnfForms := #["inc", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfForms := #["inc", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfFormTrace := some sharedStringAppendFormTrace
    requiredExternals := #[``String.Internal.append]
    requiredExecutedExternals := #[``String.Internal.append]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.append]
    requiredExecutedExternalTrace := some #[``String.Internal.append]
    provenance := firProvenance
      "Retain the consumed left alias while append takes its shared copy-on-write path" },
  { id := "string-append-self-shared"
    entry := ``Source.stringAppendSelfShared
    args := #[.string "Aé😀"]
    argSchemas := #[.string]
    resultSchema := .ctor "Prod.mk" 0 #[.string, .string]
    native := fun _ => stringPairDatum (Source.stringAppendSelfShared "Aé😀")
    tags := #["stress", "string", "unicode", "construction", "append", "external",
      "ownership", "shared", "copy-on-write", "alias", "self-alias", "non-bmp"]
    requiredLcnfForms := #["inc", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfForms := #["inc", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfFormTrace := some sharedStringAppendFormTrace
    requiredExternals := #[``String.Internal.append]
    requiredExecutedExternals := #[``String.Internal.append]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.append]
    requiredExecutedExternalTrace := some #[``String.Internal.append]
    provenance := firProvenance
      "Use one retained String as both consumed left and borrowed right append operands" },
  { id := "string-pushn-zero"
    entry := ``Source.stringPushnNonBmp
    args := #[.string "Aé", .nat 0]
    argSchemas := #[.string, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringPushnNonBmp "Aé" 0)
    tags := #["stress", "string", "unicode", "construction", "pushn", "zero",
      "external", "ownership", "unique", "no-op", "boundary"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some stringPushnFormTrace
    requiredExternals := #[``String.Internal.pushn]
    requiredExecutedExternals := #[``String.Internal.pushn]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.pushn]
    requiredExecutedExternalTrace := some #[``String.Internal.pushn]
    provenance := firProvenance
      "Require zero-count pushn to return its exact consumed source without allocation" },
  { id := "string-pushn-nonbmp-two"
    entry := ``Source.stringPushnNonBmp
    args := #[.string "Aé", .nat 2]
    argSchemas := #[.string, .nat]
    resultSchema := .string
    native := fun _ => .string (Source.stringPushnNonBmp "Aé" 2)
    tags := #["stress", "string", "unicode", "construction", "pushn", "non-bmp",
      "external", "ownership", "unique", "multiplicity"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some stringPushnFormTrace
    requiredExternals := #[``String.Internal.pushn]
    requiredExecutedExternals := #[``String.Internal.pushn]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.pushn]
    requiredExecutedExternalTrace := some #[``String.Internal.pushn]
    provenance := firProvenance
      "Append two complete non-BMP scalars while consuming a unique source" },
  { id := "string-pushn-zero-shared"
    entry := ``Source.stringPushnNonBmpShared
    args := #[.string "Aé", .nat 0]
    argSchemas := #[.string, .nat]
    resultSchema := .ctor "Prod.mk" 0 #[.string, .string]
    native := fun _ => stringPairDatum (Source.stringPushnNonBmpShared "Aé" 0)
    tags := #["stress", "string", "unicode", "construction", "pushn", "zero",
      "external", "ownership", "shared", "alias", "no-op", "boundary"]
    requiredLcnfForms := #["inc", "lit", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfForms := #["inc", "lit", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfFormTrace := some sharedStringPushnFormTrace
    requiredExternals := #[``String.Internal.pushn]
    requiredExecutedExternals := #[``String.Internal.pushn]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.pushn]
    requiredExecutedExternalTrace := some #[``String.Internal.pushn]
    provenance := firProvenance
      "Retain a shared source across zero-count pushn and return both aliases" },
  { id := "string-pushn-shared-nonbmp-two"
    entry := ``Source.stringPushnNonBmpShared
    args := #[.string "Aé", .nat 2]
    argSchemas := #[.string, .nat]
    resultSchema := .ctor "Prod.mk" 0 #[.string, .string]
    native := fun _ => stringPairDatum (Source.stringPushnNonBmpShared "Aé" 2)
    tags := #["stress", "string", "unicode", "construction", "pushn", "non-bmp",
      "external", "ownership", "shared", "copy-on-write", "alias", "multiplicity"]
    requiredLcnfForms := #["inc", "lit", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfForms := #["inc", "lit", "fap", "extern", "ctor", "return"]
    requiredExecutedLcnfFormTrace := some sharedStringPushnFormTrace
    requiredExternals := #[``String.Internal.pushn]
    requiredExecutedExternals := #[``String.Internal.pushn]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``String.Internal.pushn]
    requiredExecutedExternalTrace := some #[``String.Internal.pushn]
    provenance := firProvenance
      "Retain the source while repeated non-BMP push takes its shared copy-on-write path" },
  { id := "string-dec-eq-nul-nonbmp-true"
    entry := ``Source.stringDecEq
    args := #[.string "A\u0000é😀", .string "A\u0000é😀"]
    argSchemas := #[.string, .string]
    resultSchema := .bool
    native := fun _ => .bool (Source.stringDecEq "A\u0000é😀" "A\u0000é😀")
    tags := #["stress", "string", "unicode", "comparison", "equality", "true",
      "nul", "non-bmp", "external", "borrowed"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.decEq]
    requiredExecutedExternals := #[``String.decEq]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.decEq]
    requiredExecutedExternalTrace := some #[``String.decEq]
    provenance := firProvenance
      "Decide exact equality across NUL, BMP, and non-BMP UTF-8 contents" },
  { id := "string-dec-eq-nonbmp-false"
    entry := ``Source.stringDecEq
    args := #[.string "A\u0000é😀", .string "A\u0000é😁"]
    argSchemas := #[.string, .string]
    resultSchema := .bool
    native := fun _ => .bool (Source.stringDecEq "A\u0000é😀" "A\u0000é😁")
    tags := #["stress", "string", "unicode", "comparison", "equality", "false",
      "nul", "non-bmp", "external", "borrowed", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.decEq]
    requiredExecutedExternals := #[``String.decEq]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.decEq]
    requiredExecutedExternalTrace := some #[``String.decEq]
    provenance := firProvenance
      "Reject strings that differ only at one non-BMP scalar" },
  { id := "string-dec-eq-prefix-false"
    entry := ``Source.stringDecEq
    args := #[.string "A", .string "A\u0000"]
    argSchemas := #[.string, .string]
    resultSchema := .bool
    native := fun _ => .bool (Source.stringDecEq "A" "A\u0000")
    tags := #["stress", "string", "comparison", "equality", "false", "prefix",
      "nul", "external", "borrowed", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.decEq]
    requiredExecutedExternals := #[``String.decEq]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.decEq]
    requiredExecutedExternalTrace := some #[``String.decEq]
    provenance := firProvenance
      "Reject a proper prefix when the longer String continues with NUL" },
  { id := "string-dec-lt-bmp-supplementary-true"
    entry := ``Source.stringDecLt
    args := #[.string bmpPrivateUseString, .string supplementaryPlaneString]
    argSchemas := #[.string, .string]
    resultSchema := .bool
    native := fun _ => .bool
      (Source.stringDecLt bmpPrivateUseString supplementaryPlaneString)
    tags := #["stress", "string", "unicode", "comparison", "ordering", "true",
      "bmp", "non-bmp", "external", "borrowed", "utf8", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.decidableLT]
    requiredExecutedExternals := #[``String.decidableLT]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.decidableLT]
    requiredExecutedExternalTrace := some #[``String.decidableLT]
    provenance := firProvenance
      "Order BMP U+E000 before supplementary U+10000 by UTF-8 rather than JS UTF-16" },
  { id := "string-dec-lt-supplementary-bmp-false"
    entry := ``Source.stringDecLt
    args := #[.string supplementaryPlaneString, .string bmpPrivateUseString]
    argSchemas := #[.string, .string]
    resultSchema := .bool
    native := fun _ => .bool
      (Source.stringDecLt supplementaryPlaneString bmpPrivateUseString)
    tags := #["stress", "string", "unicode", "comparison", "ordering", "false",
      "bmp", "non-bmp", "external", "borrowed", "utf8", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.decidableLT]
    requiredExecutedExternals := #[``String.decidableLT]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.decidableLT]
    requiredExecutedExternalTrace := some #[``String.decidableLT]
    provenance := firProvenance
      "Reject the reverse supplementary/BMP order at the UTF-16 discriminator" },
  { id := "string-dec-lt-prefix-true"
    entry := ``Source.stringDecLt
    args := #[.string "A", .string "A\u0000"]
    argSchemas := #[.string, .string]
    resultSchema := .bool
    native := fun _ => .bool (Source.stringDecLt "A" "A\u0000")
    tags := #["stress", "string", "comparison", "ordering", "true", "prefix",
      "nul", "external", "borrowed", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``String.decidableLT]
    requiredExecutedExternals := #[``String.decidableLT]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.decidableLT]
    requiredExecutedExternalTrace := some #[``String.decidableLT]
    provenance := firProvenance
      "Order a proper String prefix before the longer NUL-extended value" },
  { id := "string-compare-equal"
    entry := ``Source.stringCompareClassify
    args := #[.string "A\u0000é😀", .string "A\u0000é😀"]
    argSchemas := #[.string, .string]
    resultSchema := .nat
    native := fun _ => .nat
      (Source.stringCompareClassify "A\u0000é😀" "A\u0000é😀")
    tags := #["stress", "string", "unicode", "comparison", "ordering", "equal",
      "nul", "non-bmp", "external", "control-flow", "scalar-enum"]
    requiredLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfFormTrace := some stringCompareClassifyFormTrace
    requiredExternals := #[``String.compare]
    requiredExecutedExternals := #[``String.compare]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.compare]
    requiredExecutedExternalTrace := some #[``String.compare]
    provenance := firProvenance
      "Classify the scalar Ordering.eq result returned by exact String comparison" },
  { id := "string-compare-bmp-supplementary-lt"
    entry := ``Source.stringCompareClassify
    args := #[.string bmpPrivateUseString, .string supplementaryPlaneString]
    argSchemas := #[.string, .string]
    resultSchema := .nat
    native := fun _ => .nat
      (Source.stringCompareClassify bmpPrivateUseString supplementaryPlaneString)
    tags := #["stress", "string", "unicode", "comparison", "ordering", "less",
      "bmp", "non-bmp", "external", "control-flow", "scalar-enum", "utf8", "boundary"]
    requiredLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfFormTrace := some stringCompareClassifyFormTrace
    requiredExternals := #[``String.compare]
    requiredExecutedExternals := #[``String.compare]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.compare]
    requiredExecutedExternalTrace := some #[``String.compare]
    provenance := firProvenance
      "Take the Ordering.lt branch for BMP U+E000 versus supplementary U+10000" },
  { id := "string-compare-supplementary-bmp-gt"
    entry := ``Source.stringCompareClassify
    args := #[.string supplementaryPlaneString, .string bmpPrivateUseString]
    argSchemas := #[.string, .string]
    resultSchema := .nat
    native := fun _ => .nat
      (Source.stringCompareClassify supplementaryPlaneString bmpPrivateUseString)
    tags := #["stress", "string", "unicode", "comparison", "ordering", "greater",
      "bmp", "non-bmp", "external", "control-flow", "scalar-enum", "utf8", "boundary"]
    requiredLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfFormTrace := some stringCompareClassifyFormTrace
    requiredExternals := #[``String.compare]
    requiredExecutedExternals := #[``String.compare]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.compare]
    requiredExecutedExternalTrace := some #[``String.compare]
    provenance := firProvenance
      "Take the Ordering.gt branch for the reverse supplementary/BMP order" },
  { id := "string-compare-prefix-lt"
    entry := ``Source.stringCompareClassify
    args := #[.string "A", .string "A\u0000"]
    argSchemas := #[.string, .string]
    resultSchema := .nat
    native := fun _ => .nat (Source.stringCompareClassify "A" "A\u0000")
    tags := #["stress", "string", "comparison", "ordering", "less", "prefix",
      "nul", "external", "control-flow", "scalar-enum", "boundary"]
    requiredLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "cases", "lit", "return"]
    requiredExecutedLcnfFormTrace := some stringCompareClassifyFormTrace
    requiredExternals := #[``String.compare]
    requiredExecutedExternals := #[``String.compare]
    requiredExecutedExternalCounts := exactlyOnceExternalCounts #[``String.compare]
    requiredExecutedExternalTrace := some #[``String.compare]
    provenance := firProvenance
      "Take the Ordering.lt branch when equal bytes end at the shorter prefix" },
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
        "heap", "boundary", "updated", "path-exclusion"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    requiredExecutedLcnfFormCounts :=
      #[{ form := "oset", minimum := 0, maximum := some 0 }]
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
        "heap", "boundary", "original", "path-exclusion"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    requiredExecutedLcnfFormCounts :=
      #[{ form := "oset", minimum := 0, maximum := some 0 }]
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
        "refcount", "bytearray", "heap", "boundary", "path-exclusion"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    requiredExecutedLcnfFormCounts :=
      #[{ form := "oset", minimum := 0, maximum := some 0 }]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.set!]
    requiredExecutedExternalTrace := some #[``ByteArray.set!]
    provenance := firProvenance
      "Replace one alias, then retain and mutate the surviving child to test nested copy-on-write" },
  { id := "aliased-byte-array-self-replace"
    entry := ``Source.aliasedByteArraySelfReplace
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setFirst]
    args := aliasedByteArraySelfArgs
    argSchemas := aliasedByteArraySelfArgSchemas
    resultSchema := byteArrayPairSchema
    native := fun _ => byteArrayPairDatum
      (Source.aliasedByteArraySelfReplace mixedLayoutBytes Source.maxUSize Source.maxUInt32)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "alias", "self-replace",
        "refcount", "bytearray", "heap", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUpdateForms
    provenance := firProvenance
      "Replace slot 0 with its existing aliased child and return both surviving occurrences" },
  { id := "aliased-byte-array-shared-self-replace"
    entry := ``Source.aliasedByteArraySharedSelfReplace
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setFirst]
    args := aliasedByteArraySelfArgs
    argSchemas := aliasedByteArraySelfArgSchemas
    resultSchema := byteArrayPairPairSchema
    native := fun _ => byteArrayPairPairDatum
      (Source.aliasedByteArraySharedSelfReplace
        mixedLayoutBytes Source.maxUSize Source.maxUInt32)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "shared", "copy-on-write", "alias",
        "self-replace", "refcount", "bytearray", "heap", "boundary", "path-exclusion"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    requiredExecutedLcnfFormCounts :=
      #[{ form := "oset", minimum := 0, maximum := some 0 }]
    provenance := firProvenance
      "Self-replace slot 0 on a shared aggregate and return updated and original field pairs" },
  { id := "aliased-byte-array-self-replace-child-copy-on-write"
    entry := ``Source.aliasedByteArraySelfReplaceChildCopyOnWrite
    dependencies :=
      #[``Source.mkAliasedByteArrayLayout, ``Source.AliasedByteArrayLayout.setFirst]
    args := aliasedByteArraySelfArgs
    argSchemas := aliasedByteArraySelfArgSchemas
    resultSchema := byteArrayPairSchema
    native := fun _ => byteArrayPairDatum
      (Source.aliasedByteArraySelfReplaceChildCopyOnWrite
        mixedLayoutBytes Source.maxUSize Source.maxUInt32)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "alias", "self-replace",
        "refcount", "bytearray", "external", "copy-on-write", "heap", "boundary"]
    requiredLcnfForms := aliasedChildCopyOnWriteForms
    requiredExecutedLcnfForms := aliasedChildCopyOnWriteForms
    requiredExternals := #[``ByteArray.set!]
    requiredExecutedExternals := #[``ByteArray.set!]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.set!]
    requiredExecutedExternalTrace := some #[``ByteArray.set!]
    provenance := firProvenance
      "Self-replace one alias, then mutate it while returning the untouched sibling occurrence" },
  { id := "byte-array-object-swap-unique"
    entry := ``Source.byteArrayObjectSwap
    dependencies :=
      #[``Source.mkByteArrayPairLayout, ``Source.AliasedByteArrayLayout.swap]
    args := byteArrayObjectSwapArgs
    argSchemas := byteArrayObjectSwapArgSchemas
    resultSchema := byteArrayPairSchema
    native := fun _ => byteArrayPairDatum
      (Source.byteArrayObjectSwap mixedLayoutBytes multiObjectReplacementBytes
        Source.maxUSize Source.maxUInt32)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "unique", "swap", "refcount",
        "bytearray", "heap", "multiplicity", "boundary"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := objectUpdateForms
    requiredExecutedLcnfFormCounts :=
      #[{ form := "oset", minimum := 2, maximum := some 2 }]
    provenance := firProvenance
      "Swap two distinct heap children on the unique path and require both object writes" },
  { id := "byte-array-object-swap-shared"
    entry := ``Source.byteArrayObjectSwapShared
    dependencies :=
      #[``Source.mkByteArrayPairLayout, ``Source.AliasedByteArrayLayout.swap]
    args := byteArrayObjectSwapArgs
    argSchemas := byteArrayObjectSwapArgSchemas
    resultSchema := byteArrayPairPairSchema
    native := fun _ => byteArrayPairPairDatum
      (Source.byteArrayObjectSwapShared mixedLayoutBytes multiObjectReplacementBytes
        Source.maxUSize Source.maxUInt32)
    tags :=
      #["stress", "mixed-layout", "object", "mutation", "shared", "copy-on-write", "swap",
        "refcount", "bytearray", "heap", "boundary", "path-exclusion"]
    requiredLcnfForms := objectUpdateForms
    requiredExecutedLcnfForms := mixedUpdateForms
    requiredExecutedLcnfFormCounts :=
      #[{ form := "oset", minimum := 0, maximum := some 0 }]
    provenance := firProvenance
      "Swap two distinct heap children on a copied aggregate while retaining the original pair" },
  { id := "tuple-rotate"
    entry := ``Source.tupleRotate
    args := #[.ctor "Prod.mk" 0 #[.nat 1, .ctor "Prod.mk" 0 #[.nat 2, .nat 3]]]
    argSchemas := #[.ctor "Prod.mk" 0 #[.nat, .ctor "Prod.mk" 0 #[.nat, .nat]]]
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .ctor "Prod.mk" 0 #[.nat, .nat]]
    native := fun _ =>
      let result := Source.tupleRotate (1, 2, 3)
      .ctor "Prod.mk" 0 #[.nat result.1, .ctor "Prod.mk" 0 #[.nat result.2.1, .nat result.2.2]]
    tags := #["quick", "constructor", "projection", "allocation", "multiplicity"]
    requiredLcnfForms := #["oproj", "ctor", "return"]
    requiredExecutedLcnfForms := #["oproj", "isShared", "cases", "oset", "jump", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "isShared", minimum := 2, maximum := some 2 },
        { form := "oproj", minimum := 4, maximum := some 4 },
        { form := "oset", minimum := 4, maximum := some 4 }]
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
    tags :=
      #["stress", "ownership", "reuse", "recursion", "constructor", "multiplicity"]
    fuel := 100000
    requiredLcnfForms :=
      #["cases", "oproj", "inc", "join", "fap", "oset", "jump", "ctor", "isShared",
        "dec", "return"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "inc", "join", "isShared", "dec", "jump", "oset", "fap",
        "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "dec", minimum := 2, maximum := some 2 },
        { form := "isShared", minimum := 2, maximum := some 2 },
        { form := "oset", minimum := 4, maximum := some 4 }]
    provenance := leanCompileProvenance "tests/compile/reusebug.lean"
      "Pure terminating reassociation adapted to execute the ownership/reuse path" },
  { id := "reuse-change-tag"
    entry := ``Source.changeOrGrow
    dependencies := #[``Source.holdNat]
    args := #[.bool true, .ctor "GrowSwitch.left" 0 #[.nat 7]]
    argSchemas := #[.bool, .ctor "GrowSwitch.left" 0 #[.nat]]
    resultSchema := .ctor "GrowSwitch.right" 1 #[.nat]
    native := fun _ => growSwitchDatum (Source.changeOrGrow true (.left 7))
    tags :=
      #["stress", "ownership", "reuse", "constructor", "set-tag", "boundary",
        "path-exclusion"]
    requiredLcnfForms :=
      #["cases", "oproj", "join", "fap", "dec", "del", "inc", "ctor", "return",
        "setTag", "oset", "jump", "isShared"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "join", "isShared", "jump", "fap", "inc", "return", "dec",
        "setTag", "oset"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "isShared", minimum := 1, maximum := some 1 },
        { form := "setTag", minimum := 1, maximum := some 1 },
        { form := "oset", minimum := 1, maximum := some 1 },
        { form := "del", minimum := 0, maximum := some 0 },
        { form := "ctor", minimum := 0, maximum := some 0 }]
    requiredExecutedLcnfFormTrace := some reuseChangeTagFormTrace
    provenance := firProvenance
      "Reuse a unique constructor at the same size while changing its runtime tag" },
  { id := "reuse-grow-delete"
    entry := ``Source.changeOrGrow
    dependencies := #[``Source.holdNat]
    args := #[.bool false, .ctor "GrowSwitch.left" 0 #[.nat 7]]
    argSchemas := #[.bool, .ctor "GrowSwitch.left" 0 #[.nat]]
    resultSchema := .ctor "GrowSwitch.big" 2 #[.nat, .nat]
    native := fun _ => growSwitchDatum (Source.changeOrGrow false (.left 7))
    tags :=
      #["stress", "ownership", "reuse", "constructor", "delete", "boundary",
        "path-exclusion"]
    requiredLcnfForms :=
      #["cases", "oproj", "join", "fap", "dec", "del", "inc", "ctor", "return",
        "setTag", "oset", "jump", "isShared"]
    requiredExecutedLcnfForms :=
      #["cases", "oproj", "join", "isShared", "jump", "fap", "inc", "return", "dec",
        "del", "ctor"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "isShared", minimum := 1, maximum := some 1 },
        { form := "del", minimum := 1, maximum := some 1 },
        { form := "ctor", minimum := 1, maximum := some 1 },
        { form := "setTag", minimum := 0, maximum := some 0 },
        { form := "oset", minimum := 0, maximum := some 0 }]
    requiredExecutedLcnfFormTrace := some reuseGrowDeleteFormTrace
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
    tags :=
      #["stress", "ownership", "reuse", "constructor", "delete", "shared",
        "path-exclusion"]
    requiredLcnfForms :=
      #["inc", "fap", "cases", "join", "isShared", "jump", "del", "ctor", "return",
        "setTag", "oset"]
    requiredExecutedLcnfForms :=
      #["inc", "fap", "cases", "join", "isShared", "jump", "del", "ctor", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "isShared", minimum := 1, maximum := some 1 },
        { form := "del", minimum := 1, maximum := some 1 },
        { form := "ctor", minimum := 2, maximum := some 2 },
        { form := "setTag", minimum := 0, maximum := some 0 },
        { form := "oset", minimum := 0, maximum := some 0 }]
    requiredExecutedLcnfFormTrace := some reuseGrowDeleteSharedFormTrace
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
    requiredExecutedLcnfFormTrace := some scalarEnumFormTrace
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
  { id := "int-multi-limb-positive-roundtrip"
    entry := ``Source.idInt
    args := #[.int 340282366920938463463374607431768211473]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ =>
      .int (Source.idInt 340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "boundary", "heap", "multi-limb",
      "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip positive 2^128 + 17 without an external" },
  { id := "int-multi-limb-negative-roundtrip"
    entry := ``Source.idInt
    args := #[.int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ =>
      .int (Source.idInt (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "negative", "boundary", "heap",
      "multi-limb", "roundtrip"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip negative 2^128 + 17 through negSucc without an external" },
  { id := "int-multi-limb-positive-negate"
    entry := ``Source.negateInt
    args := #[.int 340282366920938463463374607431768211473]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ =>
      .int (Source.negateInt 340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "negative", "heap", "multi-limb",
      "external", "arithmetic"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``Int.neg]
    requiredExecutedExternals := #[``Int.neg]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.neg]
    requiredExecutedExternalTrace := some #[``Int.neg]
    provenance := firProvenance
      "Negate positive 2^128 + 17 through the modeled runtime primitive" },
  { id := "int-multi-limb-negative-negate"
    entry := ``Source.negateInt
    args := #[.int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int]
    resultSchema := .int
    native := fun _ =>
      .int (Source.negateInt (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "negative", "heap", "multi-limb",
      "external", "arithmetic"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExternals := #[``Int.neg]
    requiredExecutedExternals := #[``Int.neg]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.neg]
    requiredExecutedExternalTrace := some #[``Int.neg]
    provenance := firProvenance
      "Negate negative 2^128 + 17 back to a positive multi-limb Int" },
  { id := "int-of-nat-multi-limb-positive"
    entry := ``Source.intOfNat
    args := #[.nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat]
    resultSchema := .int
    native := fun _ =>
      .int (Source.intOfNat 340282366920938463463374607431768211473)
    tags := #["stress", "int", "nat", "signed", "heap", "multi-limb",
      "external", "conversion"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some intOfNatFormTrace
    requiredExternals := #[``Int.ofNat]
    requiredExecutedExternals := #[``Int.ofNat]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat]
    requiredExecutedExternalTrace := some #[``Int.ofNat]
    provenance := firProvenance
      "Convert positive Nat 2^128 + 17 to an exact multi-limb Int" },
  { id := "int-of-nat-multi-limb-negative"
    entry := ``Source.negIntOfNat
    args := #[.nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat]
    resultSchema := .int
    native := fun _ =>
      .int (Source.negIntOfNat 340282366920938463463374607431768211473)
    tags := #["stress", "int", "nat", "signed", "negative", "heap",
      "multi-limb", "external", "conversion"]
    requiredLcnfForms := #["fap", "extern", "dec", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "dec", "return"]
    requiredExecutedLcnfFormTrace := some negIntOfNatFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.neg]
    provenance := firProvenance
      "Convert Nat 2^128 + 17 then negate it through exact externals" },
  { id := "int-add-multi-limb-positive-growth"
    entry := ``Source.addInt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.addInt
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "heap", "multi-limb", "external",
      "arithmetic", "addition", "growth"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.add]
    requiredExecutedExternals := #[``Int.add]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.add]
    requiredExecutedExternalTrace := some #[``Int.add]
    provenance := firProvenance
      "Add two positive multi-limb Int values and retain a heap result" },
  { id := "int-add-multi-limb-negative-growth"
    entry := ``Source.addInt
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.addInt
      (-340282366920938463463374607431768211473)
      (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "negative", "heap", "multi-limb",
      "external", "arithmetic", "addition", "growth"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.add]
    requiredExecutedExternals := #[``Int.add]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.add]
    requiredExecutedExternalTrace := some #[``Int.add]
    provenance := firProvenance
      "Add two negative multi-limb Int values and retain negSucc magnitude" },
  { id := "int-add-multi-limb-cancellation"
    entry := ``Source.addInt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.addInt
      340282366920938463463374607431768211473
      (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "heap", "multi-limb", "external",
      "arithmetic", "addition", "cancellation", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.add]
    requiredExecutedExternals := #[``Int.add]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.add]
    requiredExecutedExternalTrace := some #[``Int.add]
    provenance := firProvenance
      "Cancel opposite multi-limb heap Int values to immediate zero" },
  { id := "int-sub-multi-limb-positive-growth"
    entry := ``Source.subInt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.subInt
      340282366920938463463374607431768211473
      (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "heap", "multi-limb", "external",
      "arithmetic", "subtraction", "growth"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.sub]
    requiredExecutedExternals := #[``Int.sub]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.sub]
    requiredExecutedExternalTrace := some #[``Int.sub]
    provenance := firProvenance
      "Subtract a negative multi-limb Int and retain a positive heap result" },
  { id := "int-sub-multi-limb-negative-growth"
    entry := ``Source.subInt
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.subInt
      (-340282366920938463463374607431768211473)
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "negative", "heap", "multi-limb",
      "external", "arithmetic", "subtraction", "growth"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.sub]
    requiredExecutedExternals := #[``Int.sub]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.sub]
    requiredExecutedExternalTrace := some #[``Int.sub]
    provenance := firProvenance
      "Subtract a positive multi-limb Int and retain negSucc magnitude" },
  { id := "int-sub-multi-limb-cancellation"
    entry := ``Source.subInt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.subInt
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "heap", "multi-limb", "external",
      "arithmetic", "subtraction", "cancellation", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.sub]
    requiredExecutedExternals := #[``Int.sub]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.sub]
    requiredExecutedExternalTrace := some #[``Int.sub]
    provenance := firProvenance
      "Subtract equal multi-limb heap Int values to immediate zero" },
  { id := "int-mul-immediate-overflow-positive"
    entry := ``Source.mulInt
    args := #[.int 2147483647, .int 2]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.mulInt 2147483647 2)
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "multiplication", "boundary", "heap", "overflow"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.mul]
    requiredExecutedExternals := #[``Int.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.mul]
    requiredExecutedExternalTrace := some #[``Int.mul]
    provenance := firProvenance
      "Multiply immediate Int operands across the positive heap boundary" },
  { id := "int-mul-immediate-min-sign-flip"
    entry := ``Source.mulInt
    args := #[.int (-2147483648), .int (-1)]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.mulInt (-2147483648) (-1))
    tags := #["stress", "int", "signed", "negative", "external",
      "arithmetic", "multiplication", "boundary", "heap", "sign"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.mul]
    requiredExecutedExternals := #[``Int.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.mul]
    requiredExecutedExternalTrace := some #[``Int.mul]
    provenance := firProvenance
      "Negate the immediate Int minimum through multiplication and return a heap positive" },
  { id := "int-mul-multi-limb-negative"
    entry := ``Source.mulInt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int (-17)]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.mulInt
      340282366920938463463374607431768211473
      (-17))
    tags := #["stress", "int", "signed", "negative", "external",
      "arithmetic", "multiplication", "heap", "multi-limb", "growth"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.mul]
    requiredExecutedExternals := #[``Int.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.mul]
    requiredExecutedExternalTrace := some #[``Int.mul]
    provenance := firProvenance
      "Multiply a positive multi-limb Int by a negative immediate operand" },
  { id := "int-mul-multi-limb-zero"
    entry := ``Source.mulInt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int 0]
    argSchemas := #[.int, .int]
    resultSchema := .int
    native := fun _ => .int (Source.mulInt
      340282366920938463463374607431768211473
      0)
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "multiplication", "heap-input", "multi-limb", "zero", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.mul]
    requiredExecutedExternals := #[``Int.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.mul]
    requiredExecutedExternalTrace := some #[``Int.mul]
    provenance := firProvenance
      "Collapse a heap multi-limb Int times zero to the immediate representation" },
  { id := "int-divmod-positive-positive"
    entry := ``Source.divModInt
    args := #[.int 12, .int 7]
    argSchemas := #[.int, .int]
    resultSchema := .ctor "Prod.mk" 0 #[.int, .int]
    native := fun _ => intPairDatum (Source.divModInt 12 7)
    tags := #["quick", "int", "signed", "external", "arithmetic",
      "division", "remainder", "euclidean", "positive", "sign-matrix"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalTrace := some #[``Int.ediv, ``Int.emod]
    provenance := firProvenance
      "Pin positive/positive Euclidean Int quotient and remainder together" },
  { id := "int-divmod-positive-negative"
    entry := ``Source.divModInt
    args := #[.int 12, .int (-7)]
    argSchemas := #[.int, .int]
    resultSchema := .ctor "Prod.mk" 0 #[.int, .int]
    native := fun _ => intPairDatum (Source.divModInt 12 (-7))
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "division", "remainder", "euclidean", "positive", "negative",
      "sign-matrix"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalTrace := some #[``Int.ediv, ``Int.emod]
    provenance := firProvenance
      "Pin positive/negative Euclidean Int quotient and nonnegative remainder" },
  { id := "int-divmod-negative-positive"
    entry := ``Source.divModInt
    args := #[.int (-12), .int 7]
    argSchemas := #[.int, .int]
    resultSchema := .ctor "Prod.mk" 0 #[.int, .int]
    native := fun _ => intPairDatum (Source.divModInt (-12) 7)
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "division", "remainder", "euclidean", "negative", "positive",
      "sign-matrix", "rounding"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalTrace := some #[``Int.ediv, ``Int.emod]
    provenance := firProvenance
      "Distinguish Euclidean floor division from truncation for a negative dividend" },
  { id := "int-divmod-negative-negative"
    entry := ``Source.divModInt
    args := #[.int (-12), .int (-7)]
    argSchemas := #[.int, .int]
    resultSchema := .ctor "Prod.mk" 0 #[.int, .int]
    native := fun _ => intPairDatum (Source.divModInt (-12) (-7))
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "division", "remainder", "euclidean", "negative", "sign-matrix",
      "rounding"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalTrace := some #[``Int.ediv, ``Int.emod]
    provenance := firProvenance
      "Pin negative/negative Euclidean Int quotient and nonnegative remainder" },
  { id := "int-divmod-multi-limb-negative"
    entry := ``Source.divModInt
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int 17]
    argSchemas := #[.int, .int]
    resultSchema := .ctor "Prod.mk" 0 #[.int, .int]
    native := fun _ => intPairDatum (Source.divModInt
      (-340282366920938463463374607431768211473)
      17)
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "division", "remainder", "euclidean", "negative", "multi-limb",
      "heap", "exact", "rounding"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalTrace := some #[``Int.ediv, ``Int.emod]
    provenance := firProvenance
      "Retain exact multi-limb Euclidean quotient and adjusted remainder" },
  { id := "int-divmod-zero-divisor"
    entry := ``Source.divModInt
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int 0]
    argSchemas := #[.int, .int]
    resultSchema := .ctor "Prod.mk" 0 #[.int, .int]
    native := fun _ => intPairDatum (Source.divModInt
      (-340282366920938463463374607431768211473)
      0)
    tags := #["stress", "int", "signed", "external", "arithmetic",
      "division", "remainder", "euclidean", "negative", "multi-limb",
      "heap", "zero-divisor", "boundary"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternals := #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ediv, ``Int.emod]
    requiredExecutedExternalTrace := some #[``Int.ediv, ``Int.emod]
    provenance := firProvenance
      "Pin Int division by zero to zero and remainder by zero to the dividend" },
  { id := "int-dec-eq-multi-limb-true"
    entry := ``Source.decideIntEq
    args := #[
      .int 340282366920938463463374607431768211473,
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideIntEq
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "external", "decision",
      "equality", "true", "multi-limb", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.decEq]
    requiredExecutedExternals := #[``Int.decEq]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.decEq]
    requiredExecutedExternalTrace := some #[``Int.decEq]
    provenance := firProvenance
      "Accept equality of two identical positive multi-limb Int values" },
  { id := "int-dec-eq-opposite-sign-false"
    entry := ``Source.decideIntEq
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideIntEq
      (-340282366920938463463374607431768211473)
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "external", "decision",
      "equality", "false", "negative", "positive", "multi-limb", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.decEq]
    requiredExecutedExternals := #[``Int.decEq]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.decEq]
    requiredExecutedExternalTrace := some #[``Int.decEq]
    provenance := firProvenance
      "Reject equality of opposite-sign multi-limb Int values" },
  { id := "int-dec-lt-opposite-sign-true"
    entry := ``Source.decideIntLt
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideIntLt
      (-340282366920938463463374607431768211473)
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "external", "decision",
      "ordering", "less-than", "true", "negative", "positive",
      "multi-limb", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.decLt]
    requiredExecutedExternals := #[``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.decLt]
    provenance := firProvenance
      "Order a negative multi-limb Int below its positive magnitude" },
  { id := "int-dec-lt-multi-limb-equality-false"
    entry := ``Source.decideIntLt
    args := #[
      .int 340282366920938463463374607431768211473,
      .int 340282366920938463463374607431768211473]
    argSchemas := #[.int, .int]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideIntLt
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "external", "decision",
      "ordering", "less-than", "false", "equality", "multi-limb", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.decLt]
    requiredExecutedExternals := #[``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.decLt]
    provenance := firProvenance
      "Reject strict ordering of equal positive multi-limb Int values" },
  { id := "int-dec-le-multi-limb-equality-true"
    entry := ``Source.decideIntLe
    args := #[
      .int (-340282366920938463463374607431768211473),
      .int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int, .int]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideIntLe
      (-340282366920938463463374607431768211473)
      (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "external", "decision",
      "ordering", "less-or-equal", "true", "equality", "negative",
      "multi-limb", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.decLe]
    requiredExecutedExternals := #[``Int.decLe]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.decLe]
    requiredExecutedExternalTrace := some #[``Int.decLe]
    provenance := firProvenance
      "Accept non-strict ordering of equal negative multi-limb Int values" },
  { id := "int-dec-le-opposite-sign-false"
    entry := ``Source.decideIntLe
    args := #[
      .int 340282366920938463463374607431768211473,
      .int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int, .int]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideIntLe
      340282366920938463463374607431768211473
      (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "external", "decision",
      "ordering", "less-or-equal", "false", "positive", "negative",
      "multi-limb", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.decLe]
    requiredExecutedExternals := #[``Int.decLe]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.decLe]
    requiredExecutedExternalTrace := some #[``Int.decLe]
    provenance := firProvenance
      "Reject non-strict ordering of a positive multi-limb Int below a negative one" },
  { id := "int-nat-abs-multi-limb-positive"
    entry := ``Source.natAbsInt
    args := #[.int 340282366920938463463374607431768211473]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ =>
      .nat (Source.natAbsInt 340282366920938463463374607431768211473)
    tags := #["stress", "int", "nat", "signed", "heap", "multi-limb",
      "external", "conversion", "magnitude"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.natAbs]
    requiredExecutedExternals := #[``Int.natAbs]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.natAbs]
    requiredExecutedExternalTrace := some #[``Int.natAbs]
    provenance := firProvenance
      "Take the natural magnitude of a positive multi-limb heap Int" },
  { id := "int-nat-abs-multi-limb-negative"
    entry := ``Source.natAbsInt
    args := #[.int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ =>
      .nat (Source.natAbsInt (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "nat", "signed", "negative", "heap",
      "multi-limb", "external", "conversion", "magnitude"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.natAbs]
    requiredExecutedExternals := #[``Int.natAbs]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.natAbs]
    requiredExecutedExternalTrace := some #[``Int.natAbs]
    provenance := firProvenance
      "Take the natural magnitude of a negative multi-limb heap Int" },
  { id := "int-nat-abs-immediate-negative-boundary"
    entry := ``Source.natAbsInt
    args := #[.int (-2147483648)]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ => .nat (Source.natAbsInt (-2147483648))
    tags := #["stress", "int", "nat", "signed", "negative", "boundary",
      "external", "conversion", "magnitude"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.natAbs]
    requiredExecutedExternals := #[``Int.natAbs]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.natAbs]
    requiredExecutedExternalTrace := some #[``Int.natAbs]
    provenance := firProvenance
      "Take the natural magnitude at the negative immediate Int boundary" },
  { id := "int-nat-abs-heap-negative-boundary"
    entry := ``Source.natAbsInt
    args := #[.int (-2147483649)]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ => .nat (Source.natAbsInt (-2147483649))
    tags := #["stress", "int", "nat", "signed", "negative", "boundary",
      "heap", "external", "conversion", "magnitude"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Int.natAbs]
    requiredExecutedExternals := #[``Int.natAbs]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.natAbs]
    requiredExecutedExternalTrace := some #[``Int.natAbs]
    provenance := firProvenance
      "Take the natural magnitude of the first negative heap Int" },
  { id := "int-literal-immediate-positive"
    entry := ``Source.intPosImmediate
    resultSchema := .int
    native := fun _ => .int Source.intPosImmediate
    tags := #["stress", "int", "signed", "literal", "external", "boundary"]
    requiredLcnfForms := #["fap", "inc", "return", "lit", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "inc"]
    requiredExternals := #[``Int.ofNat]
    requiredExecutedExternals := #[``Int.ofNat]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat]
    requiredExecutedExternalTrace := some #[``Int.ofNat]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat]
    requiredExecutedExternalTrace := some #[``Int.ofNat]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.neg]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.neg]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.neg]
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
    requiredExecutedLcnfFormTrace := some intClassifyFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.decLt]
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
    requiredExecutedLcnfFormTrace := some intClassifyFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.decLt]
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
    requiredExecutedLcnfFormTrace := some intClassifyFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.decLt]
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
    requiredExecutedLcnfFormTrace := some intClassifyFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify the first negative heap Int" },
  { id := "int-classify-multi-limb-positive"
    entry := ``Source.classifyInt
    args := #[.int 340282366920938463463374607431768211473]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ =>
      .nat (Source.classifyInt 340282366920938463463374607431768211473)
    tags := #["stress", "int", "signed", "cases", "external", "heap",
      "multi-limb"]
    requiredLcnfForms := #["fap", "cases", "lit", "return", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "cases"]
    requiredExecutedLcnfFormTrace := some intClassifyFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify a positive multi-limb heap Int" },
  { id := "int-classify-multi-limb-negative"
    entry := ``Source.classifyInt
    args := #[.int (-340282366920938463463374607431768211473)]
    argSchemas := #[.int]
    resultSchema := .nat
    native := fun _ =>
      .nat (Source.classifyInt (-340282366920938463463374607431768211473))
    tags := #["stress", "int", "signed", "negative", "cases", "external",
      "heap", "multi-limb"]
    requiredLcnfForms := #["fap", "cases", "lit", "return", "extern"]
    requiredExecutedLcnfForms := #["fap", "lit", "extern", "return", "cases"]
    requiredExecutedLcnfFormTrace := some intClassifyFormTrace
    requiredExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternals := #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Int.ofNat, ``Int.decLt]
    requiredExecutedExternalTrace := some #[``Int.ofNat, ``Int.decLt]
    provenance := firProvenance "Classify a negative multi-limb heap Int" },
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.add]
    requiredExecutedExternalTrace := some #[``Nat.add]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.add]
    requiredExecutedExternalTrace := some #[``Nat.add]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.add]
    requiredExecutedExternalTrace := some #[``Nat.add]
    provenance := firProvenance "Nat.add decoding and returning heap natural values" },
  { id := "nat-mul-small"
    entry := ``Source.mulNat
    args := #[.nat 6, .nat 7]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.mulNat 6 7)
    tags := #["quick", "external", "pure", "nat", "arithmetic",
      "multiplication", "tagged"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.mul]
    requiredExecutedExternals := #[``Nat.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.mul]
    requiredExecutedExternalTrace := some #[``Nat.mul]
    provenance := firProvenance
      "Multiply two tagged naturals and retain an immediate result" },
  { id := "nat-mul-tagged-to-heap"
    entry := ``Source.mulNat
    args := #[.nat 9223372036854775807, .nat 2]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.mulNat 9223372036854775807 2)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "multiplication", "boundary", "heap", "overflow"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.mul]
    requiredExecutedExternals := #[``Nat.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.mul]
    requiredExecutedExternalTrace := some #[``Nat.mul]
    provenance := firProvenance
      "Multiply tagged naturals across the tagged-to-heap result boundary" },
  { id := "nat-mul-multi-limb-growth"
    entry := ``Source.mulNat
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 18446744073709551619]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.mulNat
      340282366920938463463374607431768211473
      18446744073709551619)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "multiplication", "heap", "multi-limb", "growth"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.mul]
    requiredExecutedExternals := #[``Nat.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.mul]
    requiredExecutedExternalTrace := some #[``Nat.mul]
    provenance := firProvenance
      "Multiply two heap naturals into an exact larger multi-limb result" },
  { id := "nat-mul-multi-limb-zero"
    entry := ``Source.mulNat
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 0]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.mulNat
      340282366920938463463374607431768211473
      0)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "multiplication", "heap-input", "multi-limb", "zero", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.mul]
    requiredExecutedExternals := #[``Nat.mul]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.mul]
    requiredExecutedExternalTrace := some #[``Nat.mul]
    provenance := firProvenance
      "Collapse a heap multi-limb natural times zero to a tagged result" },
  { id := "nat-divmod-small"
    entry := ``Source.divModNat
    args := #[.nat 43, .nat 7]
    argSchemas := #[.nat, .nat]
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .nat]
    native := fun _ => natPairDatum (Source.divModNat 43 7)
    tags := #["quick", "external", "pure", "nat", "arithmetic",
      "division", "remainder", "euclidean", "tagged"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Nat.div, ``Nat.mod]
    requiredExecutedExternals := #[``Nat.div, ``Nat.mod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.div, ``Nat.mod]
    requiredExecutedExternalTrace := some #[``Nat.div, ``Nat.mod]
    provenance := firProvenance
      "Return tagged natural quotient and remainder from one input pair" },
  { id := "nat-divmod-multi-limb"
    entry := ``Source.divModNat
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 18446744073709551619]
    argSchemas := #[.nat, .nat]
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .nat]
    native := fun _ => natPairDatum (Source.divModNat
      340282366920938463463374607431768211473
      18446744073709551619)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "division", "remainder", "euclidean", "heap", "multi-limb", "exact"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Nat.div, ``Nat.mod]
    requiredExecutedExternals := #[``Nat.div, ``Nat.mod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.div, ``Nat.mod]
    requiredExecutedExternalTrace := some #[``Nat.div, ``Nat.mod]
    provenance := firProvenance
      "Retain exact multi-limb natural quotient and tagged remainder together" },
  { id := "nat-divmod-zero-divisor"
    entry := ``Source.divModNat
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 0]
    argSchemas := #[.nat, .nat]
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .nat]
    native := fun _ => natPairDatum (Source.divModNat
      340282366920938463463374607431768211473
      0)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "division", "remainder", "euclidean", "heap", "multi-limb",
      "zero-divisor", "boundary"]
    requiredLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfForms := #["ctor", "extern", "fap", "return"]
    requiredExecutedLcnfFormTrace := some pairedExternalCallFormTrace
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``Nat.div, ``Nat.mod]
    requiredExecutedExternals := #[``Nat.div, ``Nat.mod]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.div, ``Nat.mod]
    requiredExecutedExternalTrace := some #[``Nat.div, ``Nat.mod]
    provenance := firProvenance
      "Pin Nat division by zero to zero and remainder by zero to the dividend" },
  exactNatBinaryExternalCase
    "nat-land-multi-limb-to-tagged" ``Source.landNat Source.landNat ``Nat.land
    340282366920938463463374607431768211473
    18446744073709551619
    #["stress", "external", "pure", "nat", "bitwise", "and", "heap-input",
      "multi-limb", "tagged-result", "normalization"]
    "Intersect multi-limb heap naturals into the tagged value one",
  exactNatBinaryExternalCase
    "nat-lor-multi-limb-growth" ``Source.lorNat Source.lorNat ``Nat.lor
    340282366920938463463374607431768211473
    18446744073709551619
    #["stress", "external", "pure", "nat", "bitwise", "or", "heap",
      "multi-limb", "growth"]
    "Union disjoint high limbs and overlapping low bits exactly",
  exactNatBinaryExternalCase
    "nat-xor-multi-limb-mixed" ``Source.xorNat Source.xorNat ``Nat.xor
    340282366920938463463374607431768211473
    18446744073709551619
    #["stress", "external", "pure", "nat", "bitwise", "xor", "heap",
      "multi-limb", "mixed-bits"]
    "Exclusive-or heap naturals with high disjoint and low overlapping bits",
  exactNatBinaryExternalCase
    "nat-xor-multi-limb-cancellation" ``Source.xorNat Source.xorNat ``Nat.xor
    340282366920938463463374607431768211473
    340282366920938463463374607431768211473
    #["stress", "external", "pure", "nat", "bitwise", "xor", "heap-input",
      "multi-limb", "zero", "tagged-result", "normalization"]
    "Cancel equal multi-limb heap naturals to tagged zero",
  exactNatBinaryExternalCase
    "nat-shift-left-tagged-to-heap" ``Source.shiftLeftNat Source.shiftLeftNat
    ``Nat.shiftLeft
    9223372036854775807
    1
    #["stress", "external", "pure", "nat", "bitwise", "shift-left",
      "boundary", "tagged-input", "heap-result", "growth"]
    "Shift the tagged maximum across the heap representation boundary",
  exactNatBinaryExternalCase
    "nat-shift-left-multi-limb-growth" ``Source.shiftLeftNat Source.shiftLeftNat
    ``Nat.shiftLeft
    340282366920938463463374607431768211473
    65
    #["stress", "external", "pure", "nat", "bitwise", "shift-left", "heap",
      "multi-limb", "growth", "cross-limb"]
    "Shift a multi-limb heap natural left across a limb boundary",
  exactNatBinaryExternalCase
    "nat-shift-right-first-heap" ``Source.shiftRightNat Source.shiftRightNat
    ``Nat.shiftRight
    340282366920938463463374607431768211473
    65
    #["stress", "external", "pure", "nat", "bitwise", "shift-right",
      "heap", "multi-limb", "boundary", "heap-result", "cross-limb"]
    "Shift a multi-limb natural down to the first heap value",
  exactNatBinaryExternalCase
    "nat-shift-right-heap-to-tagged" ``Source.shiftRightNat Source.shiftRightNat
    ``Nat.shiftRight
    340282366920938463463374607431768211473
    128
    #["stress", "external", "pure", "nat", "bitwise", "shift-right",
      "heap-input", "multi-limb", "tagged-result", "normalization"]
    "Shift a multi-limb heap natural down to tagged one",
  exactNatBinaryExternalCase
    "nat-shift-right-exhausted" ``Source.shiftRightNat Source.shiftRightNat
    ``Nat.shiftRight
    340282366920938463463374607431768211473
    129
    #["stress", "external", "pure", "nat", "bitwise", "shift-right",
      "heap-input", "multi-limb", "zero", "tagged-result", "boundary"]
    "Shift one bit past a multi-limb natural into tagged zero",
  exactNatBinaryExternalCase
    "nat-shift-right-multi-limb-count" ``Source.shiftRightNat Source.shiftRightNat
    ``Nat.shiftRight
    340282366920938463463374607431768211473
    340282366920938463463374607431768211473
    #["stress", "external", "pure", "nat", "bitwise", "shift-right",
      "heap-input", "multi-limb", "multi-limb-count", "oversized-count",
      "zero", "tagged-result"]
    "Use a multi-limb shift count larger than the value bit width",
  { id := "nat-sub-multi-limb-preserves-heap"
    entry := ``Source.subNat
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 17]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.subNat
      340282366920938463463374607431768211473
      17)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "subtraction", "heap", "multi-limb"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.sub]
    requiredExecutedExternals := #[``Nat.sub]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.sub]
    requiredExecutedExternalTrace := some #[``Nat.sub]
    provenance := firProvenance
      "Subtract 17 from 2^128 + 17 and retain a multi-limb heap result" },
  { id := "nat-sub-multi-limb-equality"
    entry := ``Source.subNat
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.subNat
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "subtraction", "heap", "multi-limb", "equality", "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.sub]
    requiredExecutedExternals := #[``Nat.sub]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.sub]
    requiredExecutedExternalTrace := some #[``Nat.sub]
    provenance := firProvenance
      "Subtract equal multi-limb heap naturals to immediate zero" },
  { id := "nat-sub-multi-limb-underflow"
    entry := ``Source.subNat
    args := #[
      .nat 17,
      .nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.subNat
      17
      340282366920938463463374607431768211473)
    tags := #["stress", "external", "pure", "nat", "arithmetic",
      "subtraction", "heap", "multi-limb", "saturation", "underflow",
      "boundary"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.sub]
    requiredExecutedExternals := #[``Nat.sub]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.sub]
    requiredExecutedExternalTrace := some #[``Nat.sub]
    provenance := firProvenance
      "Saturate tagged-minus-multi-limb Nat subtraction at immediate zero" },
  { id := "nat-dec-eq-multi-limb-true"
    entry := ``Source.decideNatEq
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat, .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideNatEq
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "external", "pure", "nat", "decision", "equality",
      "true", "heap", "multi-limb"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.decEq]
    requiredExecutedExternals := #[``Nat.decEq]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.decEq]
    requiredExecutedExternalTrace := some #[``Nat.decEq]
    provenance := firProvenance
      "Decide equality of identical multi-limb heap naturals" },
  { id := "nat-dec-eq-tagged-heap-false"
    entry := ``Source.decideNatEq
    args := #[.nat 9223372036854775807, .nat 9223372036854775808]
    argSchemas := #[.nat, .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideNatEq
      9223372036854775807 9223372036854775808)
    tags := #["stress", "external", "pure", "nat", "decision", "equality",
      "false", "boundary", "immediate", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.decEq]
    requiredExecutedExternals := #[``Nat.decEq]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.decEq]
    requiredExecutedExternalTrace := some #[``Nat.decEq]
    provenance := firProvenance
      "Reject equality across the tagged-to-heap Nat boundary" },
  { id := "nat-dec-lt-tagged-heap-true"
    entry := ``Source.decideNatLt
    args := #[.nat 9223372036854775807, .nat 9223372036854775808]
    argSchemas := #[.nat, .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideNatLt
      9223372036854775807 9223372036854775808)
    tags := #["stress", "external", "pure", "nat", "decision", "ordering",
      "less-than", "true", "boundary", "immediate", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.decLt]
    requiredExecutedExternals := #[``Nat.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.decLt]
    requiredExecutedExternalTrace := some #[``Nat.decLt]
    provenance := firProvenance
      "Decide strict ordering across the tagged-to-heap Nat boundary" },
  { id := "nat-dec-lt-multi-limb-equality-false"
    entry := ``Source.decideNatLt
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat, .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideNatLt
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "external", "pure", "nat", "decision", "ordering",
      "less-than", "false", "equality", "heap", "multi-limb"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.decLt]
    requiredExecutedExternals := #[``Nat.decLt]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.decLt]
    requiredExecutedExternalTrace := some #[``Nat.decLt]
    provenance := firProvenance
      "Reject strict ordering for equal multi-limb heap naturals" },
  { id := "nat-dec-le-multi-limb-equality-true"
    entry := ``Source.decideNatLe
    args := #[
      .nat 340282366920938463463374607431768211473,
      .nat 340282366920938463463374607431768211473]
    argSchemas := #[.nat, .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideNatLe
      340282366920938463463374607431768211473
      340282366920938463463374607431768211473)
    tags := #["stress", "external", "pure", "nat", "decision", "ordering",
      "less-or-equal", "true", "equality", "heap", "multi-limb"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.decLe]
    requiredExecutedExternals := #[``Nat.decLe]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.decLe]
    requiredExecutedExternalTrace := some #[``Nat.decLe]
    provenance := firProvenance
      "Accept non-strict ordering for equal multi-limb heap naturals" },
  { id := "nat-dec-le-heap-tagged-false"
    entry := ``Source.decideNatLe
    args := #[.nat 9223372036854775808, .nat 9223372036854775807]
    argSchemas := #[.nat, .nat]
    resultSchema := .bool
    native := fun _ => .bool (Source.decideNatLe
      9223372036854775808 9223372036854775807)
    tags := #["stress", "external", "pure", "nat", "decision", "ordering",
      "less-or-equal", "false", "boundary", "immediate", "heap"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormTrace := some externalCallFormTrace
    requiredExternals := #[``Nat.decLe]
    requiredExecutedExternals := #[``Nat.decLe]
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``Nat.decLe]
    requiredExecutedExternalTrace := some #[``Nat.decLe]
    provenance := firProvenance
      "Reject non-strict ordering from the first heap Nat to tagged maximum" },
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``NativeEffects.recordImpl]
    requiredExecutedExternalTrace := some #[``NativeEffects.recordImpl]
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
    tags := #["quick", "effect", "external", "nat", "sequence", "multiplicity"]
    requiredLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfForms := #["fap", "extern", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``NativeEffects.recordImpl]
    requiredExecutedExternals := #[``NativeEffects.recordImpl]
    requiredExecutedExternalCounts :=
      #[{ external := ``NativeEffects.recordImpl, minimum := 2, maximum := some 2 }]
    requiredExecutedExternalTrace :=
      some #[``NativeEffects.recordImpl, ``NativeEffects.recordImpl]
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
      #["stress", "effect", "external", "bytes", "heap", "mutation", "snapshot",
        "sequence", "multiplicity"]
    requiredLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["lit", "fap", "extern", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "extern", minimum := 2, maximum := some 2 },
        { form := "fap", minimum := 2, maximum := some 2 }]
    requiredExternals := #[``NativeEffects.recordByteArrayImpl]
    requiredExecutedExternals := #[``NativeEffects.recordByteArrayImpl]
    requiredExecutedExternalCounts :=
      #[{ external := ``NativeEffects.recordByteArrayImpl, minimum := 2,
          maximum := some 2 }]
    requiredExecutedExternalTrace :=
      some #[``NativeEffects.recordByteArrayImpl, ``NativeEffects.recordByteArrayImpl]
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
  { id := "empty-byte-array-roundtrip"
    entry := ``Source.idByteArray
    args := #[.bytes #[]]
    argSchemas := #[.bytes]
    resultSchema := .bytes
    native := fun _ => byteArrayDatum (Source.idByteArray ⟨#[]⟩)
    tags := #["stress", "bytes", "packed-layout", "empty", "roundtrip", "boundary"]
    requiredLcnfForms := #["inc", "return"]
    requiredExecutedLcnfForms := #["inc", "return"]
    provenance := firProvenance
      "Round-trip the empty packed ByteArray representation without an external" },
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.size]
    requiredExecutedExternalTrace := some #[``ByteArray.size]
    provenance := firProvenance "Controlled ByteArray.size external on packed boundary bytes" },
  { id := "conditional-byte-array-get-taken"
    entry := ``Source.conditionalByteArrayGet
    args := #[.bool true, .bytes #[0, 127, 128, 255]]
    argSchemas := #[.bool, .bytes]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat
        (Source.conditionalByteArrayGet true ⟨#[0, 127, 128, 255]⟩).toNat)
    tags :=
      #["quick", "bytes", "packed-layout", "external", "pure", "control-flow",
        "scalar", "multiplicity"]
    requiredLcnfForms := #["cases", "lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "fap", "extern", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "cases", minimum := 1, maximum := some 1 },
        { form := "fap", minimum := 1, maximum := some 1 },
        { form := "extern", minimum := 1, maximum := some 1 }]
    requiredExecutedLcnfFormTrace := some conditionalExternalTakenFormTrace
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternals := #[``ByteArray.get!]
    requiredExecutedExternalCounts :=
      #[{ external := ``ByteArray.get!, minimum := 1, maximum := some 1 }]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
    provenance := firProvenance
      "Take a runtime Boolean branch and dispatch ByteArray.get! exactly once" },
  { id := "conditional-byte-array-get-skipped"
    entry := ``Source.conditionalByteArrayGet
    args := #[.bool false, .bytes #[0, 127, 128, 255]]
    argSchemas := #[.bool, .bytes]
    resultSchema := .bits 8
    native := fun _ =>
      .bits 8 (UInt64.ofNat
        (Source.conditionalByteArrayGet false ⟨#[0, 127, 128, 255]⟩).toNat)
    tags :=
      #["quick", "bytes", "packed-layout", "external", "pure", "control-flow",
        "scalar", "boundary", "path-exclusion", "multiplicity"]
    requiredLcnfForms := #["cases", "lit", "fap", "extern", "return"]
    requiredExecutedLcnfForms := #["cases", "lit", "return"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "cases", minimum := 1, maximum := some 1 },
        { form := "fap", minimum := 0, maximum := some 0 },
        { form := "extern", minimum := 0, maximum := some 0 }]
    requiredExecutedLcnfFormTrace := some branchFormTrace
    requiredExternals := #[``ByteArray.get!]
    requiredExecutedExternalCounts :=
      #[{ external := ``ByteArray.get!, minimum := 0, maximum := some 0 }]
    requiredExecutedExternalTrace := some #[]
    provenance := firProvenance
      "Skip a retained ByteArray.get! branch and require zero external dispatches" },
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.get!]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.get!]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.get!]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.get!]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.get!]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.get!]
    requiredExecutedExternalTrace := some #[``ByteArray.get!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.set!]
    requiredExecutedExternalTrace := some #[``ByteArray.set!]
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
    requiredExecutedExternalCounts :=
      exactlyOnceExternalCounts #[``ByteArray.set!]
    requiredExecutedExternalTrace := some #[``ByteArray.set!]
    provenance := firProvenance
      "Copy a shared byte array while preserving its original alias through ByteArray.set!" }
]

/-- Source-reachable final-impure forms whose execution coverage the corpus must preserve. -/
def requiredFinalExecutedForms : Array String :=
  #["box", "cases", "ctor", "dec", "del", "extern", "fap", "fvar", "inc", "isShared",
    "join", "jump", "lit", "oproj", "oset", "pap", "return", "setTag", "sproj", "sset",
    "unbox", "uproj", "uset"]

/--
Administrative transitions observed in well-typed LCNF emitted by the source
compiler.  `admin:yield-apply` remains a recognized machine transition, but the
compiler normalizes curried applications into arity-respecting calls rather
than emitting the over-application needed to reach it.
-/
def requiredSourceAdministrativeStepKinds : Array String :=
  #["admin:invoke-name", "admin:invoke-value", "admin:yield-bind",
    "admin:yield-cache", "admin:yield-done"]

#guard cases.all fun validationCase => !validationCase.requiredExecutedLcnfForms.isEmpty

#guard cases.all fun validationCase =>
  validationCase.requiredAdministrativeStepKinds.all fun kind =>
    validationCase.requiredAdministrativeStepKinds.foldl
      (fun count candidate => if candidate == kind then count + 1 else count) 0 == 1

#guard cases.all fun validationCase =>
  validationCase.requiredAdministrativeStepKinds.all
    requiredSourceAdministrativeStepKinds.contains

#guard requiredSourceAdministrativeStepKinds.all fun kind =>
  cases.any fun validationCase =>
    validationCase.requiredAdministrativeStepKinds.contains kind

#guard cases.all fun validationCase =>
  validationCase.effectProjections.all fun projection =>
    validationCase.requiredExternals.contains projection.external &&
    validationCase.requiredExecutedExternals.contains projection.external

#guard cases.all fun validationCase =>
  match validationCase.requiredExecutedLcnfFormTrace with
  | none => true
  | some trace =>
      validationCase.requiredExecutedLcnfForms.all trace.contains &&
      validationCase.requiredExecutedLcnfFormCounts.all fun requirement =>
        let observed := trace.foldl (init := 0) fun count form =>
          if form == requirement.form then count + 1 else count
        observed == requirement.minimum &&
          requirement.maximum == some observed

#guard cases.all fun validationCase =>
  validationCase.requiredExecutedExternalCounts.all fun requirement =>
    requirement.maximum == some requirement.minimum

#guard cases.all fun validationCase =>
  validationCase.requiredExternals.all fun external =>
    validationCase.requiredExecutedExternalCounts.any fun requirement =>
      requirement.external == external

#guard cases.all fun validationCase =>
  validationCase.requiredExternals.isEmpty ||
    validationCase.requiredExecutedExternalTrace.isSome

#guard cases.all fun validationCase =>
  match validationCase.requiredExecutedExternalTrace with
  | none => true
  | some trace =>
      trace.all validationCase.requiredExecutedExternals.contains &&
      validationCase.requiredExecutedExternals.all trace.contains &&
      validationCase.requiredExecutedExternalCounts.all fun requirement =>
        let observed := trace.foldl (init := 0) fun count external =>
          if external == requirement.external then count + 1 else count
        observed == requirement.minimum &&
          requirement.maximum == some observed

#guard requiredFinalExecutedForms.all fun form =>
  cases.any fun validationCase => validationCase.requiredExecutedLcnfForms.contains form

def findCase? (id : String) : Option Case :=
  cases.find? (·.id == id)

def caseIds : Array String :=
  cases.map (·.id)

def descriptors : Array CaseDescriptor :=
  cases.map Case.descriptor

end Fir.Validation.Corpus
