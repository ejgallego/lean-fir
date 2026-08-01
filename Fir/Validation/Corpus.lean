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
def selectCapturedBool (captured : Bool) (_x : Nat) : Nat :=
  if captured then 1 else 0

def capturedBoolPartial (captured : Bool) (x : Nat) : Nat :=
  applyNat (selectCapturedBool captured) x

@[noinline]
def firstGeneric {α : Type} (captured _value : α) : α :=
  captured

@[noinline]
def applyGeneric {α : Type} (f : α → α) (value : α) : α :=
  f value

def capturedUInt8Partial (captured value : UInt8) : UInt8 :=
  applyGeneric (firstGeneric captured) value

def capturedUInt16Partial (captured value : UInt16) : UInt16 :=
  applyGeneric (firstGeneric captured) value

def capturedUInt32Partial (captured value : UInt32) : UInt32 :=
  applyGeneric (firstGeneric captured) value

def capturedUInt64Partial (captured value : UInt64) : UInt64 :=
  applyGeneric (firstGeneric captured) value

def capturedUSizePartial (captured value : USize) : USize :=
  applyGeneric (firstGeneric captured) value

def capturedInt8Partial (captured value : Int8) : Int8 :=
  applyGeneric (firstGeneric captured) value

def capturedInt16Partial (captured value : Int16) : Int16 :=
  applyGeneric (firstGeneric captured) value

def capturedInt32Partial (captured value : Int32) : Int32 :=
  applyGeneric (firstGeneric captured) value

def capturedInt64Partial (captured value : Int64) : Int64 :=
  applyGeneric (firstGeneric captured) value

def capturedISizePartial (captured value : ISize) : ISize :=
  applyGeneric (firstGeneric captured) value

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

@[noinline]
def addInt8 (left right : Int8) : Int8 :=
  Int8.add left right

@[noinline]
def subInt8 (left right : Int8) : Int8 :=
  Int8.sub left right

@[noinline]
def mulInt8 (left right : Int8) : Int8 :=
  Int8.mul left right

@[noinline]
def divInt8 (left right : Int8) : Int8 :=
  Int8.div left right

@[noinline]
def modInt8 (left right : Int8) : Int8 :=
  Int8.mod left right

@[noinline]
def landInt8 (left right : Int8) : Int8 :=
  Int8.land left right

@[noinline]
def lorInt8 (left right : Int8) : Int8 :=
  Int8.lor left right

@[noinline]
def xorInt8 (left right : Int8) : Int8 :=
  Int8.xor left right

@[noinline]
def shiftLeftInt8 (value count : Int8) : Int8 :=
  Int8.shiftLeft value count

@[noinline]
def shiftRightInt8 (value count : Int8) : Int8 :=
  Int8.shiftRight value count

@[noinline]
def complementInt8 (value : Int8) : Int8 :=
  Int8.complement value

@[noinline]
def negInt8 (value : Int8) : Int8 :=
  Int8.neg value

@[noinline]
def absInt8 (value : Int8) : Int8 :=
  Int8.abs value

@[noinline]
def decideInt8Eq (left right : Int8) : Bool :=
  decide (left = right)

@[noinline]
def decideInt8Lt (left right : Int8) : Bool :=
  decide (left < right)

@[noinline]
def decideInt8Le (left right : Int8) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToInt8 (value : Nat) : Int8 :=
  Int8.ofNat value

@[noinline]
def intToInt8 (value : Int) : Int8 :=
  Int8.ofInt value

@[noinline]
def int8ToInt (value : Int8) : Int :=
  Int8.toInt value

@[noinline]
def addInt16 (left right : Int16) : Int16 :=
  Int16.add left right

@[noinline]
def subInt16 (left right : Int16) : Int16 :=
  Int16.sub left right

@[noinline]
def mulInt16 (left right : Int16) : Int16 :=
  Int16.mul left right

@[noinline]
def divInt16 (left right : Int16) : Int16 :=
  Int16.div left right

@[noinline]
def modInt16 (left right : Int16) : Int16 :=
  Int16.mod left right

@[noinline]
def landInt16 (left right : Int16) : Int16 :=
  Int16.land left right

@[noinline]
def lorInt16 (left right : Int16) : Int16 :=
  Int16.lor left right

@[noinline]
def xorInt16 (left right : Int16) : Int16 :=
  Int16.xor left right

@[noinline]
def shiftLeftInt16 (value count : Int16) : Int16 :=
  Int16.shiftLeft value count

@[noinline]
def shiftRightInt16 (value count : Int16) : Int16 :=
  Int16.shiftRight value count

@[noinline]
def complementInt16 (value : Int16) : Int16 :=
  Int16.complement value

@[noinline]
def negInt16 (value : Int16) : Int16 :=
  Int16.neg value

@[noinline]
def absInt16 (value : Int16) : Int16 :=
  Int16.abs value

@[noinline]
def decideInt16Eq (left right : Int16) : Bool :=
  decide (left = right)

@[noinline]
def decideInt16Lt (left right : Int16) : Bool :=
  decide (left < right)

@[noinline]
def decideInt16Le (left right : Int16) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToInt16 (value : Nat) : Int16 :=
  Int16.ofNat value

@[noinline]
def intToInt16 (value : Int) : Int16 :=
  Int16.ofInt value

@[noinline]
def int16ToInt (value : Int16) : Int :=
  Int16.toInt value

@[noinline]
def int8ToInt16 (value : Int8) : Int16 :=
  Int8.toInt16 value

@[noinline]
def int16ToInt8 (value : Int16) : Int8 :=
  Int16.toInt8 value

@[noinline]
def addInt32 (left right : Int32) : Int32 :=
  Int32.add left right

@[noinline]
def subInt32 (left right : Int32) : Int32 :=
  Int32.sub left right

@[noinline]
def mulInt32 (left right : Int32) : Int32 :=
  Int32.mul left right

@[noinline]
def divInt32 (left right : Int32) : Int32 :=
  Int32.div left right

@[noinline]
def modInt32 (left right : Int32) : Int32 :=
  Int32.mod left right

@[noinline]
def landInt32 (left right : Int32) : Int32 :=
  Int32.land left right

@[noinline]
def lorInt32 (left right : Int32) : Int32 :=
  Int32.lor left right

@[noinline]
def xorInt32 (left right : Int32) : Int32 :=
  Int32.xor left right

@[noinline]
def shiftLeftInt32 (value count : Int32) : Int32 :=
  Int32.shiftLeft value count

@[noinline]
def shiftRightInt32 (value count : Int32) : Int32 :=
  Int32.shiftRight value count

@[noinline]
def complementInt32 (value : Int32) : Int32 :=
  Int32.complement value

@[noinline]
def negInt32 (value : Int32) : Int32 :=
  Int32.neg value

@[noinline]
def absInt32 (value : Int32) : Int32 :=
  Int32.abs value

@[noinline]
def decideInt32Eq (left right : Int32) : Bool :=
  decide (left = right)

@[noinline]
def decideInt32Lt (left right : Int32) : Bool :=
  decide (left < right)

@[noinline]
def decideInt32Le (left right : Int32) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToInt32 (value : Nat) : Int32 :=
  Int32.ofNat value

@[noinline]
def intToInt32 (value : Int) : Int32 :=
  Int32.ofInt value

@[noinline]
def int32ToInt (value : Int32) : Int :=
  Int32.toInt value

@[noinline]
def int8ToInt32 (value : Int8) : Int32 :=
  Int8.toInt32 value

@[noinline]
def int16ToInt32 (value : Int16) : Int32 :=
  Int16.toInt32 value

@[noinline]
def int32ToInt8 (value : Int32) : Int8 :=
  Int32.toInt8 value

@[noinline]
def int32ToInt16 (value : Int32) : Int16 :=
  Int32.toInt16 value

@[noinline]
def addInt64 (left right : Int64) : Int64 :=
  Int64.add left right

@[noinline]
def subInt64 (left right : Int64) : Int64 :=
  Int64.sub left right

@[noinline]
def mulInt64 (left right : Int64) : Int64 :=
  Int64.mul left right

@[noinline]
def divInt64 (left right : Int64) : Int64 :=
  Int64.div left right

@[noinline]
def modInt64 (left right : Int64) : Int64 :=
  Int64.mod left right

@[noinline]
def landInt64 (left right : Int64) : Int64 :=
  Int64.land left right

@[noinline]
def lorInt64 (left right : Int64) : Int64 :=
  Int64.lor left right

@[noinline]
def xorInt64 (left right : Int64) : Int64 :=
  Int64.xor left right

@[noinline]
def shiftLeftInt64 (value count : Int64) : Int64 :=
  Int64.shiftLeft value count

@[noinline]
def shiftRightInt64 (value count : Int64) : Int64 :=
  Int64.shiftRight value count

@[noinline]
def complementInt64 (value : Int64) : Int64 :=
  Int64.complement value

@[noinline]
def negInt64 (value : Int64) : Int64 :=
  Int64.neg value

@[noinline]
def absInt64 (value : Int64) : Int64 :=
  Int64.abs value

@[noinline]
def decideInt64Eq (left right : Int64) : Bool :=
  decide (left = right)

@[noinline]
def decideInt64Lt (left right : Int64) : Bool :=
  decide (left < right)

@[noinline]
def decideInt64Le (left right : Int64) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToInt64 (value : Nat) : Int64 :=
  Int64.ofNat value

@[noinline]
def intToInt64 (value : Int) : Int64 :=
  Int64.ofInt value

@[noinline]
def int64ToInt (value : Int64) : Int :=
  Int64.toInt value

@[noinline]
def int8ToInt64 (value : Int8) : Int64 :=
  Int8.toInt64 value

@[noinline]
def int16ToInt64 (value : Int16) : Int64 :=
  Int16.toInt64 value

@[noinline]
def int32ToInt64 (value : Int32) : Int64 :=
  Int32.toInt64 value

@[noinline]
def int64ToInt8 (value : Int64) : Int8 :=
  Int64.toInt8 value

@[noinline]
def int64ToInt16 (value : Int64) : Int16 :=
  Int64.toInt16 value

@[noinline]
def int64ToInt32 (value : Int64) : Int32 :=
  Int64.toInt32 value

@[noinline]
def addISize (left right : ISize) : ISize :=
  ISize.add left right

@[noinline]
def subISize (left right : ISize) : ISize :=
  ISize.sub left right

@[noinline]
def mulISize (left right : ISize) : ISize :=
  ISize.mul left right

@[noinline]
def divISize (left right : ISize) : ISize :=
  ISize.div left right

@[noinline]
def modISize (left right : ISize) : ISize :=
  ISize.mod left right

@[noinline]
def landISize (left right : ISize) : ISize :=
  ISize.land left right

@[noinline]
def lorISize (left right : ISize) : ISize :=
  ISize.lor left right

@[noinline]
def xorISize (left right : ISize) : ISize :=
  ISize.xor left right

@[noinline]
def shiftLeftISize (value count : ISize) : ISize :=
  ISize.shiftLeft value count

@[noinline]
def shiftRightISize (value count : ISize) : ISize :=
  ISize.shiftRight value count

@[noinline]
def complementISize (value : ISize) : ISize :=
  ISize.complement value

@[noinline]
def negISize (value : ISize) : ISize :=
  ISize.neg value

@[noinline]
def absISize (value : ISize) : ISize :=
  ISize.abs value

@[noinline]
def decideISizeEq (left right : ISize) : Bool :=
  decide (left = right)

@[noinline]
def decideISizeLt (left right : ISize) : Bool :=
  decide (left < right)

@[noinline]
def decideISizeLe (left right : ISize) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToISize (value : Nat) : ISize :=
  ISize.ofNat value

@[noinline]
def intToISize (value : Int) : ISize :=
  ISize.ofInt value

@[noinline]
def isizeToInt (value : ISize) : Int :=
  ISize.toInt value

@[noinline]
def int8ToISize (value : Int8) : ISize :=
  Int8.toISize value

@[noinline]
def int16ToISize (value : Int16) : ISize :=
  Int16.toISize value

@[noinline]
def int32ToISize (value : Int32) : ISize :=
  Int32.toISize value

@[noinline]
def int64ToISize (value : Int64) : ISize :=
  Int64.toISize value

@[noinline]
def isizeToInt8 (value : ISize) : Int8 :=
  ISize.toInt8 value

@[noinline]
def isizeToInt16 (value : ISize) : Int16 :=
  ISize.toInt16 value

@[noinline]
def isizeToInt32 (value : ISize) : Int32 :=
  ISize.toInt32 value

@[noinline]
def isizeToInt64 (value : ISize) : Int64 :=
  ISize.toInt64 value

def idUInt8 (value : UInt8) : UInt8 :=
  value

def idUInt16 (value : UInt16) : UInt16 :=
  value

@[noinline]
def addUInt8 (left right : UInt8) : UInt8 :=
  UInt8.add left right

@[noinline]
def subUInt8 (left right : UInt8) : UInt8 :=
  UInt8.sub left right

@[noinline]
def mulUInt8 (left right : UInt8) : UInt8 :=
  UInt8.mul left right

@[noinline]
def divUInt8 (left right : UInt8) : UInt8 :=
  UInt8.div left right

@[noinline]
def modUInt8 (left right : UInt8) : UInt8 :=
  UInt8.mod left right

@[noinline]
def landUInt8 (left right : UInt8) : UInt8 :=
  UInt8.land left right

@[noinline]
def lorUInt8 (left right : UInt8) : UInt8 :=
  UInt8.lor left right

@[noinline]
def xorUInt8 (left right : UInt8) : UInt8 :=
  UInt8.xor left right

@[noinline]
def shiftLeftUInt8 (value count : UInt8) : UInt8 :=
  UInt8.shiftLeft value count

@[noinline]
def shiftRightUInt8 (value count : UInt8) : UInt8 :=
  UInt8.shiftRight value count

@[noinline]
def complementUInt8 (value : UInt8) : UInt8 :=
  UInt8.complement value

@[noinline]
def negUInt8 (value : UInt8) : UInt8 :=
  UInt8.neg value

@[noinline]
def decideUInt8Eq (left right : UInt8) : Bool :=
  decide (left = right)

@[noinline]
def decideUInt8Lt (left right : UInt8) : Bool :=
  decide (left < right)

@[noinline]
def decideUInt8Le (left right : UInt8) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToUInt8 (value : Nat) : UInt8 :=
  UInt8.ofNat value

@[noinline]
def uint8ToNat (value : UInt8) : Nat :=
  UInt8.toNat value

@[noinline]
def uint8ToUInt16 (value : UInt8) : UInt16 :=
  UInt8.toUInt16 value

@[noinline]
def uint8ToUInt32 (value : UInt8) : UInt32 :=
  UInt8.toUInt32 value

@[noinline]
def uint8ToUInt64 (value : UInt8) : UInt64 :=
  UInt8.toUInt64 value

@[noinline]
def uint8ToUSize (value : UInt8) : USize :=
  UInt8.toUSize value

@[noinline]
def addUInt16 (left right : UInt16) : UInt16 :=
  UInt16.add left right

@[noinline]
def subUInt16 (left right : UInt16) : UInt16 :=
  UInt16.sub left right

@[noinline]
def mulUInt16 (left right : UInt16) : UInt16 :=
  UInt16.mul left right

@[noinline]
def divUInt16 (left right : UInt16) : UInt16 :=
  UInt16.div left right

@[noinline]
def modUInt16 (left right : UInt16) : UInt16 :=
  UInt16.mod left right

@[noinline]
def landUInt16 (left right : UInt16) : UInt16 :=
  UInt16.land left right

@[noinline]
def lorUInt16 (left right : UInt16) : UInt16 :=
  UInt16.lor left right

@[noinline]
def xorUInt16 (left right : UInt16) : UInt16 :=
  UInt16.xor left right

@[noinline]
def shiftLeftUInt16 (value count : UInt16) : UInt16 :=
  UInt16.shiftLeft value count

@[noinline]
def shiftRightUInt16 (value count : UInt16) : UInt16 :=
  UInt16.shiftRight value count

@[noinline]
def complementUInt16 (value : UInt16) : UInt16 :=
  UInt16.complement value

@[noinline]
def negUInt16 (value : UInt16) : UInt16 :=
  UInt16.neg value

@[noinline]
def decideUInt16Eq (left right : UInt16) : Bool :=
  decide (left = right)

@[noinline]
def decideUInt16Lt (left right : UInt16) : Bool :=
  decide (left < right)

@[noinline]
def decideUInt16Le (left right : UInt16) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToUInt16 (value : Nat) : UInt16 :=
  UInt16.ofNat value

@[noinline]
def uint16ToNat (value : UInt16) : Nat :=
  UInt16.toNat value

@[noinline]
def uint16ToUInt8 (value : UInt16) : UInt8 :=
  UInt16.toUInt8 value

@[noinline]
def uint16ToUInt32 (value : UInt16) : UInt32 :=
  UInt16.toUInt32 value

@[noinline]
def uint16ToUInt64 (value : UInt16) : UInt64 :=
  UInt16.toUInt64 value

@[noinline]
def uint16ToUSize (value : UInt16) : USize :=
  UInt16.toUSize value

def idUInt32 (value : UInt32) : UInt32 :=
  value

@[noinline]
def addUInt32 (left right : UInt32) : UInt32 :=
  UInt32.add left right

@[noinline]
def subUInt32 (left right : UInt32) : UInt32 :=
  UInt32.sub left right

@[noinline]
def mulUInt32 (left right : UInt32) : UInt32 :=
  UInt32.mul left right

@[noinline]
def divUInt32 (left right : UInt32) : UInt32 :=
  UInt32.div left right

@[noinline]
def modUInt32 (left right : UInt32) : UInt32 :=
  UInt32.mod left right

@[noinline]
def landUInt32 (left right : UInt32) : UInt32 :=
  UInt32.land left right

@[noinline]
def lorUInt32 (left right : UInt32) : UInt32 :=
  UInt32.lor left right

@[noinline]
def xorUInt32 (left right : UInt32) : UInt32 :=
  UInt32.xor left right

@[noinline]
def shiftLeftUInt32 (value count : UInt32) : UInt32 :=
  UInt32.shiftLeft value count

@[noinline]
def shiftRightUInt32 (value count : UInt32) : UInt32 :=
  UInt32.shiftRight value count

@[noinline]
def complementUInt32 (value : UInt32) : UInt32 :=
  UInt32.complement value

@[noinline]
def negUInt32 (value : UInt32) : UInt32 :=
  UInt32.neg value

@[noinline]
def decideUInt32Eq (left right : UInt32) : Bool :=
  decide (left = right)

@[noinline]
def decideUInt32Lt (left right : UInt32) : Bool :=
  decide (left < right)

@[noinline]
def decideUInt32Le (left right : UInt32) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToUInt32 (value : Nat) : UInt32 :=
  UInt32.ofNat value

@[noinline]
def uint32ToNat (value : UInt32) : Nat :=
  UInt32.toNat value

@[noinline]
def uint32ToUInt8 (value : UInt32) : UInt8 :=
  UInt32.toUInt8 value

@[noinline]
def uint32ToUInt16 (value : UInt32) : UInt16 :=
  UInt32.toUInt16 value

@[noinline]
def uint32ToUInt64 (value : UInt32) : UInt64 :=
  UInt32.toUInt64 value

@[noinline]
def uint32ToUSize (value : UInt32) : USize :=
  UInt32.toUSize value

def idUInt64 (value : UInt64) : UInt64 :=
  value

@[noinline]
def addUInt64 (left right : UInt64) : UInt64 :=
  UInt64.add left right

@[noinline]
def subUInt64 (left right : UInt64) : UInt64 :=
  UInt64.sub left right

@[noinline]
def mulUInt64 (left right : UInt64) : UInt64 :=
  UInt64.mul left right

@[noinline]
def divUInt64 (left right : UInt64) : UInt64 :=
  UInt64.div left right

@[noinline]
def modUInt64 (left right : UInt64) : UInt64 :=
  UInt64.mod left right

@[noinline]
def landUInt64 (left right : UInt64) : UInt64 :=
  UInt64.land left right

@[noinline]
def lorUInt64 (left right : UInt64) : UInt64 :=
  UInt64.lor left right

@[noinline]
def xorUInt64 (left right : UInt64) : UInt64 :=
  UInt64.xor left right

@[noinline]
def shiftLeftUInt64 (value count : UInt64) : UInt64 :=
  UInt64.shiftLeft value count

@[noinline]
def shiftRightUInt64 (value count : UInt64) : UInt64 :=
  UInt64.shiftRight value count

@[noinline]
def complementUInt64 (value : UInt64) : UInt64 :=
  UInt64.complement value

@[noinline]
def negUInt64 (value : UInt64) : UInt64 :=
  UInt64.neg value

@[noinline]
def decideUInt64Eq (left right : UInt64) : Bool :=
  decide (left = right)

@[noinline]
def decideUInt64Lt (left right : UInt64) : Bool :=
  decide (left < right)

@[noinline]
def decideUInt64Le (left right : UInt64) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToUInt64 (value : Nat) : UInt64 :=
  UInt64.ofNat value

@[noinline]
def uint64ToNat (value : UInt64) : Nat :=
  UInt64.toNat value

@[noinline]
def uint64ToUInt8 (value : UInt64) : UInt8 :=
  UInt64.toUInt8 value

@[noinline]
def uint64ToUInt16 (value : UInt64) : UInt16 :=
  UInt64.toUInt16 value

@[noinline]
def uint64ToUInt32 (value : UInt64) : UInt32 :=
  UInt64.toUInt32 value

@[noinline]
def uint64ToUSize (value : UInt64) : USize :=
  UInt64.toUSize value

@[noinline]
def addUSize (left right : USize) : USize :=
  USize.add left right

@[noinline]
def subUSize (left right : USize) : USize :=
  USize.sub left right

@[noinline]
def mulUSize (left right : USize) : USize :=
  USize.mul left right

@[noinline]
def divUSize (left right : USize) : USize :=
  USize.div left right

@[noinline]
def modUSize (left right : USize) : USize :=
  USize.mod left right

@[noinline]
def landUSize (left right : USize) : USize :=
  USize.land left right

@[noinline]
def lorUSize (left right : USize) : USize :=
  USize.lor left right

@[noinline]
def xorUSize (left right : USize) : USize :=
  USize.xor left right

@[noinline]
def shiftLeftUSize (value count : USize) : USize :=
  USize.shiftLeft value count

@[noinline]
def shiftRightUSize (value count : USize) : USize :=
  USize.shiftRight value count

@[noinline]
def complementUSize (value : USize) : USize :=
  USize.complement value

@[noinline]
def negUSize (value : USize) : USize :=
  USize.neg value

@[noinline]
def decideUSizeEq (left right : USize) : Bool :=
  decide (left = right)

@[noinline]
def decideUSizeLt (left right : USize) : Bool :=
  decide (left < right)

@[noinline]
def decideUSizeLe (left right : USize) : Bool :=
  decide (left ≤ right)

@[noinline]
def natToUSize (value : Nat) : USize :=
  USize.ofNat value

@[noinline]
def usizeToNat (value : USize) : Nat :=
  USize.toNat value

@[noinline]
def usizeToUInt8 (value : USize) : UInt8 :=
  USize.toUInt8 value

@[noinline]
def usizeToUInt16 (value : USize) : UInt16 :=
  USize.toUInt16 value

@[noinline]
def usizeToUInt32 (value : USize) : UInt32 :=
  USize.toUInt32 value

@[noinline]
def usizeToUInt64 (value : USize) : UInt64 :=
  USize.toUInt64 value

def maxUInt8 : UInt8 := 255

def maxUInt16 : UInt16 := 65535

def maxUInt32 : UInt32 := 4294967295

def maxUInt64 : UInt64 := 18446744073709551615

def maxUSize : USize := 18446744073709551615

def resultInt8Minimum : Int8 := ⟨0x80⟩

def resultInt8NegativeOne : Int8 := ⟨0xff⟩

def resultInt8Zero : Int8 := ⟨0⟩

def resultInt8Maximum : Int8 := ⟨0x7f⟩

def resultInt16Minimum : Int16 := ⟨0x8000⟩

def resultInt16NegativeOne : Int16 := ⟨0xffff⟩

def resultInt16Zero : Int16 := ⟨0⟩

def resultInt16Maximum : Int16 := ⟨0x7fff⟩

def resultInt32Minimum : Int32 := ⟨0x80000000⟩

def resultInt32NegativeOne : Int32 := ⟨0xffffffff⟩

def resultInt32Zero : Int32 := ⟨0⟩

def resultInt32Maximum : Int32 := ⟨0x7fffffff⟩

def resultInt64Minimum : Int64 := ⟨0x8000000000000000⟩

def resultInt64NegativeOne : Int64 := ⟨0xffffffffffffffff⟩

def resultInt64Zero : Int64 := ⟨0⟩

def resultInt64Maximum : Int64 := ⟨0x7fffffffffffffff⟩

def resultISizeMinimum : ISize := ⟨0x8000000000000000⟩

def resultISizeNegativeOne : ISize := ⟨0xffffffffffffffff⟩

def resultISizeZero : ISize := ⟨0⟩

def resultISizeMaximum : ISize := ⟨0x7fffffffffffffff⟩

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

/--
An internal closure result spanning every final-LCNF storage lane.  Validation
observes only its `argument` projection so this ownership regression does not
depend on the general mixed-constructor wire codec.
-/
structure MixedClosureCapture where
  natural : Nat
  text : String
  bytes : ByteArray
  usize : USize
  word : UInt32
  single : Float32
  double : Float
  argument : Nat

@[noinline]
def applyMixedClosureCapture
    (f : Nat → MixedClosureCapture) (argument : Nat) : Nat :=
  (f argument).argument

@[noinline]
def applyMixedClosureCaptureTwice
    (f : Nat → MixedClosureCapture) (first second : Nat) : Nat × Nat :=
  ((f first).argument, (f second).argument)

def captureMixedClosure
    (natural : Nat) (text : String) (bytes : ByteArray) (usize : USize)
    (word : UInt32) (single : Float32) (double : Float) (argument : Nat) : Nat :=
  applyMixedClosureCapture
    (fun capturedArgument =>
      { natural, text, bytes, usize, word, single, double,
        argument := capturedArgument })
    argument

def captureMixedClosureTwice
    (natural : Nat) (text : String) (bytes : ByteArray) (usize : USize)
    (word : UInt32) (single : Float32) (double : Float)
    (first second : Nat) : Nat × Nat :=
  applyMixedClosureCaptureTwice
    (fun capturedArgument =>
      { natural, text, bytes, usize, word, single, double,
        argument := capturedArgument })
    first second

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
def shiftLeftInt (value : Int) (count : Nat) : Int :=
  Int.shiftLeft value count

@[noinline]
def shiftRightInt (value : Int) (count : Nat) : Int :=
  Int.shiftRight value count

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

private def float32Datum (value : Float32) : ValidationDatum :=
  .bits 32 (UInt64.ofNat value.toBits.toNat)

private def float64Datum (value : Float) : ValidationDatum :=
  .bits 64 value.toBits

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

private def mixedClosureSingle : Float32 :=
  Float32.ofBits 0x7fc12345

private def mixedClosureDouble : Float :=
  Float.ofBits 0x8000000000000000

private def mixedClosureBaseArgs : Array ValidationDatum :=
  #[.nat Source.largeNat, .string mixedLayoutText, byteArrayDatum mixedLayoutBytes,
    .usize (UInt64.ofNat Source.maxUSize.toNat), .bits 32 0xdeadbeef,
    float32Datum mixedClosureSingle, float64Datum mixedClosureDouble]

private def mixedClosureBaseArgSchemas : Array ValidationSchema :=
  #[.nat, .string, .bytes, .usize, .bits 32, .float32, .float64]

private def mixedClosureOnceArgs : Array ValidationDatum :=
  mixedClosureBaseArgs.push (.nat 99)

private def mixedClosureOnceArgSchemas : Array ValidationSchema :=
  mixedClosureBaseArgSchemas.push .nat

private def mixedClosureTwiceArgs : Array ValidationDatum :=
  mixedClosureBaseArgs
    |>.push (.nat 17)
    |>.push (.nat 340282366920938463463374607431768211473)

private def mixedClosureTwiceArgSchemas : Array ValidationSchema :=
  mixedClosureBaseArgSchemas.push .nat |>.push .nat

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

private def capturedBoolPartialFormTrace : Array String :=
  #["box", "pap", "fap", "fvar", "unbox", "fap", "fap", "cases", "lit",
    "return", "return", "dec", "return", "return", "return"]

private def capturedBoolPartialFormCounts : Array ExecutedFormCountRequirement :=
  #[{ form := "box", minimum := 1, maximum := some 1 },
    { form := "cases", minimum := 1, maximum := some 1 },
    { form := "dec", minimum := 1, maximum := some 1 },
    { form := "fap", minimum := 3, maximum := some 3 },
    { form := "fvar", minimum := 1, maximum := some 1 },
    { form := "lit", minimum := 1, maximum := some 1 },
    { form := "pap", minimum := 1, maximum := some 1 },
    { form := "return", minimum := 5, maximum := some 5 },
    { form := "unbox", minimum := 1, maximum := some 1 }]

private def capturedBoolPartialAdministrativeKinds : Array String :=
  #["admin:invoke-name", "admin:invoke-value", "admin:yield-bind",
    "admin:yield-done"]

private def capturedGenericScalarPartialFormTrace : Array String :=
  #["box", "pap", "box", "fap", "fvar", "fap", "fap", "inc", "return",
    "return", "dec", "dec", "return", "return", "unbox", "dec", "return"]

private def capturedGenericScalarPartialFormCounts :
    Array ExecutedFormCountRequirement :=
  #[{ form := "box", minimum := 2, maximum := some 2 },
    { form := "dec", minimum := 3, maximum := some 3 },
    { form := "fap", minimum := 3, maximum := some 3 },
    { form := "fvar", minimum := 1, maximum := some 1 },
    { form := "inc", minimum := 1, maximum := some 1 },
    { form := "pap", minimum := 1, maximum := some 1 },
    { form := "return", minimum := 5, maximum := some 5 },
    { form := "unbox", minimum := 1, maximum := some 1 }]

private def capturedGenericScalarPartialAdministrativeKinds : Array String :=
  #["admin:invoke-name", "admin:invoke-value", "admin:yield-bind",
    "admin:yield-done"]

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

private def mixedClosureOnceFormTrace : Array String :=
  #["box", "box", "box", "box", "pap", "fap", "fvar",
    "unbox", "dec", "unbox", "dec", "unbox", "dec", "unbox", "dec",
    "fap", "ctor", "uset", "sset", "sset", "sset", "return", "return",
    "oproj", "inc", "dec", "return", "return"]

private def mixedClosureTwiceFormTrace : Array String :=
  #["box", "box", "box", "box", "pap", "fap", "inc", "fvar",
    "unbox", "dec", "unbox", "dec", "unbox", "dec", "unbox", "dec",
    "fap", "ctor", "uset", "sset", "sset", "sset", "return", "return",
    "oproj", "inc", "dec", "fvar",
    "unbox", "dec", "unbox", "dec", "unbox", "dec", "unbox", "dec",
    "fap", "ctor", "uset", "sset", "sset", "sset", "return", "return",
    "oproj", "inc", "dec", "ctor", "return", "return"]

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

private def exactIntNatExternalCase
    (id : String) (entry : Lean.Name) (operation : Int → Nat → Int)
    (external : Lean.Name) (value : Int) (count : Nat) (tags : Array String)
    (note : String) : Case := {
  id
  entry
  args := #[.int value, .nat count]
  argSchemas := #[.int, .nat]
  resultSchema := .int
  native := fun _ => .int (operation value count)
  tags
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private structure FixedWidthCaseCodec (α : Type) where
  schema : ValidationSchema
  datum : α → ValidationDatum
  externalTag : String
  conversionTag : String

private def int8CaseCodec : FixedWidthCaseCodec Int8 where
  schema := .bits 8
  datum value := .bits 8 (UInt64.ofNat value.toUInt8.toNat)
  externalTag := "fixed-width-signed-external"
  conversionTag := "fixed-width-signed-conversion"

private def int16CaseCodec : FixedWidthCaseCodec Int16 where
  schema := .bits 16
  datum value := .bits 16 (UInt64.ofNat value.toUInt16.toNat)
  externalTag := "fixed-width-signed-external"
  conversionTag := "fixed-width-signed-conversion"

private def int32CaseCodec : FixedWidthCaseCodec Int32 where
  schema := .bits 32
  datum value := .bits 32 (UInt64.ofNat value.toUInt32.toNat)
  externalTag := "fixed-width-signed-external"
  conversionTag := "fixed-width-signed-conversion"

private def int64CaseCodec : FixedWidthCaseCodec Int64 where
  schema := .bits 64
  datum value := .bits 64 value.toUInt64
  externalTag := "fixed-width-signed-external"
  conversionTag := "fixed-width-signed-conversion"

private def isizeCaseCodec : FixedWidthCaseCodec ISize where
  schema := .usize
  datum value := .usize value.toUSize.toUInt64
  externalTag := "fixed-width-signed-external"
  conversionTag := "fixed-width-signed-conversion"

private def uint8CaseCodec : FixedWidthCaseCodec UInt8 where
  schema := .bits 8
  datum value := .bits 8 (UInt64.ofNat value.toNat)
  externalTag := "fixed-width-unsigned-external"
  conversionTag := "fixed-width-unsigned-conversion"

private def uint16CaseCodec : FixedWidthCaseCodec UInt16 where
  schema := .bits 16
  datum value := .bits 16 (UInt64.ofNat value.toNat)
  externalTag := "fixed-width-unsigned-external"
  conversionTag := "fixed-width-unsigned-conversion"

private def uint32CaseCodec : FixedWidthCaseCodec UInt32 where
  schema := .bits 32
  datum value := .bits 32 (UInt64.ofNat value.toNat)
  externalTag := "fixed-width-unsigned-external"
  conversionTag := "fixed-width-unsigned-conversion"

private def uint64CaseCodec : FixedWidthCaseCodec UInt64 where
  schema := .bits 64
  datum := .bits 64
  externalTag := "fixed-width-unsigned-external"
  conversionTag := "fixed-width-unsigned-conversion"

private def usizeCaseCodec : FixedWidthCaseCodec USize where
  schema := .usize
  datum value := .usize value.toUInt64
  externalTag := "fixed-width-unsigned-external"
  conversionTag := "fixed-width-unsigned-conversion"

private def exactCapturedFixedWidthEntryCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : α → α → α)
    (captured applied : α) (tags : Array String) (note : String) : Case := {
  id
  entry
  dependencies := #[``Source.firstGeneric, ``Source.applyGeneric]
  args := #[codec.datum captured, codec.datum applied]
  argSchemas := #[codec.schema, codec.schema]
  resultSchema := codec.schema
  native := fun _ => codec.datum (operation captured applied)
  tags := #[
    "quick", "scalar", "closure", "partial-application", "entry-abi",
    "generic-application", "boundary", "wasm-generation-pending"] ++ tags
  requiredLcnfForms := #["box", "dec", "fap", "fvar", "inc", "pap", "return", "unbox"]
  requiredExecutedLcnfForms :=
    #["box", "dec", "fap", "fvar", "inc", "pap", "return", "unbox"]
  requiredExecutedLcnfFormCounts := capturedGenericScalarPartialFormCounts
  requiredExecutedLcnfFormTrace := some capturedGenericScalarPartialFormTrace
  requiredAdministrativeStepKinds := capturedGenericScalarPartialAdministrativeKinds
  provenance := firProvenance note }

private def exactFixedWidthResultCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (value : α) (tags : Array String)
    (note : String) : Case := {
  id
  entry
  resultSchema := codec.schema
  native := fun _ => codec.datum value
  tags := #["quick", "scalar", "result-abi", "literal", "boundary"] ++ tags
  requiredLcnfForms := #["lit", "return"]
  requiredExecutedLcnfForms := #["lit", "return"]
  requiredExecutedLcnfFormCounts :=
    #[{ form := "lit", minimum := 1, maximum := some 1 },
      { form := "return", minimum := 1, maximum := some 1 }]
  requiredExecutedLcnfFormTrace := some #["lit", "return"]
  requiredAdministrativeStepKinds :=
    #["admin:invoke-name", "admin:yield-cache", "admin:yield-done"]
  provenance := firProvenance note }

private def signedFixedWidthEntryCases (codec : FixedWidthCaseCodec α)
    (typeId wasmLane : String) (entry : Lean.Name) (operation : α → α → α)
    (ofInt : Int → α) (minimum maximum : Int) (platformTags : Array String) :
    Array Case :=
  let value := ofInt
  let tags (boundaryTags : Array String) :=
    #[typeId, "signed", wasmLane] ++ platformTags ++ boundaryTags
  #[
    exactCapturedFixedWidthEntryCase codec
      s!"captured-{typeId}-partial-min" entry operation
      (value minimum) (value maximum)
      (tags #["minimum", "negative", "sign-bit", "twos-complement"])
      s!"Capture runner-supplied {typeId} minimum through generic application and return it",
    exactCapturedFixedWidthEntryCase codec
      s!"captured-{typeId}-partial-negative-one" entry operation
      (value (-1)) (value 0)
      (tags #["negative-one", "negative", "sign-bit", "twos-complement"])
      s!"Capture runner-supplied {typeId} negative one through generic application and return it",
    exactCapturedFixedWidthEntryCase codec
      s!"captured-{typeId}-partial-zero" entry operation
      (value 0) (value (-1))
      (tags #["zero"])
      s!"Capture runner-supplied {typeId} zero through generic application and return it",
    exactCapturedFixedWidthEntryCase codec
      s!"captured-{typeId}-partial-max" entry operation
      (value maximum) (value minimum)
      (tags #["maximum"])
      s!"Capture runner-supplied {typeId} maximum through generic application and return it"
  ]

private def signedFixedWidthResultCases (codec : FixedWidthCaseCodec α)
    (typeId wasmLane : String)
    (minimumEntry negativeOneEntry zeroEntry maximumEntry : Lean.Name)
    (ofInt : Int → α) (minimum maximum : Int) (platformTags : Array String) :
    Array Case :=
  let value := ofInt
  let tags (boundaryTags : Array String) :=
    #[typeId, "signed", wasmLane] ++ platformTags ++ boundaryTags
  #[
    exactFixedWidthResultCase codec s!"{typeId}-result-min" minimumEntry
      (value minimum)
      (tags #["minimum", "negative", "sign-bit", "twos-complement"])
      s!"Return the argument-free {typeId} minimum through the signed scalar result ABI",
    exactFixedWidthResultCase codec s!"{typeId}-result-negative-one" negativeOneEntry
      (value (-1))
      (tags #["negative-one", "negative", "sign-bit", "twos-complement"])
      s!"Return argument-free {typeId} negative one through the signed scalar result ABI",
    exactFixedWidthResultCase codec s!"{typeId}-result-zero" zeroEntry
      (value 0) (tags #["zero"])
      s!"Return argument-free {typeId} zero through the signed scalar result ABI",
    exactFixedWidthResultCase codec s!"{typeId}-result-max" maximumEntry
      (value maximum) (tags #["maximum"])
      s!"Return the argument-free {typeId} maximum through the signed scalar result ABI"
  ]

private def exactFixedWidthBinaryExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : α → α → α)
    (external : Lean.Name) (left right : α) (tags : Array String)
    (note : String) : Case := {
  id
  entry
  args := #[codec.datum left, codec.datum right]
  argSchemas := #[codec.schema, codec.schema]
  resultSchema := codec.schema
  native := fun _ => codec.datum (operation left right)
  tags := tags.push codec.externalTag
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactFixedWidthUnaryExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : α → α)
    (external : Lean.Name) (input : α) (tags : Array String) (note : String) :
    Case := {
  id
  entry
  args := #[codec.datum input]
  argSchemas := #[codec.schema]
  resultSchema := codec.schema
  native := fun _ => codec.datum (operation input)
  tags := tags.push codec.externalTag
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactFixedWidthDecisionExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : α → α → Bool)
    (external : Lean.Name) (left right : α) (tags : Array String)
    (note : String) : Case := {
  id
  entry
  args := #[codec.datum left, codec.datum right]
  argSchemas := #[codec.schema, codec.schema]
  resultSchema := .bool
  native := fun _ => .bool (operation left right)
  tags := tags.push codec.externalTag
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactNatToFixedWidthExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : Nat → α)
    (external : Lean.Name) (input : Nat) (tags : Array String) (note : String) :
    Case := {
  id
  entry
  args := #[.nat input]
  argSchemas := #[.nat]
  resultSchema := codec.schema
  native := fun _ => codec.datum (operation input)
  tags := (tags.push codec.conversionTag).push "nat-word-conversion"
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactIntToFixedWidthExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : Int → α)
    (external : Lean.Name) (input : Int) (tags : Array String) (note : String) :
    Case := {
  id
  entry
  args := #[.int input]
  argSchemas := #[.int]
  resultSchema := codec.schema
  native := fun _ => codec.datum (operation input)
  tags := (tags.push codec.conversionTag).push "int-word-conversion"
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactFixedWidthToNatExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : α → Nat)
    (external : Lean.Name) (input : α) (tags : Array String) (note : String) :
    Case := {
  id
  entry
  args := #[codec.datum input]
  argSchemas := #[codec.schema]
  resultSchema := .nat
  native := fun _ => .nat (operation input)
  tags := (tags.push codec.conversionTag).push "nat-word-conversion"
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactFixedWidthToIntExternalCase (codec : FixedWidthCaseCodec α)
    (id : String) (entry : Lean.Name) (operation : α → Int)
    (external : Lean.Name) (input : α) (tags : Array String) (note : String) :
    Case := {
  id
  entry
  args := #[codec.datum input]
  argSchemas := #[codec.schema]
  resultSchema := .int
  native := fun _ => .int (operation input)
  tags := (tags.push codec.conversionTag).push "int-word-conversion"
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactFixedWidthConversionExternalCase
    (sourceCodec : FixedWidthCaseCodec α) (targetCodec : FixedWidthCaseCodec β)
    (id : String) (entry : Lean.Name) (operation : α → β)
    (external : Lean.Name) (input : α) (tags : Array String) (note : String) :
    Case := {
  id
  entry
  args := #[sourceCodec.datum input]
  argSchemas := #[sourceCodec.schema]
  resultSchema := targetCodec.schema
  native := fun _ => targetCodec.datum (operation input)
  tags :=
    (tags.push sourceCodec.conversionTag).push "fixed-width-cross-conversion"
  requiredLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfForms := #["fap", "extern", "return"]
  requiredExecutedLcnfFormTrace := some externalCallFormTrace
  requiredExternals := #[external]
  requiredExecutedExternals := #[external]
  requiredExecutedExternalCounts := exactlyOnceExternalCounts #[external]
  requiredExecutedExternalTrace := some #[external]
  provenance := firProvenance note }

private def exactInt8BinaryExternalCase :=
  exactFixedWidthBinaryExternalCase int8CaseCodec

private def exactInt8UnaryExternalCase :=
  exactFixedWidthUnaryExternalCase int8CaseCodec

private def exactInt8DecisionExternalCase :=
  exactFixedWidthDecisionExternalCase int8CaseCodec

private def exactNatToInt8ExternalCase :=
  exactNatToFixedWidthExternalCase int8CaseCodec

private def exactIntToInt8ExternalCase :=
  exactIntToFixedWidthExternalCase int8CaseCodec

private def exactInt8ToIntExternalCase :=
  exactFixedWidthToIntExternalCase int8CaseCodec

private def exactUInt8BinaryExternalCase :=
  exactFixedWidthBinaryExternalCase uint8CaseCodec

private def exactUInt8UnaryExternalCase :=
  exactFixedWidthUnaryExternalCase uint8CaseCodec

private def exactUInt8DecisionExternalCase :=
  exactFixedWidthDecisionExternalCase uint8CaseCodec

private def exactNatToUInt8ExternalCase :=
  exactNatToFixedWidthExternalCase uint8CaseCodec

private def exactUInt8ToNatExternalCase :=
  exactFixedWidthToNatExternalCase uint8CaseCodec

private def exactUInt16BinaryExternalCase :=
  exactFixedWidthBinaryExternalCase uint16CaseCodec

private def exactUInt16UnaryExternalCase :=
  exactFixedWidthUnaryExternalCase uint16CaseCodec

private def exactUInt16DecisionExternalCase :=
  exactFixedWidthDecisionExternalCase uint16CaseCodec

private def exactNatToUInt16ExternalCase :=
  exactNatToFixedWidthExternalCase uint16CaseCodec

private def exactUInt16ToNatExternalCase :=
  exactFixedWidthToNatExternalCase uint16CaseCodec

private def exactUInt32BinaryExternalCase :=
  exactFixedWidthBinaryExternalCase uint32CaseCodec

private def exactUInt32UnaryExternalCase :=
  exactFixedWidthUnaryExternalCase uint32CaseCodec

private def exactUInt32DecisionExternalCase :=
  exactFixedWidthDecisionExternalCase uint32CaseCodec

private def exactNatToUInt32ExternalCase :=
  exactNatToFixedWidthExternalCase uint32CaseCodec

private def exactUInt32ToNatExternalCase :=
  exactFixedWidthToNatExternalCase uint32CaseCodec

private def exactUInt64BinaryExternalCase :=
  exactFixedWidthBinaryExternalCase uint64CaseCodec

private def exactUInt64UnaryExternalCase :=
  exactFixedWidthUnaryExternalCase uint64CaseCodec

private def exactUInt64DecisionExternalCase :=
  exactFixedWidthDecisionExternalCase uint64CaseCodec

private def exactNatToUInt64ExternalCase :=
  exactNatToFixedWidthExternalCase uint64CaseCodec

private def exactUInt64ToNatExternalCase :=
  exactFixedWidthToNatExternalCase uint64CaseCodec

private def exactUSizeBinaryExternalCase :=
  exactFixedWidthBinaryExternalCase usizeCaseCodec

private def exactUSizeUnaryExternalCase :=
  exactFixedWidthUnaryExternalCase usizeCaseCodec

private def exactUSizeDecisionExternalCase :=
  exactFixedWidthDecisionExternalCase usizeCaseCodec

private def exactNatToUSizeExternalCase :=
  exactNatToFixedWidthExternalCase usizeCaseCodec

private def exactUSizeToNatExternalCase :=
  exactFixedWidthToNatExternalCase usizeCaseCodec

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

private def preConversionCases : Array Case := #[
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
  { id := "captured-bool-partial-true"
    entry := ``Source.capturedBoolPartial
    dependencies := #[``Source.selectCapturedBool, ``Source.applyNat]
    args := #[.bool true, .nat 2]
    argSchemas := #[.bool, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.capturedBoolPartial true 2)
    tags := #[
      "quick", "bool", "closure", "partial-application", "scalar", "boundary",
      "wasm-generation-pending"]
    requiredLcnfForms :=
      #["box", "pap", "fap", "fvar", "unbox", "cases", "lit", "dec", "return"]
    requiredExecutedLcnfForms :=
      #["box", "pap", "fap", "fvar", "unbox", "cases", "lit", "dec", "return"]
    requiredExecutedLcnfFormCounts := capturedBoolPartialFormCounts
    requiredExecutedLcnfFormTrace := some capturedBoolPartialFormTrace
    requiredAdministrativeStepKinds := capturedBoolPartialAdministrativeKinds
    provenance := firProvenance
      "Capture runner-supplied Bool true through the scalar entry ABI" },
  { id := "captured-bool-partial-false"
    entry := ``Source.capturedBoolPartial
    dependencies := #[``Source.selectCapturedBool, ``Source.applyNat]
    args := #[.bool false, .nat 2]
    argSchemas := #[.bool, .nat]
    resultSchema := .nat
    native := fun _ => .nat (Source.capturedBoolPartial false 2)
    tags := #[
      "quick", "bool", "closure", "partial-application", "scalar", "boundary",
      "wasm-generation-pending"]
    requiredLcnfForms :=
      #["box", "pap", "fap", "fvar", "unbox", "cases", "lit", "dec", "return"]
    requiredExecutedLcnfForms :=
      #["box", "pap", "fap", "fvar", "unbox", "cases", "lit", "dec", "return"]
    requiredExecutedLcnfFormCounts := capturedBoolPartialFormCounts
    requiredExecutedLcnfFormTrace := some capturedBoolPartialFormTrace
    requiredAdministrativeStepKinds := capturedBoolPartialAdministrativeKinds
    provenance := firProvenance
      "Capture runner-supplied Bool false through the scalar entry ABI" },
  exactCapturedFixedWidthEntryCase uint8CaseCodec
    "captured-uint8-partial-zero" ``Source.capturedUInt8Partial
    Source.capturedUInt8Partial 0 255
    #["uint8", "unsigned", "zero", "i32"]
    "Capture runner-supplied UInt8 zero through generic application and return it",
  exactCapturedFixedWidthEntryCase uint8CaseCodec
    "captured-uint8-partial-max" ``Source.capturedUInt8Partial
    Source.capturedUInt8Partial 255 0
    #["uint8", "unsigned", "maximum", "i32"]
    "Capture runner-supplied UInt8 maximum through generic application and return it",
  exactCapturedFixedWidthEntryCase uint16CaseCodec
    "captured-uint16-partial-zero" ``Source.capturedUInt16Partial
    Source.capturedUInt16Partial 0 65535
    #["uint16", "unsigned", "zero", "i32"]
    "Capture runner-supplied UInt16 zero through generic application and return it",
  exactCapturedFixedWidthEntryCase uint16CaseCodec
    "captured-uint16-partial-max" ``Source.capturedUInt16Partial
    Source.capturedUInt16Partial 65535 0
    #["uint16", "unsigned", "maximum", "i32"]
    "Capture runner-supplied UInt16 maximum through generic application and return it",
  exactCapturedFixedWidthEntryCase uint32CaseCodec
    "captured-uint32-partial-zero" ``Source.capturedUInt32Partial
    Source.capturedUInt32Partial 0 0xffffffff
    #["uint32", "unsigned", "zero", "i32"]
    "Capture runner-supplied UInt32 zero through generic application and return it",
  exactCapturedFixedWidthEntryCase uint32CaseCodec
    "captured-uint32-partial-max" ``Source.capturedUInt32Partial
    Source.capturedUInt32Partial 0xffffffff 0
    #["uint32", "unsigned", "maximum", "i32"]
    "Capture runner-supplied UInt32 maximum through generic application and return it",
  exactCapturedFixedWidthEntryCase uint64CaseCodec
    "captured-uint64-partial-zero" ``Source.capturedUInt64Partial
    Source.capturedUInt64Partial 0 0xffffffffffffffff
    #["uint64", "unsigned", "zero", "i64"]
    "Capture runner-supplied UInt64 zero through generic application and return it",
  exactCapturedFixedWidthEntryCase uint64CaseCodec
    "captured-uint64-partial-max" ``Source.capturedUInt64Partial
    Source.capturedUInt64Partial 0xffffffffffffffff 0
    #["uint64", "unsigned", "maximum", "i64"]
    "Capture runner-supplied UInt64 maximum through generic application and return it",
  exactCapturedFixedWidthEntryCase usizeCaseCodec
    "captured-usize-partial-zero" ``Source.capturedUSizePartial
    Source.capturedUSizePartial 0 Source.maxUSize
    #["usize", "unsigned", "zero", "i64", "semantic-lean64"]
    "Capture runner-supplied USize zero through generic application and return it",
  exactCapturedFixedWidthEntryCase usizeCaseCodec
    "captured-usize-partial-max" ``Source.capturedUSizePartial
    Source.capturedUSizePartial Source.maxUSize 0
    #["usize", "unsigned", "maximum", "i64", "semantic-lean64"]
    "Capture runner-supplied USize maximum through generic application and return it",
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
  exactUInt8BinaryExternalCase
    "uint8-add-overflow" ``Source.addUInt8 Source.addUInt8 ``UInt8.add 255 1
    #["stress", "scalar", "uint8", "external", "arithmetic", "addition",
      "overflow", "wraparound", "boundary"]
    "Wrap maximum UInt8 plus one to zero through the native runtime external",
  exactUInt8BinaryExternalCase
    "uint8-sub-underflow" ``Source.subUInt8 Source.subUInt8 ``UInt8.sub 0 1
    #["stress", "scalar", "uint8", "external", "arithmetic", "subtraction",
      "underflow", "wraparound", "boundary"]
    "Wrap UInt8 zero minus one to the maximum value",
  exactUInt8BinaryExternalCase
    "uint8-mul-overflow" ``Source.mulUInt8 Source.mulUInt8 ``UInt8.mul 128 2
    #["stress", "scalar", "uint8", "external", "arithmetic", "multiplication",
      "overflow", "wraparound", "boundary"]
    "Discard the high multiplication bit at the exact UInt8 width",
  exactUInt8BinaryExternalCase
    "uint8-div-floor" ``Source.divUInt8 Source.divUInt8 ``UInt8.div 255 3
    #["stress", "scalar", "uint8", "external", "arithmetic", "division",
      "floor", "boundary"]
    "Compute unsigned floor division at the UInt8 maximum",
  exactUInt8BinaryExternalCase
    "uint8-div-zero" ``Source.divUInt8 Source.divUInt8 ``UInt8.div 255 0
    #["stress", "scalar", "uint8", "external", "arithmetic", "division",
      "zero-divisor", "boundary"]
    "Pin total UInt8 division by zero to zero",
  exactUInt8BinaryExternalCase
    "uint8-mod-remainder" ``Source.modUInt8 Source.modUInt8 ``UInt8.mod 255 16
    #["stress", "scalar", "uint8", "external", "arithmetic", "remainder",
      "boundary"]
    "Retain the low four bits as the UInt8 remainder",
  exactUInt8BinaryExternalCase
    "uint8-mod-zero" ``Source.modUInt8 Source.modUInt8 ``UInt8.mod 255 0
    #["stress", "scalar", "uint8", "external", "arithmetic", "remainder",
      "zero-divisor", "boundary"]
    "Pin UInt8 remainder by zero to the dividend",
  exactUInt8BinaryExternalCase
    "uint8-land-mixed" ``Source.landUInt8 Source.landUInt8 ``UInt8.land 0xf0 0x3c
    #["stress", "scalar", "uint8", "external", "bitwise", "and", "mixed-bits"]
    "Intersect mixed UInt8 bit groups exactly",
  exactUInt8BinaryExternalCase
    "uint8-lor-mixed" ``Source.lorUInt8 Source.lorUInt8 ``UInt8.lor 0xc0 0x3c
    #["stress", "scalar", "uint8", "external", "bitwise", "or", "mixed-bits"]
    "Union separated UInt8 bit groups across both nibbles",
  exactUInt8BinaryExternalCase
    "uint8-xor-mixed" ``Source.xorUInt8 Source.xorUInt8 ``UInt8.xor 0xf0 0x3c
    #["stress", "scalar", "uint8", "external", "bitwise", "xor", "mixed-bits"]
    "Exclusive-or mixed UInt8 bit groups exactly",
  exactUInt8BinaryExternalCase
    "uint8-shift-left-count-8" ``Source.shiftLeftUInt8 Source.shiftLeftUInt8
    ``UInt8.shiftLeft 0x81 8
    #["stress", "scalar", "uint8", "external", "bitwise", "shift-left",
      "masked-count", "boundary"]
    "Mask a UInt8 left-shift count of eight to zero",
  exactUInt8BinaryExternalCase
    "uint8-shift-left-count-9" ``Source.shiftLeftUInt8 Source.shiftLeftUInt8
    ``UInt8.shiftLeft 0x81 9
    #["stress", "scalar", "uint8", "external", "bitwise", "shift-left",
      "masked-count", "overflow", "boundary"]
    "Mask a UInt8 left-shift count of nine to one and discard the high bit",
  exactUInt8BinaryExternalCase
    "uint8-shift-right-count-8" ``Source.shiftRightUInt8 Source.shiftRightUInt8
    ``UInt8.shiftRight 0x81 8
    #["stress", "scalar", "uint8", "external", "bitwise", "shift-right",
      "masked-count", "boundary"]
    "Mask a UInt8 right-shift count of eight to zero",
  exactUInt8BinaryExternalCase
    "uint8-shift-right-count-9" ``Source.shiftRightUInt8 Source.shiftRightUInt8
    ``UInt8.shiftRight 0x81 9
    #["stress", "scalar", "uint8", "external", "bitwise", "shift-right",
      "masked-count", "logical", "boundary"]
    "Mask a UInt8 right-shift count of nine to one and shift logically",
  exactUInt8UnaryExternalCase
    "uint8-complement-zero" ``Source.complementUInt8 Source.complementUInt8
    ``UInt8.complement 0
    #["stress", "scalar", "uint8", "external", "bitwise", "complement",
      "boundary"]
    "Complement UInt8 zero to the exact eight-bit maximum",
  exactUInt8UnaryExternalCase
    "uint8-neg-one" ``Source.negUInt8 Source.negUInt8 ``UInt8.neg 1
    #["stress", "scalar", "uint8", "external", "arithmetic", "negation",
      "wraparound", "boundary"]
    "Negate UInt8 one modulo 2^8",
  exactUInt8DecisionExternalCase
    "uint8-dec-eq-max-true" ``Source.decideUInt8Eq Source.decideUInt8Eq
    ``UInt8.decEq 255 255
    #["stress", "scalar", "uint8", "external", "decision", "equality",
      "true", "boundary"]
    "Decide equality of two maximum UInt8 values",
  exactUInt8DecisionExternalCase
    "uint8-dec-eq-max-zero-false" ``Source.decideUInt8Eq Source.decideUInt8Eq
    ``UInt8.decEq 255 0
    #["stress", "scalar", "uint8", "external", "decision", "equality",
      "false", "boundary"]
    "Reject equality of maximum and zero UInt8 values",
  exactUInt8DecisionExternalCase
    "uint8-dec-lt-zero-max-true" ``Source.decideUInt8Lt Source.decideUInt8Lt
    ``UInt8.decLt 0 255
    #["stress", "scalar", "uint8", "external", "decision", "ordering",
      "less-than", "true", "boundary"]
    "Order UInt8 zero strictly before the maximum",
  exactUInt8DecisionExternalCase
    "uint8-dec-lt-max-zero-false" ``Source.decideUInt8Lt Source.decideUInt8Lt
    ``UInt8.decLt 255 0
    #["stress", "scalar", "uint8", "external", "decision", "ordering",
      "less-than", "false", "boundary"]
    "Reject strict unsigned ordering from maximum UInt8 to zero",
  exactUInt8DecisionExternalCase
    "uint8-dec-le-max-max-true" ``Source.decideUInt8Le Source.decideUInt8Le
    ``UInt8.decLe 255 255
    #["stress", "scalar", "uint8", "external", "decision", "ordering",
      "less-or-equal", "true", "equality", "boundary"]
    "Accept non-strict ordering at the UInt8 maximum",
  exactUInt8DecisionExternalCase
    "uint8-dec-le-max-zero-false" ``Source.decideUInt8Le Source.decideUInt8Le
    ``UInt8.decLe 255 0
    #["stress", "scalar", "uint8", "external", "decision", "ordering",
      "less-or-equal", "false", "boundary"]
    "Reject non-strict unsigned ordering from maximum UInt8 to zero",
  exactUInt16BinaryExternalCase
    "uint16-add-overflow" ``Source.addUInt16 Source.addUInt16 ``UInt16.add
    0xffff 1
    #["stress", "scalar", "uint16", "external", "arithmetic", "addition",
      "overflow", "wraparound", "boundary"]
    "Wrap maximum UInt16 plus one to zero through the native runtime external",
  exactUInt16BinaryExternalCase
    "uint16-sub-underflow" ``Source.subUInt16 Source.subUInt16 ``UInt16.sub 0 1
    #["stress", "scalar", "uint16", "external", "arithmetic", "subtraction",
      "underflow", "wraparound", "boundary"]
    "Wrap UInt16 zero minus one to the maximum value",
  exactUInt16BinaryExternalCase
    "uint16-mul-overflow" ``Source.mulUInt16 Source.mulUInt16 ``UInt16.mul
    0x8000 2
    #["stress", "scalar", "uint16", "external", "arithmetic", "multiplication",
      "overflow", "wraparound", "boundary"]
    "Discard the high multiplication bit at the exact UInt16 width",
  exactUInt16BinaryExternalCase
    "uint16-div-floor" ``Source.divUInt16 Source.divUInt16 ``UInt16.div
    0xffff 3
    #["stress", "scalar", "uint16", "external", "arithmetic", "division",
      "floor", "boundary"]
    "Compute unsigned floor division at the UInt16 maximum",
  exactUInt16BinaryExternalCase
    "uint16-div-zero" ``Source.divUInt16 Source.divUInt16 ``UInt16.div
    0xffff 0
    #["stress", "scalar", "uint16", "external", "arithmetic", "division",
      "zero-divisor", "boundary"]
    "Pin total UInt16 division by zero to zero",
  exactUInt16BinaryExternalCase
    "uint16-mod-remainder" ``Source.modUInt16 Source.modUInt16 ``UInt16.mod
    0xffff 16
    #["stress", "scalar", "uint16", "external", "arithmetic", "remainder",
      "boundary"]
    "Retain the low four bits as the UInt16 remainder",
  exactUInt16BinaryExternalCase
    "uint16-mod-zero" ``Source.modUInt16 Source.modUInt16 ``UInt16.mod
    0xffff 0
    #["stress", "scalar", "uint16", "external", "arithmetic", "remainder",
      "zero-divisor", "boundary"]
    "Pin UInt16 remainder by zero to the dividend",
  exactUInt16BinaryExternalCase
    "uint16-land-mixed" ``Source.landUInt16 Source.landUInt16 ``UInt16.land
    0xf0f0 0x0ff0
    #["stress", "scalar", "uint16", "external", "bitwise", "and", "mixed-bits"]
    "Intersect alternating UInt16 bit groups exactly",
  exactUInt16BinaryExternalCase
    "uint16-lor-mixed" ``Source.lorUInt16 Source.lorUInt16 ``UInt16.lor
    0xf00f 0x0ff0
    #["stress", "scalar", "uint16", "external", "bitwise", "or", "mixed-bits"]
    "Union separated UInt16 bit groups across the high and low boundaries",
  exactUInt16BinaryExternalCase
    "uint16-xor-mixed" ``Source.xorUInt16 Source.xorUInt16 ``UInt16.xor
    0xf0f0 0x0ff0
    #["stress", "scalar", "uint16", "external", "bitwise", "xor", "mixed-bits"]
    "Exclusive-or alternating UInt16 bit groups exactly",
  exactUInt16BinaryExternalCase
    "uint16-shift-left-count-16" ``Source.shiftLeftUInt16 Source.shiftLeftUInt16
    ``UInt16.shiftLeft 0x8001 16
    #["stress", "scalar", "uint16", "external", "bitwise", "shift-left",
      "masked-count", "boundary"]
    "Mask a UInt16 left-shift count of 16 to zero",
  exactUInt16BinaryExternalCase
    "uint16-shift-left-count-17" ``Source.shiftLeftUInt16 Source.shiftLeftUInt16
    ``UInt16.shiftLeft 0x8001 17
    #["stress", "scalar", "uint16", "external", "bitwise", "shift-left",
      "masked-count", "overflow", "boundary"]
    "Mask a UInt16 left-shift count of 17 to one and discard the high bit",
  exactUInt16BinaryExternalCase
    "uint16-shift-right-count-16" ``Source.shiftRightUInt16 Source.shiftRightUInt16
    ``UInt16.shiftRight 0x8001 16
    #["stress", "scalar", "uint16", "external", "bitwise", "shift-right",
      "masked-count", "boundary"]
    "Mask a UInt16 right-shift count of 16 to zero",
  exactUInt16BinaryExternalCase
    "uint16-shift-right-count-17" ``Source.shiftRightUInt16 Source.shiftRightUInt16
    ``UInt16.shiftRight 0x8001 17
    #["stress", "scalar", "uint16", "external", "bitwise", "shift-right",
      "masked-count", "logical", "boundary"]
    "Mask a UInt16 right-shift count of 17 to one and shift logically",
  exactUInt16UnaryExternalCase
    "uint16-complement-zero" ``Source.complementUInt16 Source.complementUInt16
    ``UInt16.complement 0
    #["stress", "scalar", "uint16", "external", "bitwise", "complement",
      "boundary"]
    "Complement UInt16 zero to the exact 16-bit maximum",
  exactUInt16UnaryExternalCase
    "uint16-neg-one" ``Source.negUInt16 Source.negUInt16 ``UInt16.neg 1
    #["stress", "scalar", "uint16", "external", "arithmetic", "negation",
      "wraparound", "boundary"]
    "Negate UInt16 one modulo 2^16",
  exactUInt16DecisionExternalCase
    "uint16-dec-eq-max-true" ``Source.decideUInt16Eq Source.decideUInt16Eq
    ``UInt16.decEq 0xffff 0xffff
    #["stress", "scalar", "uint16", "external", "decision", "equality",
      "true", "boundary"]
    "Decide equality of two maximum UInt16 values",
  exactUInt16DecisionExternalCase
    "uint16-dec-eq-max-zero-false" ``Source.decideUInt16Eq Source.decideUInt16Eq
    ``UInt16.decEq 0xffff 0
    #["stress", "scalar", "uint16", "external", "decision", "equality",
      "false", "boundary"]
    "Reject equality of maximum and zero UInt16 values",
  exactUInt16DecisionExternalCase
    "uint16-dec-lt-zero-max-true" ``Source.decideUInt16Lt Source.decideUInt16Lt
    ``UInt16.decLt 0 0xffff
    #["stress", "scalar", "uint16", "external", "decision", "ordering",
      "less-than", "true", "boundary"]
    "Order UInt16 zero strictly before the maximum",
  exactUInt16DecisionExternalCase
    "uint16-dec-lt-max-zero-false" ``Source.decideUInt16Lt Source.decideUInt16Lt
    ``UInt16.decLt 0xffff 0
    #["stress", "scalar", "uint16", "external", "decision", "ordering",
      "less-than", "false", "boundary"]
    "Reject strict unsigned ordering from maximum UInt16 to zero",
  exactUInt16DecisionExternalCase
    "uint16-dec-le-max-max-true" ``Source.decideUInt16Le Source.decideUInt16Le
    ``UInt16.decLe 0xffff 0xffff
    #["stress", "scalar", "uint16", "external", "decision", "ordering",
      "less-or-equal", "true", "equality", "boundary"]
    "Accept non-strict ordering at the UInt16 maximum",
  exactUInt16DecisionExternalCase
    "uint16-dec-le-max-zero-false" ``Source.decideUInt16Le Source.decideUInt16Le
    ``UInt16.decLe 0xffff 0
    #["stress", "scalar", "uint16", "external", "decision", "ordering",
      "less-or-equal", "false", "boundary"]
    "Reject non-strict unsigned ordering from maximum UInt16 to zero",
  exactUInt32BinaryExternalCase
    "uint32-add-overflow" ``Source.addUInt32 Source.addUInt32 ``UInt32.add
    4294967295 1
    #["stress", "scalar", "uint32", "external", "arithmetic", "addition",
      "overflow", "wraparound", "boundary"]
    "Wrap maximum UInt32 plus one to zero through the native runtime external",
  exactUInt32BinaryExternalCase
    "uint32-sub-underflow" ``Source.subUInt32 Source.subUInt32 ``UInt32.sub
    0 1
    #["stress", "scalar", "uint32", "external", "arithmetic", "subtraction",
      "underflow", "wraparound", "boundary"]
    "Wrap UInt32 zero minus one to the maximum value",
  exactUInt32BinaryExternalCase
    "uint32-mul-overflow" ``Source.mulUInt32 Source.mulUInt32 ``UInt32.mul
    2147483648 2
    #["stress", "scalar", "uint32", "external", "arithmetic", "multiplication",
      "overflow", "wraparound", "boundary"]
    "Discard the high multiplication bit at the exact UInt32 width",
  exactUInt32BinaryExternalCase
    "uint32-div-floor" ``Source.divUInt32 Source.divUInt32 ``UInt32.div
    4294967295 3
    #["stress", "scalar", "uint32", "external", "arithmetic", "division",
      "floor", "boundary"]
    "Compute unsigned floor division at the UInt32 maximum",
  exactUInt32BinaryExternalCase
    "uint32-div-zero" ``Source.divUInt32 Source.divUInt32 ``UInt32.div
    4294967295 0
    #["stress", "scalar", "uint32", "external", "arithmetic", "division",
      "zero-divisor", "boundary"]
    "Pin total UInt32 division by zero to zero",
  exactUInt32BinaryExternalCase
    "uint32-mod-remainder" ``Source.modUInt32 Source.modUInt32 ``UInt32.mod
    4294967295 16
    #["stress", "scalar", "uint32", "external", "arithmetic", "remainder",
      "boundary"]
    "Retain the low four bits as the UInt32 remainder",
  exactUInt32BinaryExternalCase
    "uint32-mod-zero" ``Source.modUInt32 Source.modUInt32 ``UInt32.mod
    4294967295 0
    #["stress", "scalar", "uint32", "external", "arithmetic", "remainder",
      "zero-divisor", "boundary"]
    "Pin UInt32 remainder by zero to the dividend",
  exactUInt32BinaryExternalCase
    "uint32-land-mixed" ``Source.landUInt32 Source.landUInt32 ``UInt32.land
    0xf0f0f0f0 0x0ff00ff0
    #["stress", "scalar", "uint32", "external", "bitwise", "and", "mixed-bits"]
    "Intersect alternating UInt32 bit groups exactly",
  exactUInt32BinaryExternalCase
    "uint32-lor-mixed" ``Source.lorUInt32 Source.lorUInt32 ``UInt32.lor
    0xf000000f 0x0ff00ff0
    #["stress", "scalar", "uint32", "external", "bitwise", "or", "mixed-bits"]
    "Union separated UInt32 bit groups across the high and low boundaries",
  exactUInt32BinaryExternalCase
    "uint32-xor-mixed" ``Source.xorUInt32 Source.xorUInt32 ``UInt32.xor
    0xf0f0f0f0 0x0ff00ff0
    #["stress", "scalar", "uint32", "external", "bitwise", "xor", "mixed-bits"]
    "Exclusive-or alternating UInt32 bit groups exactly",
  exactUInt32BinaryExternalCase
    "uint32-shift-left-count-32" ``Source.shiftLeftUInt32 Source.shiftLeftUInt32
    ``UInt32.shiftLeft 0x80000001 32
    #["stress", "scalar", "uint32", "external", "bitwise", "shift-left",
      "masked-count", "boundary"]
    "Mask a UInt32 left-shift count of 32 to zero",
  exactUInt32BinaryExternalCase
    "uint32-shift-left-count-33" ``Source.shiftLeftUInt32 Source.shiftLeftUInt32
    ``UInt32.shiftLeft 0x80000001 33
    #["stress", "scalar", "uint32", "external", "bitwise", "shift-left",
      "masked-count", "overflow", "boundary"]
    "Mask a UInt32 left-shift count of 33 to one and discard the high bit",
  exactUInt32BinaryExternalCase
    "uint32-shift-right-count-32" ``Source.shiftRightUInt32 Source.shiftRightUInt32
    ``UInt32.shiftRight 0x80000001 32
    #["stress", "scalar", "uint32", "external", "bitwise", "shift-right",
      "masked-count", "boundary"]
    "Mask a UInt32 right-shift count of 32 to zero",
  exactUInt32BinaryExternalCase
    "uint32-shift-right-count-33" ``Source.shiftRightUInt32 Source.shiftRightUInt32
    ``UInt32.shiftRight 0x80000001 33
    #["stress", "scalar", "uint32", "external", "bitwise", "shift-right",
      "masked-count", "logical", "boundary"]
    "Mask a UInt32 right-shift count of 33 to one and shift logically",
  exactUInt32UnaryExternalCase
    "uint32-complement-zero" ``Source.complementUInt32 Source.complementUInt32
    ``UInt32.complement 0
    #["stress", "scalar", "uint32", "external", "bitwise", "complement",
      "boundary"]
    "Complement UInt32 zero to the exact 32-bit maximum",
  exactUInt32UnaryExternalCase
    "uint32-neg-one" ``Source.negUInt32 Source.negUInt32 ``UInt32.neg 1
    #["stress", "scalar", "uint32", "external", "arithmetic", "negation",
      "wraparound", "boundary"]
    "Negate UInt32 one modulo 2^32",
  exactUInt32DecisionExternalCase
    "uint32-dec-eq-max-true" ``Source.decideUInt32Eq Source.decideUInt32Eq
    ``UInt32.decEq 4294967295 4294967295
    #["stress", "scalar", "uint32", "external", "decision", "equality",
      "true", "boundary"]
    "Decide equality of two maximum UInt32 values",
  exactUInt32DecisionExternalCase
    "uint32-dec-eq-max-zero-false" ``Source.decideUInt32Eq Source.decideUInt32Eq
    ``UInt32.decEq 4294967295 0
    #["stress", "scalar", "uint32", "external", "decision", "equality",
      "false", "boundary"]
    "Reject equality of maximum and zero UInt32 values",
  exactUInt32DecisionExternalCase
    "uint32-dec-lt-zero-max-true" ``Source.decideUInt32Lt Source.decideUInt32Lt
    ``UInt32.decLt 0 4294967295
    #["stress", "scalar", "uint32", "external", "decision", "ordering",
      "less-than", "true", "boundary"]
    "Order UInt32 zero strictly before the maximum",
  exactUInt32DecisionExternalCase
    "uint32-dec-lt-max-zero-false" ``Source.decideUInt32Lt Source.decideUInt32Lt
    ``UInt32.decLt 4294967295 0
    #["stress", "scalar", "uint32", "external", "decision", "ordering",
      "less-than", "false", "boundary"]
    "Reject strict unsigned ordering from maximum UInt32 to zero",
  exactUInt32DecisionExternalCase
    "uint32-dec-le-max-max-true" ``Source.decideUInt32Le Source.decideUInt32Le
    ``UInt32.decLe 4294967295 4294967295
    #["stress", "scalar", "uint32", "external", "decision", "ordering",
      "less-or-equal", "true", "equality", "boundary"]
    "Accept non-strict ordering at the UInt32 maximum",
  exactUInt32DecisionExternalCase
    "uint32-dec-le-max-zero-false" ``Source.decideUInt32Le Source.decideUInt32Le
    ``UInt32.decLe 4294967295 0
    #["stress", "scalar", "uint32", "external", "decision", "ordering",
      "less-or-equal", "false", "boundary"]
    "Reject non-strict unsigned ordering from maximum UInt32 to zero",
  exactUInt64BinaryExternalCase
    "uint64-add-overflow" ``Source.addUInt64 Source.addUInt64 ``UInt64.add
    0xffffffffffffffff 1
    #["stress", "scalar", "uint64", "external", "arithmetic", "addition",
      "overflow", "wraparound", "boundary", "i64"]
    "Wrap maximum UInt64 plus one to zero through the native runtime external",
  exactUInt64BinaryExternalCase
    "uint64-sub-underflow" ``Source.subUInt64 Source.subUInt64 ``UInt64.sub
    0 1
    #["stress", "scalar", "uint64", "external", "arithmetic", "subtraction",
      "underflow", "wraparound", "boundary", "i64"]
    "Wrap UInt64 zero minus one to the maximum value",
  exactUInt64BinaryExternalCase
    "uint64-mul-overflow" ``Source.mulUInt64 Source.mulUInt64 ``UInt64.mul
    0x8000000000000000 2
    #["stress", "scalar", "uint64", "external", "arithmetic", "multiplication",
      "overflow", "wraparound", "boundary", "i64"]
    "Discard the high multiplication bit at the exact UInt64 width",
  exactUInt64BinaryExternalCase
    "uint64-div-floor" ``Source.divUInt64 Source.divUInt64 ``UInt64.div
    0xffffffffffffffff 3
    #["stress", "scalar", "uint64", "external", "arithmetic", "division",
      "floor", "boundary", "i64"]
    "Compute unsigned floor division at the UInt64 maximum",
  exactUInt64BinaryExternalCase
    "uint64-div-zero" ``Source.divUInt64 Source.divUInt64 ``UInt64.div
    0xffffffffffffffff 0
    #["stress", "scalar", "uint64", "external", "arithmetic", "division",
      "zero-divisor", "boundary", "i64"]
    "Pin total UInt64 division by zero to zero",
  exactUInt64BinaryExternalCase
    "uint64-mod-remainder" ``Source.modUInt64 Source.modUInt64 ``UInt64.mod
    0xffffffffffffffff 16
    #["stress", "scalar", "uint64", "external", "arithmetic", "remainder",
      "boundary", "i64"]
    "Retain the low four bits as the UInt64 remainder",
  exactUInt64BinaryExternalCase
    "uint64-mod-zero" ``Source.modUInt64 Source.modUInt64 ``UInt64.mod
    0xffffffffffffffff 0
    #["stress", "scalar", "uint64", "external", "arithmetic", "remainder",
      "zero-divisor", "boundary", "i64"]
    "Pin UInt64 remainder by zero to the dividend",
  exactUInt64BinaryExternalCase
    "uint64-land-mixed" ``Source.landUInt64 Source.landUInt64 ``UInt64.land
    0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0
    #["stress", "scalar", "uint64", "external", "bitwise", "and", "mixed-bits",
      "i64"]
    "Intersect alternating UInt64 bit groups exactly",
  exactUInt64BinaryExternalCase
    "uint64-lor-mixed" ``Source.lorUInt64 Source.lorUInt64 ``UInt64.lor
    0xf00000000000000f 0x0ff00ff00ff00ff0
    #["stress", "scalar", "uint64", "external", "bitwise", "or", "mixed-bits",
      "i64"]
    "Union separated UInt64 bit groups across the high and low boundaries",
  exactUInt64BinaryExternalCase
    "uint64-xor-mixed" ``Source.xorUInt64 Source.xorUInt64 ``UInt64.xor
    0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0
    #["stress", "scalar", "uint64", "external", "bitwise", "xor", "mixed-bits",
      "i64"]
    "Exclusive-or alternating UInt64 bit groups exactly",
  exactUInt64BinaryExternalCase
    "uint64-shift-left-count-64" ``Source.shiftLeftUInt64 Source.shiftLeftUInt64
    ``UInt64.shiftLeft 0x8000000000000001 64
    #["stress", "scalar", "uint64", "external", "bitwise", "shift-left",
      "masked-count", "boundary", "i64"]
    "Mask a UInt64 left-shift count of 64 to zero",
  exactUInt64BinaryExternalCase
    "uint64-shift-left-count-65" ``Source.shiftLeftUInt64 Source.shiftLeftUInt64
    ``UInt64.shiftLeft 0x8000000000000001 65
    #["stress", "scalar", "uint64", "external", "bitwise", "shift-left",
      "masked-count", "overflow", "boundary", "i64"]
    "Mask a UInt64 left-shift count of 65 to one and discard the high bit",
  exactUInt64BinaryExternalCase
    "uint64-shift-right-count-64" ``Source.shiftRightUInt64 Source.shiftRightUInt64
    ``UInt64.shiftRight 0x8000000000000001 64
    #["stress", "scalar", "uint64", "external", "bitwise", "shift-right",
      "masked-count", "boundary", "i64"]
    "Mask a UInt64 right-shift count of 64 to zero",
  exactUInt64BinaryExternalCase
    "uint64-shift-right-count-65" ``Source.shiftRightUInt64 Source.shiftRightUInt64
    ``UInt64.shiftRight 0x8000000000000001 65
    #["stress", "scalar", "uint64", "external", "bitwise", "shift-right",
      "masked-count", "logical", "boundary", "i64"]
    "Mask a UInt64 right-shift count of 65 to one and shift logically",
  exactUInt64UnaryExternalCase
    "uint64-complement-zero" ``Source.complementUInt64 Source.complementUInt64
    ``UInt64.complement 0
    #["stress", "scalar", "uint64", "external", "bitwise", "complement",
      "boundary", "i64"]
    "Complement UInt64 zero to the exact 64-bit maximum",
  exactUInt64UnaryExternalCase
    "uint64-neg-one" ``Source.negUInt64 Source.negUInt64 ``UInt64.neg 1
    #["stress", "scalar", "uint64", "external", "arithmetic", "negation",
      "wraparound", "boundary", "i64"]
    "Negate UInt64 one modulo 2^64",
  exactUInt64DecisionExternalCase
    "uint64-dec-eq-max-true" ``Source.decideUInt64Eq Source.decideUInt64Eq
    ``UInt64.decEq 0xffffffffffffffff 0xffffffffffffffff
    #["stress", "scalar", "uint64", "external", "decision", "equality",
      "true", "boundary", "i64"]
    "Decide equality of two maximum UInt64 values",
  exactUInt64DecisionExternalCase
    "uint64-dec-eq-max-zero-false" ``Source.decideUInt64Eq Source.decideUInt64Eq
    ``UInt64.decEq 0xffffffffffffffff 0
    #["stress", "scalar", "uint64", "external", "decision", "equality",
      "false", "boundary", "i64"]
    "Reject equality of maximum and zero UInt64 values",
  exactUInt64DecisionExternalCase
    "uint64-dec-lt-zero-max-true" ``Source.decideUInt64Lt Source.decideUInt64Lt
    ``UInt64.decLt 0 0xffffffffffffffff
    #["stress", "scalar", "uint64", "external", "decision", "ordering",
      "less-than", "true", "boundary", "i64"]
    "Order UInt64 zero strictly before the maximum",
  exactUInt64DecisionExternalCase
    "uint64-dec-lt-max-zero-false" ``Source.decideUInt64Lt Source.decideUInt64Lt
    ``UInt64.decLt 0xffffffffffffffff 0
    #["stress", "scalar", "uint64", "external", "decision", "ordering",
      "less-than", "false", "boundary", "i64"]
    "Reject strict unsigned ordering from maximum UInt64 to zero",
  exactUInt64DecisionExternalCase
    "uint64-dec-le-max-max-true" ``Source.decideUInt64Le Source.decideUInt64Le
    ``UInt64.decLe 0xffffffffffffffff 0xffffffffffffffff
    #["stress", "scalar", "uint64", "external", "decision", "ordering",
      "less-or-equal", "true", "equality", "boundary", "i64"]
    "Accept non-strict ordering at the UInt64 maximum",
  exactUInt64DecisionExternalCase
    "uint64-dec-le-max-zero-false" ``Source.decideUInt64Le Source.decideUInt64Le
    ``UInt64.decLe 0xffffffffffffffff 0
    #["stress", "scalar", "uint64", "external", "decision", "ordering",
      "less-or-equal", "false", "boundary", "i64"]
    "Reject non-strict unsigned ordering from maximum UInt64 to zero"
]

private def conversionCases : Array Case := #[
  exactFixedWidthConversionExternalCase uint8CaseCodec uint16CaseCodec
    "uint8-to-uint16" ``Source.uint8ToUInt16 Source.uint8ToUInt16
    ``UInt8.toUInt16 255
    #["stress", "scalar", "uint8", "uint16", "external", "conversion",
      "cross-width", "widening", "i32"]
    "Zero-extend the maximum UInt8 to UInt16 without sign extension",
  exactFixedWidthConversionExternalCase uint8CaseCodec uint32CaseCodec
    "uint8-to-uint32" ``Source.uint8ToUInt32 Source.uint8ToUInt32
    ``UInt8.toUInt32 255
    #["stress", "scalar", "uint8", "uint32", "external", "conversion",
      "cross-width", "widening", "i32"]
    "Zero-extend the maximum UInt8 to UInt32 without sign extension",
  exactFixedWidthConversionExternalCase uint8CaseCodec uint64CaseCodec
    "uint8-to-uint64" ``Source.uint8ToUInt64 Source.uint8ToUInt64
    ``UInt8.toUInt64 255
    #["stress", "scalar", "uint8", "uint64", "external", "conversion",
      "cross-width", "widening", "i32-to-i64"]
    "Zero-extend the maximum UInt8 across the i32-to-i64 boundary",
  exactFixedWidthConversionExternalCase uint8CaseCodec usizeCaseCodec
    "uint8-to-usize" ``Source.uint8ToUSize Source.uint8ToUSize
    ``UInt8.toUSize 255
    #["stress", "uint8", "usize", "usize-external", "external", "conversion",
      "cross-width", "widening", "i32-to-i64", "semantic-lean64"]
    "Zero-extend the maximum UInt8 to semantic Lean64 USize",
  exactFixedWidthConversionExternalCase uint16CaseCodec uint8CaseCodec
    "uint16-to-uint8" ``Source.uint16ToUInt8 Source.uint16ToUInt8
    ``UInt16.toUInt8 273
    #["stress", "scalar", "uint16", "uint8", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i32"]
    "Reduce 2^8 + 17 modulo 2^8 while narrowing UInt16 to UInt8",
  exactFixedWidthConversionExternalCase uint16CaseCodec uint32CaseCodec
    "uint16-to-uint32" ``Source.uint16ToUInt32 Source.uint16ToUInt32
    ``UInt16.toUInt32 65535
    #["stress", "scalar", "uint16", "uint32", "external", "conversion",
      "cross-width", "widening", "i32"]
    "Zero-extend the maximum UInt16 to UInt32 without sign extension",
  exactFixedWidthConversionExternalCase uint16CaseCodec uint64CaseCodec
    "uint16-to-uint64" ``Source.uint16ToUInt64 Source.uint16ToUInt64
    ``UInt16.toUInt64 65535
    #["stress", "scalar", "uint16", "uint64", "external", "conversion",
      "cross-width", "widening", "i32-to-i64"]
    "Zero-extend the maximum UInt16 across the i32-to-i64 boundary",
  exactFixedWidthConversionExternalCase uint16CaseCodec usizeCaseCodec
    "uint16-to-usize" ``Source.uint16ToUSize Source.uint16ToUSize
    ``UInt16.toUSize 65535
    #["stress", "uint16", "usize", "usize-external", "external", "conversion",
      "cross-width", "widening", "i32-to-i64", "semantic-lean64"]
    "Zero-extend the maximum UInt16 to semantic Lean64 USize",
  exactFixedWidthConversionExternalCase uint32CaseCodec uint8CaseCodec
    "uint32-to-uint8" ``Source.uint32ToUInt8 Source.uint32ToUInt8
    ``UInt32.toUInt8 273
    #["stress", "scalar", "uint32", "uint8", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i32"]
    "Reduce 2^8 + 17 modulo 2^8 while narrowing UInt32 to UInt8",
  exactFixedWidthConversionExternalCase uint32CaseCodec uint16CaseCodec
    "uint32-to-uint16" ``Source.uint32ToUInt16 Source.uint32ToUInt16
    ``UInt32.toUInt16 65553
    #["stress", "scalar", "uint32", "uint16", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i32"]
    "Reduce 2^16 + 17 modulo 2^16 while narrowing UInt32 to UInt16",
  exactFixedWidthConversionExternalCase uint32CaseCodec uint64CaseCodec
    "uint32-to-uint64" ``Source.uint32ToUInt64 Source.uint32ToUInt64
    ``UInt32.toUInt64 4294967295
    #["stress", "scalar", "uint32", "uint64", "external", "conversion",
      "cross-width", "widening", "i32-to-i64"]
    "Zero-extend the maximum UInt32 across the i32-to-i64 boundary",
  exactFixedWidthConversionExternalCase uint32CaseCodec usizeCaseCodec
    "uint32-to-usize" ``Source.uint32ToUSize Source.uint32ToUSize
    ``UInt32.toUSize 4294967295
    #["stress", "uint32", "usize", "usize-external", "external", "conversion",
      "cross-width", "widening", "i32-to-i64", "semantic-lean64"]
    "Zero-extend the maximum UInt32 to semantic Lean64 USize",
  exactFixedWidthConversionExternalCase uint64CaseCodec uint8CaseCodec
    "uint64-to-uint8" ``Source.uint64ToUInt8 Source.uint64ToUInt8
    ``UInt64.toUInt8 273
    #["stress", "scalar", "uint64", "uint8", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i64-to-i32"]
    "Reduce 2^8 + 17 modulo 2^8 while narrowing UInt64 to UInt8",
  exactFixedWidthConversionExternalCase uint64CaseCodec uint16CaseCodec
    "uint64-to-uint16" ``Source.uint64ToUInt16 Source.uint64ToUInt16
    ``UInt64.toUInt16 65553
    #["stress", "scalar", "uint64", "uint16", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i64-to-i32"]
    "Reduce 2^16 + 17 modulo 2^16 while narrowing UInt64 to UInt16",
  exactFixedWidthConversionExternalCase uint64CaseCodec uint32CaseCodec
    "uint64-to-uint32" ``Source.uint64ToUInt32 Source.uint64ToUInt32
    ``UInt64.toUInt32 4294967313
    #["stress", "scalar", "uint64", "uint32", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i64-to-i32"]
    "Reduce 2^32 + 17 modulo 2^32 while narrowing UInt64 to UInt32",
  exactFixedWidthConversionExternalCase uint64CaseCodec usizeCaseCodec
    "uint64-to-usize" ``Source.uint64ToUSize Source.uint64ToUSize
    ``UInt64.toUSize 0x8000000000000011
    #["stress", "uint64", "usize", "usize-external", "external", "conversion",
      "cross-width", "same-width", "high-bit", "i64", "semantic-lean64"]
    "Preserve a high-bit UInt64 exactly when converting to semantic Lean64 USize",
  exactFixedWidthConversionExternalCase usizeCaseCodec uint8CaseCodec
    "usize-to-uint8" ``Source.usizeToUInt8 Source.usizeToUInt8
    ``USize.toUInt8 273
    #["stress", "usize", "usize-external", "uint8", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i64-to-i32", "semantic-lean64"]
    "Reduce 2^8 + 17 modulo 2^8 while narrowing USize to UInt8",
  exactFixedWidthConversionExternalCase usizeCaseCodec uint16CaseCodec
    "usize-to-uint16" ``Source.usizeToUInt16 Source.usizeToUInt16
    ``USize.toUInt16 65553
    #["stress", "usize", "usize-external", "uint16", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i64-to-i32", "semantic-lean64"]
    "Reduce 2^16 + 17 modulo 2^16 while narrowing USize to UInt16",
  exactFixedWidthConversionExternalCase usizeCaseCodec uint32CaseCodec
    "usize-to-uint32" ``Source.usizeToUInt32 Source.usizeToUInt32
    ``USize.toUInt32 4294967313
    #["stress", "usize", "usize-external", "uint32", "external", "conversion",
      "cross-width", "narrowing", "modulo", "i64-to-i32", "semantic-lean64"]
    "Reduce 2^32 + 17 modulo 2^32 while narrowing USize to UInt32",
  exactFixedWidthConversionExternalCase usizeCaseCodec uint64CaseCodec
    "usize-to-uint64" ``Source.usizeToUInt64 Source.usizeToUInt64
    ``USize.toUInt64 0x8000000000000011
    #["stress", "usize", "usize-external", "uint64", "external", "conversion",
      "cross-width", "same-width", "high-bit", "i64", "semantic-lean64"]
    "Preserve a high-bit semantic Lean64 USize exactly when converting to UInt64",
  exactNatToUInt8ExternalCase
    "nat-to-uint8-max" ``Source.natToUInt8 Source.natToUInt8
    ``UInt8.ofNat 255
    #["stress", "scalar", "uint8", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "immediate-input",
      "boundary", "maximum", "i32"]
    "Convert the maximum in-range Nat to the maximum UInt8",
  exactNatToUInt8ExternalCase
    "nat-to-uint8-modulus" ``Source.natToUInt8 Source.natToUInt8
    ``UInt8.ofNat 256
    #["stress", "scalar", "uint8", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "immediate-input",
      "boundary", "overflow", "wraparound", "i32"]
    "Wrap the first out-of-range Nat at exactly 2^8 to UInt8 zero",
  exactNatToUInt8ExternalCase
    "nat-to-uint8-multi-limb" ``Source.natToUInt8 Source.natToUInt8
    ``UInt8.ofNat 340282366920938463463374607431768211473
    #["stress", "scalar", "uint8", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "heap-input",
      "multi-limb", "wraparound", "i32"]
    "Reduce 2^128 + 17 modulo 2^8 while converting a multi-limb Nat to UInt8",
  exactUInt8ToNatExternalCase
    "uint8-to-nat-zero" ``Source.uint8ToNat Source.uint8ToNat
    ``UInt8.toNat 0
    #["stress", "scalar", "uint8", "external", "conversion", "nat",
      "small-word-nat-conversion", "from-fixed-width", "immediate-result",
      "boundary", "i32"]
    "Convert UInt8 zero to a tagged Nat",
  exactUInt8ToNatExternalCase
    "uint8-to-nat-max" ``Source.uint8ToNat Source.uint8ToNat
    ``UInt8.toNat 255
    #["stress", "scalar", "uint8", "external", "conversion", "nat",
      "small-word-nat-conversion", "from-fixed-width", "immediate-result",
      "boundary", "maximum", "i32"]
    "Convert the maximum UInt8 exactly to a tagged Nat",
  exactNatToUInt16ExternalCase
    "nat-to-uint16-max" ``Source.natToUInt16 Source.natToUInt16
    ``UInt16.ofNat 65535
    #["stress", "scalar", "uint16", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "immediate-input",
      "boundary", "maximum", "i32"]
    "Convert the maximum in-range Nat to the maximum UInt16",
  exactNatToUInt16ExternalCase
    "nat-to-uint16-modulus" ``Source.natToUInt16 Source.natToUInt16
    ``UInt16.ofNat 65536
    #["stress", "scalar", "uint16", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "immediate-input",
      "boundary", "overflow", "wraparound", "i32"]
    "Wrap the first out-of-range Nat at exactly 2^16 to UInt16 zero",
  exactNatToUInt16ExternalCase
    "nat-to-uint16-multi-limb" ``Source.natToUInt16 Source.natToUInt16
    ``UInt16.ofNat 340282366920938463463374607431768211473
    #["stress", "scalar", "uint16", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "heap-input",
      "multi-limb", "wraparound", "i32"]
    "Reduce 2^128 + 17 modulo 2^16 while converting a multi-limb Nat to UInt16",
  exactUInt16ToNatExternalCase
    "uint16-to-nat-zero" ``Source.uint16ToNat Source.uint16ToNat
    ``UInt16.toNat 0
    #["stress", "scalar", "uint16", "external", "conversion", "nat",
      "small-word-nat-conversion", "from-fixed-width", "immediate-result",
      "boundary", "i32"]
    "Convert UInt16 zero to a tagged Nat",
  exactUInt16ToNatExternalCase
    "uint16-to-nat-max" ``Source.uint16ToNat Source.uint16ToNat
    ``UInt16.toNat 65535
    #["stress", "scalar", "uint16", "external", "conversion", "nat",
      "small-word-nat-conversion", "from-fixed-width", "immediate-result",
      "boundary", "maximum", "i32"]
    "Convert the maximum UInt16 exactly to a tagged Nat",
  exactNatToUInt32ExternalCase
    "nat-to-uint32-max" ``Source.natToUInt32 Source.natToUInt32
    ``UInt32.ofNat 4294967295
    #["stress", "scalar", "uint32", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "immediate-input",
      "boundary", "maximum", "i32"]
    "Convert the maximum in-range Nat to the maximum UInt32",
  exactNatToUInt32ExternalCase
    "nat-to-uint32-modulus" ``Source.natToUInt32 Source.natToUInt32
    ``UInt32.ofNat 4294967296
    #["stress", "scalar", "uint32", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "immediate-input",
      "boundary", "overflow", "wraparound", "i32"]
    "Wrap the first out-of-range Nat at exactly 2^32 to UInt32 zero",
  exactNatToUInt32ExternalCase
    "nat-to-uint32-multi-limb" ``Source.natToUInt32 Source.natToUInt32
    ``UInt32.ofNat 340282366920938463463374607431768211473
    #["stress", "scalar", "uint32", "external", "conversion", "nat",
      "small-word-nat-conversion", "to-fixed-width", "heap-input",
      "multi-limb", "wraparound", "i32"]
    "Reduce 2^128 + 17 modulo 2^32 while converting a multi-limb Nat to UInt32",
  exactUInt32ToNatExternalCase
    "uint32-to-nat-zero" ``Source.uint32ToNat Source.uint32ToNat
    ``UInt32.toNat 0
    #["stress", "scalar", "uint32", "external", "conversion", "nat",
      "small-word-nat-conversion", "from-fixed-width", "immediate-result",
      "boundary", "i32"]
    "Convert UInt32 zero to a tagged Nat",
  exactUInt32ToNatExternalCase
    "uint32-to-nat-max" ``Source.uint32ToNat Source.uint32ToNat
    ``UInt32.toNat 4294967295
    #["stress", "scalar", "uint32", "external", "conversion", "nat",
      "small-word-nat-conversion", "from-fixed-width", "immediate-result",
      "boundary", "maximum", "i32"]
    "Convert the maximum UInt32 exactly to a tagged Nat",
  exactNatToUInt64ExternalCase
    "nat-to-uint64-small" ``Source.natToUInt64 Source.natToUInt64
    ``UInt64.ofNat 17
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "to-fixed-width", "immediate-input", "i64"]
    "Convert a small tagged Nat to an exact UInt64 scalar",
  exactNatToUInt64ExternalCase
    "nat-to-uint64-immediate-max" ``Source.natToUInt64 Source.natToUInt64
    ``UInt64.ofNat 9223372036854775807
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "to-fixed-width", "immediate-input", "boundary", "i64"]
    "Convert the maximum tagged Nat to UInt64 without losing its high payload bits",
  exactNatToUInt64ExternalCase
    "nat-to-uint64-first-heap" ``Source.natToUInt64 Source.natToUInt64
    ``UInt64.ofNat 9223372036854775808
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "boundary", "i64"]
    "Convert the first heap Nat to the UInt64 value at bit 63",
  exactNatToUInt64ExternalCase
    "nat-to-uint64-max" ``Source.natToUInt64 Source.natToUInt64
    ``UInt64.ofNat 18446744073709551615
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "boundary", "maximum", "i64"]
    "Convert the maximum in-range 64-bit Nat to the maximum UInt64",
  exactNatToUInt64ExternalCase
    "nat-to-uint64-modulus" ``Source.natToUInt64 Source.natToUInt64
    ``UInt64.ofNat 18446744073709551616
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "boundary", "overflow", "wraparound", "i64"]
    "Wrap the first out-of-range Nat at exactly 2^64 to UInt64 zero",
  exactNatToUInt64ExternalCase
    "nat-to-uint64-multi-limb" ``Source.natToUInt64 Source.natToUInt64
    ``UInt64.ofNat 340282366920938463463374607431768211473
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "multi-limb", "wraparound", "i64"]
    "Reduce 2^128 + 17 modulo 2^64 while converting a multi-limb Nat to UInt64",
  exactUInt64ToNatExternalCase
    "uint64-to-nat-zero" ``Source.uint64ToNat Source.uint64ToNat
    ``UInt64.toNat 0
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "from-fixed-width", "immediate-result", "boundary", "i64"]
    "Convert UInt64 zero to a tagged Nat",
  exactUInt64ToNatExternalCase
    "uint64-to-nat-immediate-max" ``Source.uint64ToNat Source.uint64ToNat
    ``UInt64.toNat 0x7fffffffffffffff
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "from-fixed-width", "immediate-result", "boundary", "i64"]
    "Convert bit-63-minus-one UInt64 to the maximum tagged Nat",
  exactUInt64ToNatExternalCase
    "uint64-to-nat-first-heap" ``Source.uint64ToNat Source.uint64ToNat
    ``UInt64.toNat 0x8000000000000000
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "from-fixed-width", "heap-result", "allocation", "boundary", "i64"]
    "Allocate the first heap Nat while converting the UInt64 bit-63 boundary",
  exactUInt64ToNatExternalCase
    "uint64-to-nat-max" ``Source.uint64ToNat Source.uint64ToNat
    ``UInt64.toNat 0xffffffffffffffff
    #["stress", "scalar", "uint64", "external", "conversion", "nat",
      "from-fixed-width", "heap-result", "allocation", "boundary", "maximum", "i64"]
    "Allocate an exact heap Nat for the maximum UInt64",
  exactNatToUSizeExternalCase
    "nat-to-usize-small" ``Source.natToUSize Source.natToUSize
    ``USize.ofNat 17
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "to-fixed-width", "immediate-input", "i64", "semantic-lean64"]
    "Convert a small tagged Nat to an exact semantic Lean64 USize",
  exactNatToUSizeExternalCase
    "nat-to-usize-immediate-max" ``Source.natToUSize Source.natToUSize
    ``USize.ofNat 9223372036854775807
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "to-fixed-width", "immediate-input", "boundary", "i64", "semantic-lean64"]
    "Convert the maximum tagged Nat to Lean64 USize without losing high payload bits",
  exactNatToUSizeExternalCase
    "nat-to-usize-first-heap" ``Source.natToUSize Source.natToUSize
    ``USize.ofNat 9223372036854775808
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "boundary", "i64", "semantic-lean64"]
    "Convert the first heap Nat to semantic Lean64 USize at bit 63",
  exactNatToUSizeExternalCase
    "nat-to-usize-max" ``Source.natToUSize Source.natToUSize
    ``USize.ofNat 18446744073709551615
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "boundary", "maximum", "i64",
      "semantic-lean64"]
    "Convert the maximum in-range 64-bit Nat to maximum semantic Lean64 USize",
  exactNatToUSizeExternalCase
    "nat-to-usize-modulus" ``Source.natToUSize Source.natToUSize
    ``USize.ofNat 18446744073709551616
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "boundary", "overflow", "wraparound", "i64",
      "semantic-lean64"]
    "Wrap the first out-of-range Nat at exactly 2^64 to semantic Lean64 USize zero",
  exactNatToUSizeExternalCase
    "nat-to-usize-multi-limb" ``Source.natToUSize Source.natToUSize
    ``USize.ofNat 340282366920938463463374607431768211473
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "to-fixed-width", "heap-input", "multi-limb", "wraparound", "i64",
      "semantic-lean64"]
    "Reduce 2^128 + 17 modulo 2^64 while converting a multi-limb Nat to USize",
  exactUSizeToNatExternalCase
    "usize-to-nat-zero" ``Source.usizeToNat Source.usizeToNat
    ``USize.toNat 0
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "from-fixed-width", "immediate-result", "boundary", "i64", "semantic-lean64"]
    "Convert semantic Lean64 USize zero to a tagged Nat",
  exactUSizeToNatExternalCase
    "usize-to-nat-immediate-max" ``Source.usizeToNat Source.usizeToNat
    ``USize.toNat 0x7fffffffffffffff
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "from-fixed-width", "immediate-result", "boundary", "i64", "semantic-lean64"]
    "Convert bit-63-minus-one Lean64 USize to the maximum tagged Nat",
  exactUSizeToNatExternalCase
    "usize-to-nat-first-heap" ``Source.usizeToNat Source.usizeToNat
    ``USize.toNat 0x8000000000000000
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "from-fixed-width", "heap-result", "allocation", "boundary", "i64",
      "semantic-lean64"]
    "Allocate the first heap Nat while converting the Lean64 USize bit-63 boundary",
  exactUSizeToNatExternalCase
    "usize-to-nat-max" ``Source.usizeToNat Source.usizeToNat
    ``USize.toNat 0xffffffffffffffff
    #["stress", "usize", "usize-external", "external", "conversion", "nat",
      "from-fixed-width", "heap-result", "allocation", "boundary", "maximum", "i64",
      "semantic-lean64"]
    "Allocate an exact heap Nat for the maximum semantic Lean64 USize"
]

private def postConversionCases : Array Case := #[
  exactUSizeBinaryExternalCase
    "usize-add-overflow" ``Source.addUSize Source.addUSize ``USize.add
    0xffffffffffffffff 1
    #["stress", "usize", "usize-external", "external", "arithmetic", "addition",
      "overflow", "wraparound", "boundary", "i64", "semantic-lean64"]
    "Wrap maximum Lean64 USize plus one to zero through the native runtime external",
  exactUSizeBinaryExternalCase
    "usize-sub-underflow" ``Source.subUSize Source.subUSize ``USize.sub
    0 1
    #["stress", "usize", "usize-external", "external", "arithmetic", "subtraction",
      "underflow", "wraparound", "boundary", "i64", "semantic-lean64"]
    "Wrap Lean64 USize zero minus one to the maximum value",
  exactUSizeBinaryExternalCase
    "usize-mul-overflow" ``Source.mulUSize Source.mulUSize ``USize.mul
    0x8000000000000000 2
    #["stress", "usize", "usize-external", "external", "arithmetic",
      "multiplication", "overflow", "wraparound", "boundary", "i64",
      "semantic-lean64"]
    "Discard the high multiplication bit at the frozen Lean64 USize width",
  exactUSizeBinaryExternalCase
    "usize-div-floor" ``Source.divUSize Source.divUSize ``USize.div
    0xffffffffffffffff 3
    #["stress", "usize", "usize-external", "external", "arithmetic", "division",
      "floor", "boundary", "i64", "semantic-lean64"]
    "Compute unsigned floor division at the maximum Lean64 USize",
  exactUSizeBinaryExternalCase
    "usize-div-zero" ``Source.divUSize Source.divUSize ``USize.div
    0xffffffffffffffff 0
    #["stress", "usize", "usize-external", "external", "arithmetic", "division",
      "zero-divisor", "boundary", "i64", "semantic-lean64"]
    "Pin total Lean64 USize division by zero to zero",
  exactUSizeBinaryExternalCase
    "usize-mod-remainder" ``Source.modUSize Source.modUSize ``USize.mod
    0xffffffffffffffff 16
    #["stress", "usize", "usize-external", "external", "arithmetic", "remainder",
      "boundary", "i64", "semantic-lean64"]
    "Retain the low four bits as the Lean64 USize remainder",
  exactUSizeBinaryExternalCase
    "usize-mod-zero" ``Source.modUSize Source.modUSize ``USize.mod
    0xffffffffffffffff 0
    #["stress", "usize", "usize-external", "external", "arithmetic", "remainder",
      "zero-divisor", "boundary", "i64", "semantic-lean64"]
    "Pin Lean64 USize remainder by zero to the dividend",
  exactUSizeBinaryExternalCase
    "usize-land-mixed" ``Source.landUSize Source.landUSize ``USize.land
    0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0
    #["stress", "usize", "usize-external", "external", "bitwise", "and",
      "mixed-bits", "i64", "semantic-lean64"]
    "Intersect alternating Lean64 USize bit groups exactly",
  exactUSizeBinaryExternalCase
    "usize-lor-mixed" ``Source.lorUSize Source.lorUSize ``USize.lor
    0xf00000000000000f 0x0ff00ff00ff00ff0
    #["stress", "usize", "usize-external", "external", "bitwise", "or",
      "mixed-bits", "i64", "semantic-lean64"]
    "Union separated Lean64 USize bit groups across high and low boundaries",
  exactUSizeBinaryExternalCase
    "usize-xor-mixed" ``Source.xorUSize Source.xorUSize ``USize.xor
    0xf0f0f0f0f0f0f0f0 0x0ff00ff00ff00ff0
    #["stress", "usize", "usize-external", "external", "bitwise", "xor",
      "mixed-bits", "i64", "semantic-lean64"]
    "Exclusive-or alternating Lean64 USize bit groups exactly",
  exactUSizeBinaryExternalCase
    "usize-shift-left-count-64" ``Source.shiftLeftUSize Source.shiftLeftUSize
    ``USize.shiftLeft 0x8000000000000001 64
    #["stress", "usize", "usize-external", "external", "bitwise", "shift-left",
      "masked-count", "boundary", "i64", "semantic-lean64"]
    "Mask a Lean64 USize left-shift count of 64 to zero",
  exactUSizeBinaryExternalCase
    "usize-shift-left-count-65" ``Source.shiftLeftUSize Source.shiftLeftUSize
    ``USize.shiftLeft 0x8000000000000001 65
    #["stress", "usize", "usize-external", "external", "bitwise", "shift-left",
      "masked-count", "overflow", "boundary", "i64", "semantic-lean64"]
    "Mask a Lean64 USize left-shift count of 65 to one and discard the high bit",
  exactUSizeBinaryExternalCase
    "usize-shift-right-count-64" ``Source.shiftRightUSize Source.shiftRightUSize
    ``USize.shiftRight 0x8000000000000001 64
    #["stress", "usize", "usize-external", "external", "bitwise", "shift-right",
      "masked-count", "boundary", "i64", "semantic-lean64"]
    "Mask a Lean64 USize right-shift count of 64 to zero",
  exactUSizeBinaryExternalCase
    "usize-shift-right-count-65" ``Source.shiftRightUSize Source.shiftRightUSize
    ``USize.shiftRight 0x8000000000000001 65
    #["stress", "usize", "usize-external", "external", "bitwise", "shift-right",
      "masked-count", "logical", "boundary", "i64", "semantic-lean64"]
    "Mask a Lean64 USize right-shift count of 65 to one and shift logically",
  exactUSizeUnaryExternalCase
    "usize-complement-zero" ``Source.complementUSize Source.complementUSize
    ``USize.complement 0
    #["stress", "usize", "usize-external", "external", "bitwise", "complement",
      "boundary", "i64", "semantic-lean64"]
    "Complement Lean64 USize zero to the exact 64-bit maximum",
  exactUSizeUnaryExternalCase
    "usize-neg-one" ``Source.negUSize Source.negUSize ``USize.neg 1
    #["stress", "usize", "usize-external", "external", "arithmetic", "negation",
      "wraparound", "boundary", "i64", "semantic-lean64"]
    "Negate Lean64 USize one modulo 2^64",
  exactUSizeDecisionExternalCase
    "usize-dec-eq-max-true" ``Source.decideUSizeEq Source.decideUSizeEq
    ``USize.decEq 0xffffffffffffffff 0xffffffffffffffff
    #["stress", "usize", "usize-external", "external", "decision", "equality",
      "true", "boundary", "i64", "semantic-lean64"]
    "Decide equality of two maximum Lean64 USize values",
  exactUSizeDecisionExternalCase
    "usize-dec-eq-max-zero-false" ``Source.decideUSizeEq Source.decideUSizeEq
    ``USize.decEq 0xffffffffffffffff 0
    #["stress", "usize", "usize-external", "external", "decision", "equality",
      "false", "boundary", "i64", "semantic-lean64"]
    "Reject equality of maximum and zero Lean64 USize values",
  exactUSizeDecisionExternalCase
    "usize-dec-lt-zero-max-true" ``Source.decideUSizeLt Source.decideUSizeLt
    ``USize.decLt 0 0xffffffffffffffff
    #["stress", "usize", "usize-external", "external", "decision", "ordering",
      "less-than", "true", "boundary", "i64", "semantic-lean64"]
    "Order Lean64 USize zero strictly before the maximum",
  exactUSizeDecisionExternalCase
    "usize-dec-lt-max-zero-false" ``Source.decideUSizeLt Source.decideUSizeLt
    ``USize.decLt 0xffffffffffffffff 0
    #["stress", "usize", "usize-external", "external", "decision", "ordering",
      "less-than", "false", "boundary", "i64", "semantic-lean64"]
    "Reject strict unsigned ordering from maximum Lean64 USize to zero",
  exactUSizeDecisionExternalCase
    "usize-dec-le-max-max-true" ``Source.decideUSizeLe Source.decideUSizeLe
    ``USize.decLe 0xffffffffffffffff 0xffffffffffffffff
    #["stress", "usize", "usize-external", "external", "decision", "ordering",
      "less-or-equal", "true", "equality", "boundary", "i64",
      "semantic-lean64"]
    "Accept non-strict ordering at the Lean64 USize maximum",
  exactUSizeDecisionExternalCase
    "usize-dec-le-max-zero-false" ``Source.decideUSizeLe Source.decideUSizeLe
    ``USize.decLe 0xffffffffffffffff 0
    #["stress", "usize", "usize-external", "external", "decision", "ordering",
      "less-or-equal", "false", "boundary", "i64", "semantic-lean64"]
    "Reject non-strict unsigned ordering from maximum Lean64 USize to zero",
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
  { id := "mixed-closure-capture-once"
    entry := ``Source.captureMixedClosure
    dependencies := #[``Source.applyMixedClosureCapture]
    args := mixedClosureOnceArgs
    argSchemas := mixedClosureOnceArgSchemas
    resultSchema := .nat
    native := fun _ => .nat
      (Source.captureMixedClosure Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize 0xdeadbeef mixedClosureSingle mixedClosureDouble 99)
    tags :=
      #["stress", "closure", "closure-ownership", "capture", "partial-application",
        "mixed-layout", "constructor", "projection", "object", "usize", "scalar",
        "float", "float32", "float64", "exact-bits", "heap", "ownership", "unique",
        "single-use", "wasm-generation-pending"]
    requiredLcnfForms :=
      #["box", "pap", "fap", "fvar", "unbox", "dec", "ctor", "uset", "sset",
        "return", "oproj", "inc"]
    requiredExecutedLcnfForms :=
      #["box", "pap", "fap", "fvar", "unbox", "dec", "ctor", "uset", "sset",
        "return", "oproj", "inc"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "box", minimum := 4, maximum := some 4 },
        { form := "pap", minimum := 1, maximum := some 1 },
        { form := "fap", minimum := 2, maximum := some 2 },
        { form := "fvar", minimum := 1, maximum := some 1 },
        { form := "unbox", minimum := 4, maximum := some 4 },
        { form := "dec", minimum := 5, maximum := some 5 },
        { form := "ctor", minimum := 1, maximum := some 1 },
        { form := "uset", minimum := 1, maximum := some 1 },
        { form := "sset", minimum := 3, maximum := some 3 },
        { form := "return", minimum := 4, maximum := some 4 },
        { form := "oproj", minimum := 1, maximum := some 1 },
        { form := "inc", minimum := 1, maximum := some 1 }]
    requiredExecutedLcnfFormTrace := some mixedClosureOnceFormTrace
    requiredAdministrativeStepKinds :=
      #["admin:invoke-name", "admin:invoke-value", "admin:yield-bind", "admin:yield-done"]
    provenance := firProvenance
      "Consume one mixed-kind closure application and observe its argument projection" },
  { id := "mixed-closure-capture-twice"
    entry := ``Source.captureMixedClosureTwice
    dependencies := #[``Source.applyMixedClosureCaptureTwice]
    args := mixedClosureTwiceArgs
    argSchemas := mixedClosureTwiceArgSchemas
    resultSchema := .ctor "Prod.mk" 0 #[.nat, .nat]
    native := fun _ => natPairDatum
      (Source.captureMixedClosureTwice Source.largeNat mixedLayoutText mixedLayoutBytes
        Source.maxUSize 0xdeadbeef mixedClosureSingle mixedClosureDouble 17
        340282366920938463463374607431768211473)
    tags :=
      #["stress", "closure", "closure-ownership", "capture", "partial-application",
        "mixed-layout", "constructor", "projection", "object", "usize", "scalar",
        "float", "float32", "float64", "exact-bits", "heap", "ownership", "shared",
        "multiplicity", "repeated-application", "wasm-generation-pending"]
    requiredLcnfForms :=
      #["box", "pap", "fap", "inc", "fvar", "unbox", "dec", "ctor", "uset",
        "sset", "return", "oproj"]
    requiredExecutedLcnfForms :=
      #["box", "pap", "fap", "inc", "fvar", "unbox", "dec", "ctor", "uset",
        "sset", "return", "oproj"]
    requiredExecutedLcnfFormCounts :=
      #[{ form := "box", minimum := 4, maximum := some 4 },
        { form := "pap", minimum := 1, maximum := some 1 },
        { form := "fap", minimum := 3, maximum := some 3 },
        { form := "inc", minimum := 3, maximum := some 3 },
        { form := "fvar", minimum := 2, maximum := some 2 },
        { form := "unbox", minimum := 8, maximum := some 8 },
        { form := "dec", minimum := 10, maximum := some 10 },
        { form := "ctor", minimum := 3, maximum := some 3 },
        { form := "uset", minimum := 2, maximum := some 2 },
        { form := "sset", minimum := 6, maximum := some 6 },
        { form := "return", minimum := 6, maximum := some 6 },
        { form := "oproj", minimum := 2, maximum := some 2 }]
    requiredExecutedLcnfFormTrace := some mixedClosureTwiceFormTrace
    requiredAdministrativeStepKinds :=
      #["admin:invoke-name", "admin:invoke-value", "admin:yield-bind", "admin:yield-done"]
    provenance := firProvenance
      "Apply one shared mixed-kind closure twice and preserve both argument projections" },
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
  exactIntNatExternalCase
    "int-shift-left-positive-immediate-to-heap"
    ``Source.shiftLeftInt Source.shiftLeftInt ``Int.shiftLeft
    2147483647
    1
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-left",
      "positive", "immediate-input", "heap-result", "boundary"]
    "Shift the positive immediate Int maximum into the heap representation",
  exactIntNatExternalCase
    "int-shift-left-negative-immediate-to-heap"
    ``Source.shiftLeftInt Source.shiftLeftInt ``Int.shiftLeft
    (-2147483648)
    1
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-left",
      "negative", "immediate-input", "heap-result", "boundary"]
    "Shift the negative immediate Int minimum into the heap representation",
  exactIntNatExternalCase
    "int-shift-left-multi-limb-positive"
    ``Source.shiftLeftInt Source.shiftLeftInt ``Int.shiftLeft
    340282366920938463463374607431768211473
    65
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-left",
      "positive", "heap", "multi-limb", "growth", "cross-limb"]
    "Shift a positive multi-limb Int left across a limb boundary",
  exactIntNatExternalCase
    "int-shift-left-multi-limb-negative"
    ``Source.shiftLeftInt Source.shiftLeftInt ``Int.shiftLeft
    (-340282366920938463463374607431768211473)
    65
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-left",
      "negative", "heap", "multi-limb", "growth", "cross-limb"]
    "Shift a negative multi-limb Int left while preserving its sign",
  exactIntNatExternalCase
    "int-shift-right-multi-limb-positive"
    ``Source.shiftRightInt Source.shiftRightInt ``Int.shiftRight
    340282366920938463463374607431768211473
    65
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-right",
      "positive", "heap", "multi-limb", "cross-limb"]
    "Shift a positive multi-limb Int right across a limb boundary",
  exactIntNatExternalCase
    "int-shift-right-multi-limb-negative"
    ``Source.shiftRightInt Source.shiftRightInt ``Int.shiftRight
    (-340282366920938463463374607431768211473)
    65
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-right",
      "negative", "heap", "multi-limb", "cross-limb", "sign-extension"]
    "Arithmetic-shift a negative multi-limb Int across a limb boundary",
  exactIntNatExternalCase
    "int-shift-right-positive-heap-to-immediate"
    ``Source.shiftRightInt Source.shiftRightInt ``Int.shiftRight
    340282366920938463463374607431768211473
    128
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-right",
      "positive", "heap-input", "multi-limb", "immediate-result",
      "normalization"]
    "Shift a positive multi-limb Int down to immediate one",
  exactIntNatExternalCase
    "int-shift-right-negative-sign-extension"
    ``Source.shiftRightInt Source.shiftRightInt ``Int.shiftRight
    (-340282366920938463463374607431768211473)
    129
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-right",
      "negative", "heap-input", "multi-limb", "immediate-result",
      "sign-extension", "boundary"]
    "Shift past a negative multi-limb Int and retain arithmetic sign extension",
  exactIntNatExternalCase
    "int-shift-right-negative-multi-limb-count"
    ``Source.shiftRightInt Source.shiftRightInt ``Int.shiftRight
    (-340282366920938463463374607431768211473)
    340282366920938463463374607431768211473
    #["stress", "int", "signed", "external", "bitwise", "int-shift", "shift-right",
      "negative", "heap-input", "multi-limb", "multi-limb-count",
      "oversized-count", "immediate-result", "sign-extension"]
    "Use a multi-limb count while arithmetic-shifting a negative Int to minus one",
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

private def int8Value (value : Int) : Int8 :=
  Int8.ofInt value

private def int8Cases : Array Case := #[
  exactInt8BinaryExternalCase
    "int8-add-overflow" ``Source.addInt8 Source.addInt8 ``Int8.add
    (int8Value 127) (int8Value 1)
    #["stress", "scalar", "int8", "signed", "arithmetic", "addition",
      "overflow", "wraparound", "boundary", "i32"]
    "Wrap signed Int8 maximum plus one to the minimum two's-complement value",
  exactInt8BinaryExternalCase
    "int8-sub-underflow" ``Source.subInt8 Source.subInt8 ``Int8.sub
    (int8Value (-128)) (int8Value 1)
    #["stress", "scalar", "int8", "signed", "arithmetic", "subtraction",
      "underflow", "wraparound", "boundary", "i32"]
    "Wrap signed Int8 minimum minus one to the maximum value",
  exactInt8BinaryExternalCase
    "int8-mul-overflow" ``Source.mulInt8 Source.mulInt8 ``Int8.mul
    (int8Value 64) (int8Value 2)
    #["stress", "scalar", "int8", "signed", "arithmetic", "multiplication",
      "overflow", "wraparound", "boundary", "i32"]
    "Wrap the exact high multiplication bit into the Int8 sign bit",
  exactInt8BinaryExternalCase
    "int8-div-negative-truncates" ``Source.divInt8 Source.divInt8 ``Int8.div
    (int8Value (-7)) (int8Value 3)
    #["stress", "scalar", "int8", "signed", "arithmetic", "division",
      "negative", "truncate-zero", "boundary", "i32"]
    "Truncate signed Int8 division of negative seven by positive three toward zero",
  exactInt8BinaryExternalCase
    "int8-div-min-neg-one" ``Source.divInt8 Source.divInt8 ``Int8.div
    (int8Value (-128)) (int8Value (-1))
    #["stress", "scalar", "int8", "signed", "arithmetic", "division",
      "overflow", "wraparound", "minimum", "boundary", "i32"]
    "Wrap the unique overflowing signed Int8 quotient min / -1 back to min",
  exactInt8BinaryExternalCase
    "int8-div-zero" ``Source.divInt8 Source.divInt8 ``Int8.div
    (int8Value (-7)) (int8Value 0)
    #["stress", "scalar", "int8", "signed", "arithmetic", "division",
      "negative", "zero-divisor", "boundary", "i32"]
    "Pin total signed Int8 division by zero to zero",
  exactInt8BinaryExternalCase
    "int8-mod-negative-dividend" ``Source.modInt8 Source.modInt8 ``Int8.mod
    (int8Value (-7)) (int8Value 3)
    #["stress", "scalar", "int8", "signed", "arithmetic", "remainder",
      "negative-dividend", "truncate-zero", "boundary", "i32"]
    "Retain the dividend sign for signed Int8 remainder of negative seven by three",
  exactInt8BinaryExternalCase
    "int8-mod-negative-divisor" ``Source.modInt8 Source.modInt8 ``Int8.mod
    (int8Value 7) (int8Value (-3))
    #["stress", "scalar", "int8", "signed", "arithmetic", "remainder",
      "negative-divisor", "truncate-zero", "boundary", "i32"]
    "Keep a positive signed Int8 remainder when only the divisor is negative",
  exactInt8BinaryExternalCase
    "int8-mod-zero" ``Source.modInt8 Source.modInt8 ``Int8.mod
    (int8Value (-7)) (int8Value 0)
    #["stress", "scalar", "int8", "signed", "arithmetic", "remainder",
      "negative", "zero-divisor", "boundary", "i32"]
    "Pin signed Int8 remainder by zero to the dividend",
  exactInt8BinaryExternalCase
    "int8-land-mixed" ``Source.landInt8 Source.landInt8 ``Int8.land
    (int8Value (-16)) (int8Value 60)
    #["stress", "scalar", "int8", "signed", "bitwise", "and",
      "mixed-bits", "twos-complement", "i32"]
    "Intersect negative and positive Int8 two's-complement bit groups",
  exactInt8BinaryExternalCase
    "int8-lor-mixed" ``Source.lorInt8 Source.lorInt8 ``Int8.lor
    (int8Value (-64)) (int8Value 60)
    #["stress", "scalar", "int8", "signed", "bitwise", "or",
      "mixed-bits", "twos-complement", "i32"]
    "Union negative and positive Int8 two's-complement bit groups",
  exactInt8BinaryExternalCase
    "int8-xor-mixed" ``Source.xorInt8 Source.xorInt8 ``Int8.xor
    (int8Value (-16)) (int8Value 60)
    #["stress", "scalar", "int8", "signed", "bitwise", "xor",
      "mixed-bits", "twos-complement", "i32"]
    "Exclusive-or negative and positive Int8 two's-complement bit groups",
  exactInt8BinaryExternalCase
    "int8-shift-left-negative-width" ``Source.shiftLeftInt8 Source.shiftLeftInt8
    ``Int8.shiftLeft (int8Value (-127)) (int8Value (-8))
    #["stress", "scalar", "int8", "signed", "bitwise", "shift-left",
      "negative-count", "masked-count", "identity", "boundary", "i32"]
    "Reduce a signed Int8 left-shift count of negative eight to zero",
  exactInt8BinaryExternalCase
    "int8-shift-left-negative-one" ``Source.shiftLeftInt8 Source.shiftLeftInt8
    ``Int8.shiftLeft (int8Value (-127)) (int8Value (-1))
    #["stress", "scalar", "int8", "signed", "bitwise", "shift-left",
      "negative-count", "masked-count", "overflow", "boundary", "i32"]
    "Reduce a signed Int8 left-shift count of negative one to seven",
  exactInt8BinaryExternalCase
    "int8-shift-left-width-plus-one" ``Source.shiftLeftInt8 Source.shiftLeftInt8
    ``Int8.shiftLeft (int8Value (-127)) (int8Value 9)
    #["stress", "scalar", "int8", "signed", "bitwise", "shift-left",
      "oversized-count", "masked-count", "overflow", "boundary", "i32"]
    "Reduce a signed Int8 left-shift count of nine to one",
  exactInt8BinaryExternalCase
    "int8-shift-right-negative-width" ``Source.shiftRightInt8 Source.shiftRightInt8
    ``Int8.shiftRight (int8Value (-127)) (int8Value (-8))
    #["stress", "scalar", "int8", "signed", "bitwise", "shift-right",
      "negative-count", "masked-count", "arithmetic", "identity", "boundary", "i32"]
    "Reduce a signed Int8 arithmetic-right-shift count of negative eight to zero",
  exactInt8BinaryExternalCase
    "int8-shift-right-negative-one" ``Source.shiftRightInt8 Source.shiftRightInt8
    ``Int8.shiftRight (int8Value (-127)) (int8Value (-1))
    #["stress", "scalar", "int8", "signed", "bitwise", "shift-right",
      "negative-count", "masked-count", "arithmetic", "sign-extension",
      "boundary", "i32"]
    "Reduce a signed Int8 right-shift count of negative one to seven and extend the sign",
  exactInt8BinaryExternalCase
    "int8-shift-right-width-plus-one" ``Source.shiftRightInt8 Source.shiftRightInt8
    ``Int8.shiftRight (int8Value (-127)) (int8Value 9)
    #["stress", "scalar", "int8", "signed", "bitwise", "shift-right",
      "oversized-count", "masked-count", "arithmetic", "sign-extension",
      "boundary", "i32"]
    "Reduce a signed Int8 arithmetic-right-shift count of nine to one",
  exactInt8UnaryExternalCase
    "int8-complement-zero" ``Source.complementInt8 Source.complementInt8
    ``Int8.complement (int8Value 0)
    #["stress", "scalar", "int8", "signed", "bitwise", "complement",
      "twos-complement", "boundary", "i32"]
    "Complement Int8 zero to negative one in two's-complement representation",
  exactInt8UnaryExternalCase
    "int8-neg-min" ``Source.negInt8 Source.negInt8 ``Int8.neg
    (int8Value (-128))
    #["stress", "scalar", "int8", "signed", "arithmetic", "negation",
      "minimum", "overflow", "wraparound", "boundary", "i32"]
    "Wrap negation of the signed Int8 minimum back to itself",
  exactInt8UnaryExternalCase
    "int8-abs-negative" ``Source.absInt8 Source.absInt8 ``Int8.abs
    (int8Value (-7))
    #["stress", "scalar", "int8", "signed", "arithmetic", "absolute-value",
      "negative", "i32"]
    "Compute a representable positive Int8 absolute value",
  exactInt8UnaryExternalCase
    "int8-abs-min" ``Source.absInt8 Source.absInt8 ``Int8.abs
    (int8Value (-128))
    #["stress", "scalar", "int8", "signed", "arithmetic", "absolute-value",
      "minimum", "overflow", "wraparound", "boundary", "i32"]
    "Wrap the unrepresentable absolute value of the Int8 minimum back to itself",
  exactInt8DecisionExternalCase
    "int8-dec-eq-negative-true" ``Source.decideInt8Eq Source.decideInt8Eq
    ``Int8.decEq (int8Value (-1)) (int8Value (-1))
    #["stress", "scalar", "int8", "signed", "decision", "equality",
      "negative", "true", "boundary", "i32"]
    "Decide equality of two negative-one Int8 values",
  exactInt8DecisionExternalCase
    "int8-dec-eq-sign-false" ``Source.decideInt8Eq Source.decideInt8Eq
    ``Int8.decEq (int8Value (-1)) (int8Value 1)
    #["stress", "scalar", "int8", "signed", "decision", "equality",
      "opposite-sign", "false", "boundary", "i32"]
    "Reject equality of opposite-sign Int8 bit patterns",
  exactInt8DecisionExternalCase
    "int8-dec-lt-negative-zero-true" ``Source.decideInt8Lt Source.decideInt8Lt
    ``Int8.decLt (int8Value (-1)) (int8Value 0)
    #["stress", "scalar", "int8", "signed", "decision", "ordering",
      "less-than", "opposite-sign", "true", "boundary", "i32"]
    "Order negative one before zero using signed Int8 comparison",
  exactInt8DecisionExternalCase
    "int8-dec-lt-max-min-false" ``Source.decideInt8Lt Source.decideInt8Lt
    ``Int8.decLt (int8Value 127) (int8Value (-128))
    #["stress", "scalar", "int8", "signed", "decision", "ordering",
      "less-than", "opposite-sign", "false", "boundary", "i32"]
    "Reject unsigned-style ordering of the Int8 maximum before the minimum",
  exactInt8DecisionExternalCase
    "int8-dec-le-min-min-true" ``Source.decideInt8Le Source.decideInt8Le
    ``Int8.decLe (int8Value (-128)) (int8Value (-128))
    #["stress", "scalar", "int8", "signed", "decision", "ordering",
      "less-or-equal", "minimum", "equality", "true", "boundary", "i32"]
    "Accept non-strict signed Int8 ordering at the minimum",
  exactInt8DecisionExternalCase
    "int8-dec-le-zero-negative-false" ``Source.decideInt8Le Source.decideInt8Le
    ``Int8.decLe (int8Value 0) (int8Value (-1))
    #["stress", "scalar", "int8", "signed", "decision", "ordering",
      "less-or-equal", "opposite-sign", "false", "boundary", "i32"]
    "Reject non-strict signed Int8 ordering from zero to negative one",
  exactNatToInt8ExternalCase
    "nat-to-int8-max-encoding" ``Source.natToInt8 Source.natToInt8
    ``Int8.ofNat 255
    #["stress", "scalar", "int8", "signed", "conversion", "nat",
      "maximum-encoding", "negative-result", "boundary", "i32"]
    "Wrap Nat 255 to the negative-one Int8 bit pattern",
  exactNatToInt8ExternalCase
    "nat-to-int8-modulus" ``Source.natToInt8 Source.natToInt8
    ``Int8.ofNat 256
    #["stress", "scalar", "int8", "signed", "conversion", "nat",
      "modulus", "overflow", "wraparound", "boundary", "i32"]
    "Wrap Nat 256 at the exact Int8 modulus to zero",
  exactNatToInt8ExternalCase
    "nat-to-int8-multi-limb" ``Source.natToInt8 Source.natToInt8
    ``Int8.ofNat 340282366920938463463374607431768211473
    #["stress", "scalar", "int8", "signed", "conversion", "nat",
      "heap-input", "multi-limb", "wraparound", "i32"]
    "Reduce 2^128 + 17 modulo 2^8 while converting a multi-limb Nat to Int8",
  exactIntToInt8ExternalCase
    "int-to-int8-positive-overflow" ``Source.intToInt8 Source.intToInt8
    ``Int8.ofInt 128
    #["stress", "scalar", "int8", "signed", "conversion", "int",
      "positive", "overflow", "wraparound", "boundary", "i32"]
    "Wrap Int 128 to the signed Int8 minimum",
  exactIntToInt8ExternalCase
    "int-to-int8-negative-underflow" ``Source.intToInt8 Source.intToInt8
    ``Int8.ofInt (-129)
    #["stress", "scalar", "int8", "signed", "conversion", "int",
      "negative", "underflow", "wraparound", "boundary", "i32"]
    "Wrap Int negative 129 to the signed Int8 maximum",
  exactIntToInt8ExternalCase
    "int-to-int8-multi-limb-positive" ``Source.intToInt8 Source.intToInt8
    ``Int8.ofInt 340282366920938463463374607431768211473
    #["stress", "scalar", "int8", "signed", "conversion", "int",
      "positive", "heap-input", "multi-limb", "wraparound", "i32"]
    "Reduce positive 2^128 + 17 modulo 2^8 while converting a heap Int to Int8",
  exactIntToInt8ExternalCase
    "int-to-int8-multi-limb-negative" ``Source.intToInt8 Source.intToInt8
    ``Int8.ofInt (-340282366920938463463374607431768211473)
    #["stress", "scalar", "int8", "signed", "conversion", "int",
      "negative", "heap-input", "multi-limb", "wraparound", "i32"]
    "Reduce negative 2^128 + 17 modulo 2^8 while converting a heap Int to Int8",
  exactInt8ToIntExternalCase
    "int8-to-int-min" ``Source.int8ToInt Source.int8ToInt
    ``Int8.toInt (int8Value (-128))
    #["stress", "scalar", "int8", "signed", "conversion", "int",
      "negative-result", "minimum", "immediate-result", "boundary", "i32"]
    "Sign-extend the signed Int8 minimum to an exact immediate Int",
  exactInt8ToIntExternalCase
    "int8-to-int-max" ``Source.int8ToInt Source.int8ToInt
    ``Int8.toInt (int8Value 127)
    #["stress", "scalar", "int8", "signed", "conversion", "int",
      "positive-result", "maximum", "immediate-result", "boundary", "i32"]
    "Sign-extend the signed Int8 maximum to an exact immediate Int"
]

private structure SignedFixedWidthCaseFamily (α : Type) where
  typeName : Lean.Name
  typeId : String
  sourceSuffix : String
  width : Nat
  wasmLaneTag : String
  codec : FixedWidthCaseCodec α
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

private def signedFixedWidthCases
    (family : SignedFixedWidthCaseFamily α) : Array Case :=
  let externalName (suffix : String) := Lean.Name.str family.typeName suffix
  let sourceNamespace := (``Source.addInt16).getPrefix
  let sourceName (stem : String) :=
    Lean.Name.str sourceNamespace (stem ++ family.sourceSuffix)
  let value := family.ofInt
  let magnitude : Nat := 2 ^ (family.width - 1)
  let minimum : Int := -(Int.ofNat magnitude)
  let maximum : Int := Int.ofNat (magnitude - 1)
  let nearMinimum := minimum + 1
  let tags (category : String) (extra : Array String) : Array String :=
    #["stress", "scalar", family.typeId, "signed", category] ++
      extra ++ #[family.wasmLaneTag]
  #[
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-add-overflow" (sourceName "add") family.add
      (externalName "add") (value maximum) (value 1)
      (tags "arithmetic" #["addition", "overflow", "wraparound", "boundary"])
      s!"Wrap the signed {family.typeId} maximum plus one to its minimum",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-sub-underflow" (sourceName "sub") family.sub
      (externalName "sub") (value minimum) (value 1)
      (tags "arithmetic" #["subtraction", "underflow", "wraparound", "boundary"])
      s!"Wrap the signed {family.typeId} minimum minus one to its maximum",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-mul-overflow" (sourceName "mul") family.mul
      (externalName "mul") (value (Int.ofNat (2 ^ (family.width - 2)))) (value 2)
      (tags "arithmetic" #["multiplication", "overflow", "wraparound", "boundary"])
      s!"Wrap the exact high multiplication bit into the {family.typeId} sign bit",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-div-negative-truncates" (sourceName "div") family.div
      (externalName "div") (value (-7)) (value 3)
      (tags "arithmetic" #["division", "negative", "truncate-zero", "boundary"])
      s!"Truncate signed {family.typeId} division toward zero",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-div-min-neg-one" (sourceName "div") family.div
      (externalName "div") (value minimum) (value (-1))
      (tags "arithmetic"
        #["division", "overflow", "wraparound", "minimum", "boundary"])
      s!"Wrap the unique overflowing {family.typeId} quotient min / -1 back to min",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-div-zero" (sourceName "div") family.div
      (externalName "div") (value (-7)) (value 0)
      (tags "arithmetic" #["division", "negative", "zero-divisor", "boundary"])
      s!"Pin total signed {family.typeId} division by zero to zero",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-mod-negative-dividend" (sourceName "mod") family.modulo
      (externalName "mod") (value (-7)) (value 3)
      (tags "arithmetic"
        #["remainder", "negative-dividend", "truncate-zero", "boundary"])
      s!"Retain the dividend sign for signed {family.typeId} remainder",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-mod-negative-divisor" (sourceName "mod") family.modulo
      (externalName "mod") (value 7) (value (-3))
      (tags "arithmetic"
        #["remainder", "negative-divisor", "truncate-zero", "boundary"])
      s!"Keep a positive {family.typeId} remainder when only the divisor is negative",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-mod-zero" (sourceName "mod") family.modulo
      (externalName "mod") (value (-7)) (value 0)
      (tags "arithmetic" #["remainder", "negative", "zero-divisor", "boundary"])
      s!"Pin signed {family.typeId} remainder by zero to the dividend",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-land-mixed" (sourceName "land") family.land
      (externalName "land") (value (-16)) (value 60)
      (tags "bitwise" #["and", "mixed-bits", "twos-complement"])
      s!"Intersect negative and positive {family.typeId} bit groups",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-lor-mixed" (sourceName "lor") family.lor
      (externalName "lor") (value (-64)) (value 60)
      (tags "bitwise" #["or", "mixed-bits", "twos-complement"])
      s!"Union negative and positive {family.typeId} bit groups",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-xor-mixed" (sourceName "xor") family.xor
      (externalName "xor") (value (-16)) (value 60)
      (tags "bitwise" #["xor", "mixed-bits", "twos-complement"])
      s!"Exclusive-or negative and positive {family.typeId} bit groups",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-shift-left-negative-width" (sourceName "shiftLeft")
      family.shiftLeft (externalName "shiftLeft")
      (value nearMinimum) (value (-(Int.ofNat family.width)))
      (tags "bitwise"
        #["shift-left", "negative-count", "masked-count", "identity", "boundary"])
      s!"Reduce a negative-width {family.typeId} left-shift count to zero",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-shift-left-negative-one" (sourceName "shiftLeft")
      family.shiftLeft (externalName "shiftLeft")
      (value nearMinimum) (value (-1))
      (tags "bitwise"
        #["shift-left", "negative-count", "masked-count", "overflow", "boundary"])
      s!"Reduce a negative-one {family.typeId} left-shift count to width minus one",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-shift-left-width-plus-one" (sourceName "shiftLeft")
      family.shiftLeft (externalName "shiftLeft")
      (value nearMinimum) (value (Int.ofNat family.width + 1))
      (tags "bitwise"
        #["shift-left", "oversized-count", "masked-count", "overflow", "boundary"])
      s!"Reduce a width-plus-one {family.typeId} left-shift count to one",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-shift-right-negative-width" (sourceName "shiftRight")
      family.shiftRight (externalName "shiftRight")
      (value nearMinimum) (value (-(Int.ofNat family.width)))
      (tags "bitwise"
        #["shift-right", "negative-count", "masked-count", "arithmetic",
          "identity", "boundary"])
      s!"Reduce a negative-width {family.typeId} right-shift count to zero",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-shift-right-negative-one" (sourceName "shiftRight")
      family.shiftRight (externalName "shiftRight")
      (value nearMinimum) (value (-1))
      (tags "bitwise"
        #["shift-right", "negative-count", "masked-count", "arithmetic",
          "sign-extension", "boundary"])
      s!"Reduce a negative-one {family.typeId} arithmetic shift to width minus one",
    exactFixedWidthBinaryExternalCase family.codec
      s!"{family.typeId}-shift-right-width-plus-one" (sourceName "shiftRight")
      family.shiftRight (externalName "shiftRight")
      (value nearMinimum) (value (Int.ofNat family.width + 1))
      (tags "bitwise"
        #["shift-right", "oversized-count", "masked-count", "arithmetic",
          "sign-extension", "boundary"])
      s!"Reduce a width-plus-one {family.typeId} arithmetic shift to one",
    exactFixedWidthUnaryExternalCase family.codec
      s!"{family.typeId}-complement-zero" (sourceName "complement") family.complement
      (externalName "complement") (value 0)
      (tags "bitwise" #["complement", "twos-complement", "boundary"])
      s!"Complement {family.typeId} zero to negative one",
    exactFixedWidthUnaryExternalCase family.codec
      s!"{family.typeId}-neg-min" (sourceName "neg") family.neg
      (externalName "neg") (value minimum)
      (tags "arithmetic"
        #["negation", "minimum", "overflow", "wraparound", "boundary"])
      s!"Wrap negation of the signed {family.typeId} minimum back to itself",
    exactFixedWidthUnaryExternalCase family.codec
      s!"{family.typeId}-abs-negative" (sourceName "abs") family.abs
      (externalName "abs") (value (-7))
      (tags "arithmetic" #["absolute-value", "negative"])
      s!"Compute a representable positive {family.typeId} absolute value",
    exactFixedWidthUnaryExternalCase family.codec
      s!"{family.typeId}-abs-min" (sourceName "abs") family.abs
      (externalName "abs") (value minimum)
      (tags "arithmetic"
        #["absolute-value", "minimum", "overflow", "wraparound", "boundary"])
      s!"Wrap the unrepresentable {family.typeId} minimum absolute value",
    exactFixedWidthDecisionExternalCase family.codec
      s!"{family.typeId}-dec-eq-negative-true" (Lean.Name.str sourceNamespace
        s!"decide{family.sourceSuffix}Eq") family.decEq (externalName "decEq")
      (value (-1)) (value (-1))
      (tags "decision" #["equality", "negative", "true", "boundary"])
      s!"Decide equality of two negative-one {family.typeId} values",
    exactFixedWidthDecisionExternalCase family.codec
      s!"{family.typeId}-dec-eq-sign-false" (Lean.Name.str sourceNamespace
        s!"decide{family.sourceSuffix}Eq") family.decEq (externalName "decEq")
      (value (-1)) (value 1)
      (tags "decision" #["equality", "opposite-sign", "false", "boundary"])
      s!"Reject equality of opposite-sign {family.typeId} values",
    exactFixedWidthDecisionExternalCase family.codec
      s!"{family.typeId}-dec-lt-negative-zero-true" (Lean.Name.str sourceNamespace
        s!"decide{family.sourceSuffix}Lt") family.decLt (externalName "decLt")
      (value (-1)) (value 0)
      (tags "decision"
        #["ordering", "less-than", "opposite-sign", "true", "boundary"])
      s!"Order negative one before zero using signed {family.typeId} comparison",
    exactFixedWidthDecisionExternalCase family.codec
      s!"{family.typeId}-dec-lt-max-min-false" (Lean.Name.str sourceNamespace
        s!"decide{family.sourceSuffix}Lt") family.decLt (externalName "decLt")
      (value maximum) (value minimum)
      (tags "decision"
        #["ordering", "less-than", "opposite-sign", "false", "boundary"])
      s!"Reject unsigned-style ordering of {family.typeId} maximum before minimum",
    exactFixedWidthDecisionExternalCase family.codec
      s!"{family.typeId}-dec-le-min-min-true" (Lean.Name.str sourceNamespace
        s!"decide{family.sourceSuffix}Le") family.decLe (externalName "decLe")
      (value minimum) (value minimum)
      (tags "decision"
        #["ordering", "less-or-equal", "minimum", "equality", "true", "boundary"])
      s!"Accept non-strict signed {family.typeId} ordering at the minimum",
    exactFixedWidthDecisionExternalCase family.codec
      s!"{family.typeId}-dec-le-zero-negative-false" (Lean.Name.str sourceNamespace
        s!"decide{family.sourceSuffix}Le") family.decLe (externalName "decLe")
      (value 0) (value (-1))
      (tags "decision"
        #["ordering", "less-or-equal", "opposite-sign", "false", "boundary"])
      s!"Reject non-strict signed {family.typeId} ordering from zero to negative one",
    exactNatToFixedWidthExternalCase family.codec
      s!"nat-to-{family.typeId}-max-encoding" (sourceName "natTo") family.ofNat
      (externalName "ofNat") (2 ^ family.width - 1)
      (tags "conversion"
        #["nat", "maximum-encoding", "negative-result", "boundary"])
      s!"Wrap the all-one Nat encoding to negative-one {family.typeId}",
    exactNatToFixedWidthExternalCase family.codec
      s!"nat-to-{family.typeId}-modulus" (sourceName "natTo") family.ofNat
      (externalName "ofNat") (2 ^ family.width)
      (tags "conversion" #["nat", "modulus", "overflow", "wraparound", "boundary"])
      s!"Wrap the exact {family.typeId} modulus to zero",
    exactNatToFixedWidthExternalCase family.codec
      s!"nat-to-{family.typeId}-multi-limb" (sourceName "natTo") family.ofNat
      (externalName "ofNat") 340282366920938463463374607431768211473
      (tags "conversion" #["nat", "heap-input", "multi-limb", "wraparound"])
      s!"Reduce 2^128 + 17 modulo the {family.typeId} width",
    exactIntToFixedWidthExternalCase family.codec
      s!"int-to-{family.typeId}-positive-overflow" (sourceName "intTo") family.ofInt
      (externalName "ofInt") (maximum + 1)
      (tags "conversion"
        #["int", "positive", "overflow", "wraparound", "boundary"])
      s!"Wrap maximum plus one to the signed {family.typeId} minimum",
    exactIntToFixedWidthExternalCase family.codec
      s!"int-to-{family.typeId}-negative-underflow" (sourceName "intTo") family.ofInt
      (externalName "ofInt") (minimum - 1)
      (tags "conversion"
        #["int", "negative", "underflow", "wraparound", "boundary"])
      s!"Wrap minimum minus one to the signed {family.typeId} maximum",
    exactIntToFixedWidthExternalCase family.codec
      s!"int-to-{family.typeId}-multi-limb-positive" (sourceName "intTo") family.ofInt
      (externalName "ofInt") 340282366920938463463374607431768211473
      (tags "conversion"
        #["int", "positive", "heap-input", "multi-limb", "wraparound"])
      s!"Reduce positive 2^128 + 17 modulo the {family.typeId} width",
    exactIntToFixedWidthExternalCase family.codec
      s!"int-to-{family.typeId}-multi-limb-negative" (sourceName "intTo") family.ofInt
      (externalName "ofInt") (-340282366920938463463374607431768211473)
      (tags "conversion"
        #["int", "negative", "heap-input", "multi-limb", "wraparound"])
      s!"Reduce negative 2^128 + 17 modulo the {family.typeId} width",
    exactFixedWidthToIntExternalCase family.codec
      s!"{family.typeId}-to-int-min"
      (Lean.Name.str sourceNamespace s!"{family.typeId}ToInt")
      family.toInt (externalName "toInt") (value minimum)
      (tags "conversion" #["int", "negative-result", "minimum", "boundary"])
      s!"Sign-extend the signed {family.typeId} minimum to an exact Int",
    exactFixedWidthToIntExternalCase family.codec
      s!"{family.typeId}-to-int-max"
      (Lean.Name.str sourceNamespace s!"{family.typeId}ToInt")
      family.toInt (externalName "toInt") (value maximum)
      (tags "conversion" #["int", "positive-result", "maximum", "boundary"])
      s!"Sign-extend the signed {family.typeId} maximum to an exact Int"
  ]

private def int16CaseFamily : SignedFixedWidthCaseFamily Int16 where
  typeName := ``Int16
  typeId := "int16"
  sourceSuffix := "Int16"
  width := 16
  wasmLaneTag := "i32"
  codec := int16CaseCodec
  ofNat := Source.natToInt16
  ofInt := Source.intToInt16
  toInt := Source.int16ToInt
  add := Source.addInt16
  sub := Source.subInt16
  mul := Source.mulInt16
  div := Source.divInt16
  modulo := Source.modInt16
  land := Source.landInt16
  lor := Source.lorInt16
  xor := Source.xorInt16
  shiftLeft := Source.shiftLeftInt16
  shiftRight := Source.shiftRightInt16
  complement := Source.complementInt16
  neg := Source.negInt16
  abs := Source.absInt16
  decEq := Source.decideInt16Eq
  decLt := Source.decideInt16Lt
  decLe := Source.decideInt16Le

private def int32CaseFamily : SignedFixedWidthCaseFamily Int32 where
  typeName := ``Int32
  typeId := "int32"
  sourceSuffix := "Int32"
  width := 32
  wasmLaneTag := "i32"
  codec := int32CaseCodec
  ofNat := Source.natToInt32
  ofInt := Source.intToInt32
  toInt := Source.int32ToInt
  add := Source.addInt32
  sub := Source.subInt32
  mul := Source.mulInt32
  div := Source.divInt32
  modulo := Source.modInt32
  land := Source.landInt32
  lor := Source.lorInt32
  xor := Source.xorInt32
  shiftLeft := Source.shiftLeftInt32
  shiftRight := Source.shiftRightInt32
  complement := Source.complementInt32
  neg := Source.negInt32
  abs := Source.absInt32
  decEq := Source.decideInt32Eq
  decLt := Source.decideInt32Lt
  decLe := Source.decideInt32Le

private def int64CaseFamily : SignedFixedWidthCaseFamily Int64 where
  typeName := ``Int64
  typeId := "int64"
  sourceSuffix := "Int64"
  width := 64
  wasmLaneTag := "i64"
  codec := int64CaseCodec
  ofNat := Source.natToInt64
  ofInt := Source.intToInt64
  toInt := Source.int64ToInt
  add := Source.addInt64
  sub := Source.subInt64
  mul := Source.mulInt64
  div := Source.divInt64
  modulo := Source.modInt64
  land := Source.landInt64
  lor := Source.lorInt64
  xor := Source.xorInt64
  shiftLeft := Source.shiftLeftInt64
  shiftRight := Source.shiftRightInt64
  complement := Source.complementInt64
  neg := Source.negInt64
  abs := Source.absInt64
  decEq := Source.decideInt64Eq
  decLt := Source.decideInt64Lt
  decLe := Source.decideInt64Le

private def isizeCaseFamily : SignedFixedWidthCaseFamily ISize where
  typeName := ``ISize
  typeId := "isize"
  sourceSuffix := "ISize"
  width := System.Platform.numBits
  wasmLaneTag := "i64"
  codec := isizeCaseCodec
  ofNat := Source.natToISize
  ofInt := Source.intToISize
  toInt := Source.isizeToInt
  add := Source.addISize
  sub := Source.subISize
  mul := Source.mulISize
  div := Source.divISize
  modulo := Source.modISize
  land := Source.landISize
  lor := Source.lorISize
  xor := Source.xorISize
  shiftLeft := Source.shiftLeftISize
  shiftRight := Source.shiftRightISize
  complement := Source.complementISize
  neg := Source.negISize
  abs := Source.absISize
  decEq := Source.decideISizeEq
  decLt := Source.decideISizeLt
  decLe := Source.decideISizeLe

private def signedCrossConversionCases : Array Case := #[
  exactFixedWidthConversionExternalCase int8CaseCodec int16CaseCodec
    "int8-to-int16-sign-extend" ``Source.int8ToInt16 Source.int8ToInt16
    ``Int8.toInt16 (int8Value (-128))
    #["stress", "scalar", "int8", "int16", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i32"]
    "Sign-extend the Int8 minimum through the lossless Int8-to-Int16 conversion",
  exactFixedWidthConversionExternalCase int16CaseCodec int8CaseCodec
    "int16-to-int8-truncate" ``Source.int16ToInt8 Source.int16ToInt8
    ``Int16.toInt8 (Int16.ofInt (-129))
    #["stress", "scalar", "int8", "int16", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i32"]
    "Truncate Int16 negative 129 to the signed Int8 maximum bit pattern",
  exactFixedWidthConversionExternalCase int8CaseCodec int32CaseCodec
    "int8-to-int32-sign-extend" ``Source.int8ToInt32 Source.int8ToInt32
    ``Int8.toInt32 (int8Value (-128))
    #["stress", "scalar", "int8", "int32", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i32"]
    "Sign-extend the Int8 minimum through the lossless Int8-to-Int32 conversion",
  exactFixedWidthConversionExternalCase int16CaseCodec int32CaseCodec
    "int16-to-int32-sign-extend" ``Source.int16ToInt32 Source.int16ToInt32
    ``Int16.toInt32 (Int16.ofInt (-32768))
    #["stress", "scalar", "int16", "int32", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i32"]
    "Sign-extend the Int16 minimum through the lossless Int16-to-Int32 conversion",
  exactFixedWidthConversionExternalCase int32CaseCodec int8CaseCodec
    "int32-to-int8-truncate" ``Source.int32ToInt8 Source.int32ToInt8
    ``Int32.toInt8 (Int32.ofInt (-129))
    #["stress", "scalar", "int8", "int32", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i32"]
    "Truncate Int32 negative 129 to the signed Int8 maximum bit pattern",
  exactFixedWidthConversionExternalCase int32CaseCodec int16CaseCodec
    "int32-to-int16-truncate" ``Source.int32ToInt16 Source.int32ToInt16
    ``Int32.toInt16 (Int32.ofInt (-32769))
    #["stress", "scalar", "int16", "int32", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i32"]
    "Truncate Int32 negative 32769 to the signed Int16 maximum bit pattern",
  exactFixedWidthConversionExternalCase int8CaseCodec int64CaseCodec
    "int8-to-int64-sign-extend" ``Source.int8ToInt64 Source.int8ToInt64
    ``Int8.toInt64 (int8Value (-128))
    #["stress", "scalar", "int8", "int64", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i64"]
    "Sign-extend the Int8 minimum through the lossless Int8-to-Int64 conversion",
  exactFixedWidthConversionExternalCase int16CaseCodec int64CaseCodec
    "int16-to-int64-sign-extend" ``Source.int16ToInt64 Source.int16ToInt64
    ``Int16.toInt64 (Int16.ofInt (-32768))
    #["stress", "scalar", "int16", "int64", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i64"]
    "Sign-extend the Int16 minimum through the lossless Int16-to-Int64 conversion",
  exactFixedWidthConversionExternalCase int32CaseCodec int64CaseCodec
    "int32-to-int64-sign-extend" ``Source.int32ToInt64 Source.int32ToInt64
    ``Int32.toInt64 (Int32.ofInt (-2147483648))
    #["stress", "scalar", "int32", "int64", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i64"]
    "Sign-extend the Int32 minimum through the lossless Int32-to-Int64 conversion",
  exactFixedWidthConversionExternalCase int64CaseCodec int8CaseCodec
    "int64-to-int8-truncate" ``Source.int64ToInt8 Source.int64ToInt8
    ``Int64.toInt8 (Int64.ofInt (-129))
    #["stress", "scalar", "int8", "int64", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i64"]
    "Truncate Int64 negative 129 to the signed Int8 maximum bit pattern",
  exactFixedWidthConversionExternalCase int64CaseCodec int16CaseCodec
    "int64-to-int16-truncate" ``Source.int64ToInt16 Source.int64ToInt16
    ``Int64.toInt16 (Int64.ofInt (-32769))
    #["stress", "scalar", "int16", "int64", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i64"]
    "Truncate Int64 negative 32769 to the signed Int16 maximum bit pattern",
  exactFixedWidthConversionExternalCase int64CaseCodec int32CaseCodec
    "int64-to-int32-truncate" ``Source.int64ToInt32 Source.int64ToInt32
    ``Int64.toInt32 (Int64.ofInt (-2147483649))
    #["stress", "scalar", "int32", "int64", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i64"]
    "Truncate Int64 negative 2147483649 to the signed Int32 maximum bit pattern",
  exactFixedWidthConversionExternalCase int8CaseCodec isizeCaseCodec
    "int8-to-isize-sign-extend" ``Source.int8ToISize Source.int8ToISize
    ``Int8.toISize (int8Value (-128))
    #["stress", "scalar", "int8", "isize", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i64"]
    "Sign-extend the Int8 minimum through the lossless Int8-to-ISize conversion",
  exactFixedWidthConversionExternalCase int16CaseCodec isizeCaseCodec
    "int16-to-isize-sign-extend" ``Source.int16ToISize Source.int16ToISize
    ``Int16.toISize (Int16.ofInt (-32768))
    #["stress", "scalar", "int16", "isize", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i64"]
    "Sign-extend the Int16 minimum through the lossless Int16-to-ISize conversion",
  exactFixedWidthConversionExternalCase int32CaseCodec isizeCaseCodec
    "int32-to-isize-sign-extend" ``Source.int32ToISize Source.int32ToISize
    ``Int32.toISize (Int32.ofInt (-2147483648))
    #["stress", "scalar", "int32", "isize", "signed", "conversion",
      "sign-extension", "widening", "boundary", "i64"]
    "Sign-extend the Int32 minimum through the lossless Int32-to-ISize conversion",
  exactFixedWidthConversionExternalCase int64CaseCodec isizeCaseCodec
    "int64-to-isize-same-width" ``Source.int64ToISize Source.int64ToISize
    ``Int64.toISize (Int64.ofInt (-9223372036854775808))
    #["stress", "scalar", "int64", "isize", "signed", "conversion",
      "same-width", "bit-pattern", "minimum", "boundary", "i64"]
    "Preserve the signed minimum bit pattern across Int64-to-ISize conversion",
  exactFixedWidthConversionExternalCase isizeCaseCodec int8CaseCodec
    "isize-to-int8-truncate" ``Source.isizeToInt8 Source.isizeToInt8
    ``ISize.toInt8 (ISize.ofInt (-129))
    #["stress", "scalar", "int8", "isize", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i64"]
    "Truncate ISize negative 129 to the signed Int8 maximum bit pattern",
  exactFixedWidthConversionExternalCase isizeCaseCodec int16CaseCodec
    "isize-to-int16-truncate" ``Source.isizeToInt16 Source.isizeToInt16
    ``ISize.toInt16 (ISize.ofInt (-32769))
    #["stress", "scalar", "int16", "isize", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i64"]
    "Truncate ISize negative 32769 to the signed Int16 maximum bit pattern",
  exactFixedWidthConversionExternalCase isizeCaseCodec int32CaseCodec
    "isize-to-int32-truncate" ``Source.isizeToInt32 Source.isizeToInt32
    ``ISize.toInt32 (ISize.ofInt (-2147483649))
    #["stress", "scalar", "int32", "isize", "signed", "conversion",
      "truncation", "narrowing", "underflow", "boundary", "i64"]
    "Truncate ISize negative 2147483649 to the signed Int32 maximum bit pattern",
  exactFixedWidthConversionExternalCase isizeCaseCodec int64CaseCodec
    "isize-to-int64-same-width" ``Source.isizeToInt64 Source.isizeToInt64
    ``ISize.toInt64 (ISize.ofInt (-9223372036854775808))
    #["stress", "scalar", "int64", "isize", "signed", "conversion",
      "same-width", "bit-pattern", "minimum", "boundary", "i64"]
    "Preserve the signed minimum bit pattern across ISize-to-Int64 conversion"
]

private def int16Cases : Array Case :=
  signedFixedWidthCases int16CaseFamily

private def int32Cases : Array Case :=
  signedFixedWidthCases int32CaseFamily

private def int64Cases : Array Case :=
  signedFixedWidthCases int64CaseFamily

private def isizeCases : Array Case :=
  signedFixedWidthCases isizeCaseFamily

private def signedEntryCases : Array Case :=
  signedFixedWidthEntryCases int8CaseCodec "int8" "i32"
      ``Source.capturedInt8Partial Source.capturedInt8Partial Int8.ofInt (-128) 127 #[] ++
    signedFixedWidthEntryCases int16CaseCodec "int16" "i32"
      ``Source.capturedInt16Partial Source.capturedInt16Partial Int16.ofInt (-32768) 32767 #[] ++
    signedFixedWidthEntryCases int32CaseCodec "int32" "i32"
      ``Source.capturedInt32Partial Source.capturedInt32Partial Int32.ofInt
      (-2147483648) 2147483647 #[] ++
    signedFixedWidthEntryCases int64CaseCodec "int64" "i64"
      ``Source.capturedInt64Partial Source.capturedInt64Partial Int64.ofInt
      (-9223372036854775808) 9223372036854775807 #[] ++
    signedFixedWidthEntryCases isizeCaseCodec "isize" "i64"
      ``Source.capturedISizePartial Source.capturedISizePartial ISize.ofInt
      (-9223372036854775808) 9223372036854775807 #["semantic-lean64"]

private def signedResultCases : Array Case :=
  signedFixedWidthResultCases int8CaseCodec "int8" "i32"
      ``Source.resultInt8Minimum ``Source.resultInt8NegativeOne
      ``Source.resultInt8Zero ``Source.resultInt8Maximum
      Int8.ofInt (-128) 127 #[] ++
    signedFixedWidthResultCases int16CaseCodec "int16" "i32"
      ``Source.resultInt16Minimum ``Source.resultInt16NegativeOne
      ``Source.resultInt16Zero ``Source.resultInt16Maximum
      Int16.ofInt (-32768) 32767 #[] ++
    signedFixedWidthResultCases int32CaseCodec "int32" "i32"
      ``Source.resultInt32Minimum ``Source.resultInt32NegativeOne
      ``Source.resultInt32Zero ``Source.resultInt32Maximum
      Int32.ofInt (-2147483648) 2147483647 #[] ++
    signedFixedWidthResultCases int64CaseCodec "int64" "i64"
      ``Source.resultInt64Minimum ``Source.resultInt64NegativeOne
      ``Source.resultInt64Zero ``Source.resultInt64Maximum
      Int64.ofInt (-9223372036854775808) 9223372036854775807 #[] ++
    signedFixedWidthResultCases isizeCaseCodec "isize" "i64"
      ``Source.resultISizeMinimum ``Source.resultISizeNegativeOne
      ``Source.resultISizeZero ``Source.resultISizeMaximum
      ISize.ofInt (-9223372036854775808) 9223372036854775807 #["semantic-lean64"]

def cases : Array Case :=
  preConversionCases ++ signedEntryCases ++ signedResultCases ++
    conversionCases ++ postConversionCases ++
    int8Cases ++ int16Cases ++ int32Cases ++ int64Cases ++ isizeCases ++
      signedCrossConversionCases

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

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "fixed-width-unsigned-external").size == 110

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "usize-external").size == 40

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "fixed-width-unsigned-conversion").size == 55

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "small-word-nat-conversion").size == 15

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "fixed-width-cross-conversion").size == 40

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "fixed-width-signed-external").size == 140

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "fixed-width-signed-conversion").size == 65

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "int8").size == 53

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "int16").size == 53

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "int32").size == 53

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "int64").size == 53

#guard (cases.filter fun validationCase =>
  validationCase.tags.contains "isize").size == 53

#guard System.Platform.numBits == 64

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
