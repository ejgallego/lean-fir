import Fir.Wasm.Concrete.Layout

namespace Fir.Wasm.Concrete

/-!
# Resident runtime representation markers

This module is the proof-free representation contract shared by the concrete
runtime and the Wasm resident-helper emitter.  Keep executable generation on
this lightweight boundary rather than importing the concrete memory model and
its refinement proofs.
-/

/-- First address available to resident Lean heap objects. Lower words are
reserved for runtime bookkeeping and scratch storage. -/
def heapBase : Nat := 1024

def promotedTagMarker : UInt32 := 1

def bigNaturalMarker : UInt32 := 2

/-- Experimental version marker for the current arbitrary-precision heap-Int
layout. Clients may rely on the checked API, not on long-term layout stability. -/
def integerSignMagnitudeMarker : UInt32 := 1

/-- Version marker for the W6 string payload. Strings store their canonical
UTF-8 bytes contiguously after the common header; `aux1` records the exact byte
count and `aux2`/`aux3` remain reserved. -/
def stringUtf8Marker : UInt32 := 1

/-- Canonical little-endian base-`2^64` limbs used by resident natural
payloads. This decomposition is shared by concrete allocation proofs and by
compile-time literal emission. -/
def naturalLimbs (value : Nat) : List UInt64 :=
  if _h : value < UInt64.size then
    [UInt64.ofNat value]
  else
    UInt64.ofNat (value % UInt64.size) :: naturalLimbs (value / UInt64.size)
termination_by value
decreasing_by
  apply Nat.div_lt_self
  · have sizePositive : 0 < UInt64.size := by decide
    omega
  · decide

end Fir.Wasm.Concrete
