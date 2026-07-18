import Fir.Wasm.Concrete.Refinement

namespace Fir.Wasm.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure

#guard target.name == "wasm32-lean64"
#guard target.pointerLane == .i32
#guard target.usizeLane == .i64
#guard target.semanticSlotBytes == 8

#guard (Word32.encodeImmediate? 0).map (·.value) == some 1
#guard (Word32.encodeImmediate? maxImmediatePayload).map (·.value) ==
  some 4294967295
#guard (Word32.encodeImmediate? (maxImmediatePayload + 1)).isNone

def mixedConstructorInfo : LCNF.CtorInfo := {
  name := `Concrete.mixed
  cidx := 3
  size := 1
  usize := 1
  ssize := 8 }

def mixedConstructorLayout : ConstructorLayout :=
  ConstructorLayout.ofInfo mixedConstructorInfo

#guard mixedConstructorLayout.objectFieldsOffset == 32
#guard mixedConstructorLayout.usizeFieldsOffset == 40
#guard mixedConstructorLayout.scalarFieldsOffset == 48
#guard mixedConstructorLayout.allocationBytes == 56
#guard mixedConstructorLayout.objectFieldOffset? 0 == some 32
#guard mixedConstructorLayout.objectFieldOffset? 1 == none
#guard mixedConstructorLayout.usizeFieldOffset? 0 == some 40
#guard mixedConstructorLayout.scalarFieldOffset? 2 0 .uint64 == some 48
#guard mixedConstructorLayout.scalarFieldOffset? 2 1 .uint64 == none
#guard mixedConstructorLayout.scalarFieldOffset? 1 0 .uint64 == none

def mixedClosureLayout : ClosureLayout :=
  ClosureLayout.ofCaptures #[.object, .uint64, .uint8]

#guard mixedClosureLayout.captureOffset? 0 == some 32
#guard mixedClosureLayout.captureOffset? 1 == some 40
#guard mixedClosureLayout.captureOffset? 2 == some 48
#guard mixedClosureLayout.captureOffset? 3 == none
#guard mixedClosureLayout.allocationBytes == 56

example : ValueRel (witness := {}) .tobject
    (.word32 (Word32.encodeImmediate 42 (by decide)))
    (.object (.tagged 42)) :=
  .tobject (.tagged (.immediate 42 (by decide)))

example : ValueRel (witness := {}) .usize
    (.word64 (18446744073709551615 : UInt64))
    (.usize (18446744073709551615 : UInt64)) := .usize

end Fir.Wasm.Concrete
