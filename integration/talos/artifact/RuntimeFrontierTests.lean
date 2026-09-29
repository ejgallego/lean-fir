import Fir.Wasm.Emit.ResidentFixedWidth
import Fir.Wasm.Emit.ResidentLiteral
import Fir.Wasm.Emit.ResidentNatArithmetic
import Lean.Elab.Command
import Lean.Compiler.LCNF.PhaseExt

open Lean Lean.Elab.Command Lean.Compiler.LCNF Fir.Wasm Fir.Wasm.Emit

/- Check the installed compiler's interface, not a hand-written import alone.
This file runs under both FIR's production toolchain and the isolated renderer
toolchain. Neither path consumes the other's compiled modules. -/
run_cmd do
  liftCoreM do
    let env ← getEnv
    let some sig ← getImpureSignature? ``UInt64.ofNatLT |
      throwError "missing installed UInt64.ofNatLT signature"
    unless getExternNameFor env `c sig.name == some "lean_uint64_of_nat" do
      throwError "UInt64.ofNatLT upstream symbol changed"
    unless sig.safe && sig.levelParams.isEmpty &&
        sig.type == ImpureType.uint64 &&
        sig.params.map (·.type) == #[ImpureType.tobject, ImpureType.erased] &&
        sig.params.map (·.borrow) == #[true, false] do
      throwError "UInt64.ofNatLT installed representation or borrowing changed"
    unless ResidentFixedWidth.uint64OfNatLTFunction.params.map (·.2) == #[.tobject, .erased] &&
        ResidentFixedWidth.uint64OfNatLTFunction.results == #[.uint64] &&
        ResidentFixedWidth.uint64OfNatLTFunction.body == ResidentFixedWidth.uint64OfNatFunction.body do
      throwError "UInt64.ofNatLT adapter no longer preserves the conversion body"

#guard UInt64.ofNatLT 0 (by decide) == 0
#guard UInt64.ofNatLT 9223372036854775808 (by decide) == 9223372036854775808
#guard UInt64.ofNatLT 18446744073709551615 (by decide) == 18446744073709551615
#guard Fir.Wasm.Concrete.naturalLimbs (2^64) == [0, 1]
#guard Fir.Wasm.Concrete.naturalLimbs (2^193 + 2^129 + 0x0123456789abcdef) ==
  [0x0123456789abcdef, 0, 2, 2]

/- The Collatz `n % 2` ownership boundary, before resident literal installation:
   literal divisor; Nat.mod; borrowed Nat.decEq; checked decrement.
   Use the production rewrite registry, not a test-only range rule. The input
   stays tobject: a heap-valued dividend must still use generic Nat arithmetic.
   ResidentLinker performs this refinement before release specialization. -/
namespace CollatzRemainderRelease

private def input : FVarId := ⟨`input⟩
private def unknownDivisor : FVarId := ⟨`unknownDivisor⟩
private def divisor : FVarId := ⟨`divisor⟩
private def remainder : FVarId := ⟨`remainder⟩
private def zero : FVarId := ⟨`zero⟩
private def even : FVarId := ⟨`even⟩

private def caller (literal? : Option Nat) : Function := {
  name := `collatzRemainderRelease
  params := #[(input, .tobject), (unknownDivisor, .tobject)]
  results := #[.uint8]
  locals := #[(zero, .tobject), (divisor, .tobject),
    (remainder, .tobject), (even, .uint8)]
  body := [
    .call (.runtime (.literal (.nat 0) .tobject)), .localSet zero] ++
    (match literal? with
    | some value => [
        .call (.runtime (.literal (.nat value) .tobject)), .localSet divisor]
    | none => [.localGet unknownDivisor, .localSet divisor]) ++ [
    .localGet input, .localGet divisor, .call (.declaration `Nat.mod),
    .localSet remainder,
    .localGet remainder, .localGet zero, .call (.declaration `Nat.decEq),
    .localSet even,
    .localGet remainder, .call (.runtime (.dec 1 true none)),
    .localGet even, .ret] }

private def refined (literal? : Option Nat) : Function :=
  ResidentCallSite.refineFunctionLocals ResidentNatArithmetic.callSiteRewrites
    (caller literal?)

private def specialized (literal? : Option Nat) : Function :=
  ResidentRelease.specializeCheckedDecrementFunction (refined literal?)

-- The fact is available before either the Nat.mod call or literal is lowered.
#guard ResidentRelease.specializeCheckedDecrementFunction (caller (some 2)) ==
  caller (some 2)
#guard (refined (some 2)).locals ==
  #[(zero, .tobject), (divisor, .tobject), (remainder, .tagged), (even, .uint8)]
#guard (refined (some 2)).params == (caller (some 2)).params
#guard (refined (some 2)).body == (caller (some 2)).body

-- Remove exactly the release operand/call, keeping the borrowed comparison.
#guard (specialized (some 2)).body == [
  .call (.runtime (.literal (.nat 0) .tobject)), .localSet zero,
  .call (.runtime (.literal (.nat 2) .tobject)), .localSet divisor,
  .localGet input, .localGet divisor, .call (.declaration `Nat.mod),
  .localSet remainder,
  .localGet remainder, .localGet zero, .call (.declaration `Nat.decEq),
  .localSet even, .localGet even, .ret]

-- Zero, a heap-sized divisor, and an unknown divisor do not justify erasure.
-- Both fallback cases can return a heap Nat, unlike a large dividend modulo 2.
#guard ([some 0, some (2^64), none] : List (Option Nat)).all fun literal? =>
  refined literal? == caller literal? && specialized literal? == caller literal?
#guard (2^130 + 17) % 2 == 1
#guard (2^130 + 17) % 0 > Fir.Wasm.Concrete.maxImmediatePayload
#guard (2^130 + 2^63) % (2^64) > Fir.Wasm.Concrete.maxImmediatePayload

-- The module frontier must retain the generic release for fallback callers.
private def frontier (literal? : Option Nat) : Fir.Wasm.Module :=
  ResidentRelease.specializeCheckedDecrements {
    imports := #[], exports := #[], initializers := #[], runtimeOperations := #[]
    functions := #[refined literal?] }

#guard !(frontier (some 2)).runtimeOperations.contains (.dec 1 true none)
#guard ([some 0, some (2^64), none] : List (Option Nat)).all fun literal? =>
  let module := frontier literal?
  module.runtimeOperations.contains (.dec 1 true none) &&
    module.imports.any (·.operation? == some (.dec 1 true none))

end CollatzRemainderRelease
