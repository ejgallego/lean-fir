import Fir.Wasm.Concrete.NaturalDispatchCorrectness
import FirTalos.ConcreteResidentMemory
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Factored resident primitive proofs

These short Talos programs are the exact adaptations of the scalar fragments
shared by resident Nat helpers.  Their weakest-precondition lemmas form a
stable semantic vocabulary above Talos's individual instruction equations and
below operation-specific helper proofs.
-/

namespace ResidentPrimitives

def immediateNaturalPairTest (leftIndex rightIndex : Nat) : Wasm.Program := [
  .localGet leftIndex,
  .const 1,
  .and,
  .localGet rightIndex,
  .const 1,
  .and,
  .and]

def immediateNaturalPayload (index : Nat) : Wasm.Program := [
  .localGet index,
  .const 1,
  .shrU]

def immediateNaturalPairDispatch (leftIndex rightIndex : Nat)
    (immediate fallback : Wasm.Program) : Wasm.Program :=
  immediateNaturalPairTest leftIndex rightIndex ++
    [.iff 0 0 immediate fallback]

def immediateNaturalRemainder (leftIndex rightIndex : Nat) : Wasm.Program :=
  immediateNaturalPayload leftIndex ++ immediateNaturalPayload rightIndex ++
    [.remU]

/-- The shared scalar dispatcher leaves the canonical true word on the stack
for a related pair of immediate naturals. -/
theorem wp_immediateNaturalPairTest
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 1 :: tail } env) :
    Wasm.wp module (immediateNaturalPairTest leftIndex rightIndex ++ rest) Q
      store { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)) := by simpa using leftLocal
  have rightLocal' : ({ locals with values :=
      (Wasm.Value.i32 (1 &&& UInt32.ofNat leftWord.value) :: tail) } :
      Wasm.Locals).get rightIndex =
        some (.i32 (UInt32.ofNat rightWord.value)) := by simpa using rightLocal
  simp only [immediateNaturalPairTest, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, leftLocal', Wasm.wp_const_cons, Wasm.wp_and_cons,
    rightLocal']
  have selected :
      (1 &&& UInt32.ofNat rightWord.value) &&&
          (1 &&& UInt32.ofNat leftWord.value) = 1 := by
    have reordered :
        (1 &&& UInt32.ofNat rightWord.value) &&&
            (1 &&& UInt32.ofNat leftWord.value) =
          (UInt32.ofNat leftWord.value &&& 1) &&&
            (UInt32.ofNat rightWord.value &&& 1) := by
      bv_decide
    rw [reordered, pair.wasmPairTest_eq_one]
  simpa [selected] using continuation

/-- The shared logical-shift fragment decodes the left immediate payload. -/
theorem wp_immediateNaturalLeftPayload
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 (UInt32.ofNat leftPayload.toNat) :: tail } env) :
    Wasm.wp module (immediateNaturalPayload leftIndex ++ rest) Q store
      { locals with values := tail } env := by
  have leftLocal' : ({ locals with values := tail } : Wasm.Locals).get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)) := by simpa using leftLocal
  simp only [immediateNaturalPayload, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, leftLocal', Wasm.wp_const_cons, Wasm.wp_shrU_cons]
  simpa [pair.wasmLeftPayload] using continuation

/-- The same shared fragment decodes the right immediate payload. -/
theorem wp_immediateNaturalRightPayload
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values := .i32 (UInt32.ofNat rightPayload.toNat) :: tail } env) :
    Wasm.wp module (immediateNaturalPayload rightIndex ++ rest) Q store
      { locals with values := tail } env := by
  have rightLocal' : ({ locals with values := tail } : Wasm.Locals).get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)) := by simpa using rightLocal
  simp only [immediateNaturalPayload, List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, rightLocal', Wasm.wp_const_cons, Wasm.wp_shrU_cons]
  simpa [pair.wasmRightPayload] using continuation

/-- The nonzero immediate-remainder kernel executes without trapping and
leaves the exact mathematical remainder on the operand stack. -/
theorem wp_immediateNaturalRemainder
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (rightNonzero : rightPayload.toNat ≠ 0)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (continuation : Wasm.wp module rest Q store
      { locals with values :=
          (Wasm.Value.i32
            (UInt32.ofNat (leftPayload.toNat % rightPayload.toNat)) :: tail) } env) :
    Wasm.wp module (immediateNaturalRemainder leftIndex rightIndex ++ rest) Q
      store { locals with values := tail } env := by
  unfold immediateNaturalRemainder
  rw [List.append_assoc]
  apply wp_immediateNaturalLeftPayload pair leftLocal
  apply wp_immediateNaturalRightPayload pair rightLocal
  simp only [List.cons_append, List.nil_append, Wasm.wp_remU_cons]
  have rightLt : rightPayload.toNat < UInt32.size := by
    have rightFits := pair.rightFits
    unfold maxImmediatePayload at rightFits
    simp [UInt32.size]
    omega
  have machineRightNonzero : UInt32.ofNat rightPayload.toNat ≠ 0 := by
    intro zero
    have := congrArg UInt32.toNat zero
    simp at this
    have rightLt' : rightPayload.toNat < 4294967296 := by
      simpa [UInt32.size] using rightLt
    rw [Nat.mod_eq_of_lt rightLt'] at this
    exact rightNonzero this
  rw [if_neg machineRightNonzero]
  rw [pair.wasmRemainder]
  exact continuation

/-- Once the pair test is known true, the generated `if` selects exactly the
immediate body and restores the caller's operand tail at the control boundary.
The proof is independent of the operation performed by that body. -/
theorem wp_immediateNaturalPairDispatch
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {Q : Wasm.Assertion α} {store : Wasm.Store α} {locals : Wasm.Locals}
    {leftIndex rightIndex : Nat} {leftWord rightWord : Word32}
    {leftReference rightReference : Fir.LeanIR.Impure.ObjectRef}
    {leftPayload rightPayload : UInt64} {tail : List Wasm.Value}
    {immediate fallback rest : Wasm.Program}
    (pair : ImmediateNaturalPairRel leftWord rightWord leftReference
      rightReference leftPayload rightPayload)
    (leftLocal : locals.get leftIndex =
      some (.i32 (UInt32.ofNat leftWord.value)))
    (rightLocal : locals.get rightIndex =
      some (.i32 (UInt32.ofNat rightWord.value)))
    (immediateCorrect : Wasm.wp module immediate
      (fun continuation => match continuation with
        | .Fallthrough nextStore nextLocals =>
            Wasm.wp module rest Q nextStore
              { nextLocals with values := tail } env
        | .Break 0 nextStore nextLocals =>
            Wasm.wp module rest Q nextStore
              { nextLocals with values := tail } env
        | .Break (level + 1) nextStore nextLocals =>
            Q (.Break level nextStore nextLocals)
        | other => Q other)
      store { locals with values := tail } env) :
    Wasm.wp module
      (immediateNaturalPairDispatch leftIndex rightIndex immediate fallback ++
        rest) Q store { locals with values := tail } env := by
  unfold immediateNaturalPairDispatch
  rw [List.append_assoc]
  apply wp_immediateNaturalPairTest pair leftLocal rightLocal
  apply Wasm.wp_iff_cons rfl
  convert immediateCorrect using 1
  · simp
  · funext continuation
    cases continuation <;> rfl

end ResidentPrimitives

end FirTalos.Concrete
