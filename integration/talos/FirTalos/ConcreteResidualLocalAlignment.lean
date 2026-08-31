import FirTalos.ConcreteReuseCapacityCacheCorrectness

/-!
# Compiler-derived residual local alignment

Production lowering computes one exact list of effective local-kind updates
for a complete final-LCNF function.  Current-node admission needs only the
suffix of that list belonging to the currently executing residual code.  This
module packages that compiler calculation as a small structural view: it is
not a source invariant and contains no semantic execution evidence.

The view deliberately follows `collectEffectiveLocalKindUpdates`, so its
projection rules can be reused by every `let` family rather than being
reproved separately for direct calls, lazy caches, and primitives.
-/

namespace FirTalos.Concrete

open Fir.Wasm

/-- The exact production local lookup for every effective update collected
from one residual code node.  The update list is compiler-computed rather than
chosen by a theorem client. -/
inductive ConcreteResidualLocalAlignment
    (context : Fir.Wasm.Context)
    (program : Fir.LeanIR.ImpureProgram)
    (code : Lean.Compiler.LCNF.Code .impure) : Prop where
  | intro
      (updates : List (Lean.FVarId × Fir.Wasm.AbiKind))
      (collected :
        Fir.Wasm.collectEffectiveLocalKindUpdates program code = .ok updates)
      (getLocal_of_mem :
        ∀ {fvarId : Lean.FVarId} {kind : Fir.Wasm.AbiKind},
          (fvarId, kind) ∈ updates →
            Fir.Wasm.getLocal context fvarId =
              .ok (.localGet fvarId, kind))

/-- The head destination of a residual `let` has exactly the effective kind
selected by production lowering. -/
theorem ConcreteResidualLocalAlignment.letHead
    {context : Fir.Wasm.Context}
    {program : Fir.LeanIR.ImpureProgram}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {kind : Fir.Wasm.AbiKind}
    (aligned : ConcreteResidualLocalAlignment context program
      (.let decl continuation))
    (effective : Fir.Wasm.effectiveLetValueKind program decl = .ok kind) :
    Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, kind) := by
  rcases aligned with ⟨updates, collected, getLocal_of_mem⟩
  cases restCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program continuation with
  | error fault =>
      simp [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
        restCollected, Bind.bind, Except.bind] at collected
  | ok rest =>
      have updatesEq :
          (decl.fvarId, kind) :: rest = updates := by
        simpa [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
          restCollected, Bind.bind, Except.bind, pure, Except.pure] using
          collected
      apply getLocal_of_mem
      rw [← updatesEq]
      simp

/-- Removing a residual `let` exposes the exact compiler alignment for its
continuation.  This is the structural preservation rule used by all let-step
simulation families. -/
theorem ConcreteResidualLocalAlignment.letContinuation
    {context : Fir.Wasm.Context}
    {program : Fir.LeanIR.ImpureProgram}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {kind : Fir.Wasm.AbiKind}
    (aligned : ConcreteResidualLocalAlignment context program
      (.let decl continuation))
    (effective : Fir.Wasm.effectiveLetValueKind program decl = .ok kind) :
    ConcreteResidualLocalAlignment context program continuation := by
  rcases aligned with ⟨updates, collected, getLocal_of_mem⟩
  cases restCollected :
      Fir.Wasm.collectEffectiveLocalKindUpdates program continuation with
  | error fault =>
      simp [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
        restCollected, Bind.bind, Except.bind] at collected
  | ok rest =>
      have updatesEq :
          (decl.fvarId, kind) :: rest = updates := by
        simpa [Fir.Wasm.collectEffectiveLocalKindUpdates, effective,
          restCollected, Bind.bind, Except.bind, pure, Except.pure] using
          collected
      refine ⟨rest, restCollected, ?_⟩
      intro fvarId resultKind member
      apply getLocal_of_mem
      rw [← updatesEq]
      simp [member]

end FirTalos.Concrete
