import Fir.LeanIR.Passes.AlphaEqvTrusted

namespace Fir.LeanIR.Passes.SimpCaseCorrectness

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.AlphaEqv
open Fir.LeanIR.Passes.SimpCase

/-- The default-folding rewrite is observationally correct when both branch
orientations are accepted by FIR's transparent alpha checker. -/
theorem fold_to_default_correct_of_local_alpha
    {state : MachineState} {before after : LCNF.Cases .impure}
    {discr : Value} {tag : Nat}
    {beforeBranch representative : LCNF.Code .impure}
    {externals : ExternalSpec} {observation : Observation}
    (lookupBefore : lookupValue state.env before.discr = .ok discr)
    (lookupAfter : lookupValue state.env after.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (selectedBefore : chooseAlt tag before.alts.toList = some beforeBranch)
    (selectedAfter : chooseAlt tag after.alts.toList = some representative)
    (forwardSide : CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) scope scope beforeBranch representative)
    (backwardSide : CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) scope scope representative beforeBranch)
    (forwardAccepted : Local.Accepts beforeBranch representative)
    (backwardAccepted : Local.Accepts representative beforeBranch)
    (covers : EnvCovers scope state.env)
    (frames : FramesRelated state.frames state.frames)
    (bodies : ProgramBodiesRelated state.program) :
    EvaluatesState externals
        { state with control := .code (.cases before) } observation ↔
      EvaluatesState externals
        { state with control := .code (.cases after) } observation := by
  apply case_rewrite_correct_of_selected_equivalent lookupBefore lookupAfter
    readTag selectedBefore selectedAfter
  exact codeEquivalentAt_of_local_accepts_both
    forwardSide backwardSide forwardAccepted backwardAccepted
    covers frames bodies

/-- Compiler-facing default folding. Both Boolean orientations are explicit;
their conversion reuses the sole audited Lean-4.32 correspondence axiom. -/
theorem fold_to_default_correct_of_upstream_alpha
    {state : MachineState} {before after : LCNF.Cases .impure}
    {discr : Value} {tag : Nat}
    {beforeBranch representative : LCNF.Code .impure}
    {externals : ExternalSpec} {observation : Observation}
    (lookupBefore : lookupValue state.env before.discr = .ok discr)
    (lookupAfter : lookupValue state.env after.discr = .ok discr)
    (readTag : getTag state.runtime discr = .ok tag)
    (selectedBefore : chooseAlt tag before.alts.toList = some beforeBranch)
    (selectedAfter : chooseAlt tag after.alts.toList = some representative)
    (forwardSide : CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) scope scope beforeBranch representative)
    (backwardSide : CodeSideConditions (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) scope scope representative beforeBranch)
    (forwardAccepted : beforeBranch.alphaEqv representative = true)
    (backwardAccepted : representative.alphaEqv beforeBranch = true)
    (covers : EnvCovers scope state.env)
    (frames : FramesRelated state.frames state.frames)
    (bodies : ProgramBodiesRelated state.program) :
    EvaluatesState externals
        { state with control := .code (.cases before) } observation ↔
      EvaluatesState externals
        { state with control := .code (.cases after) } observation := by
  apply fold_to_default_correct_of_alpha_sound lookupBefore lookupAfter readTag
    selectedBefore selectedAfter forwardAccepted
  intro accepted
  exact trustedCodeEquivalentAt_of_upstream_both
    forwardSide backwardSide accepted backwardAccepted covers frames bodies

end Fir.LeanIR.Passes.SimpCaseCorrectness
