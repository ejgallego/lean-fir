import Lean.Compiler.LCNF.AlphaEqv

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler

namespace Local

abbrev EqvM := LCNF.AlphaEqv.EqvM

/--
Run the alternative checker using a supplied recursive code checker. This is
the transparent counterpart of the loop inside Lean 4.32's opaque
`LCNF.AlphaEqv.eqvAlts`.
-/
private def eqvAltsUsing
    (recurse : LCNF.Code pu → LCNF.Code pu → EqvM Bool)
    (alts₁ alts₂ : Array (LCNF.Alt pu)) : EqvM Bool := do
  if alts₁.size = alts₂.size then
    let alts₁ := LCNF.AlphaEqv.sortAlts alts₁
    let alts₂ := LCNF.AlphaEqv.sortAlts alts₂
    for alt₁ in alts₁, alt₂ in alts₂ do
      match alt₁, alt₂ with
      | .alt ctorName₁ ps₁ k₁ _, .alt ctorName₂ ps₂ k₂ _ =>
          unless ctorName₁ == ctorName₂ do return false
          unless (← LCNF.AlphaEqv.withParams ps₁ ps₂ (recurse k₁ k₂)) do
            return false
      | .ctorAlt i₁ k₁ _, .ctorAlt i₂ k₂ _ =>
          unless i₁ == i₂ do return false
          unless ← recurse k₁ k₂ do return false
      | .default k₁, .default k₂ =>
          unless (← recurse k₁ k₂) do return false
      | _, _ => return false
    return true
  else
    return false

/--
A total, transparent copy of Lean 4.32's recursive LCNF alpha-equivalence
checker. Fuel is consumed only when descending through code or an alternative
table; exhaustion rejects instead of introducing another opaque `partial def`.
-/
def eqv : Nat → LCNF.Code pu → LCNF.Code pu → EqvM Bool
  | 0, _, _ => pure false
  | fuel + 1, code₁, code₂ => do
      match code₁, code₂ with
      | .let decl₁ k₁, .let decl₂ k₂ =>
          LCNF.AlphaEqv.eqvType decl₁.type decl₂.type <&&>
          LCNF.AlphaEqv.eqvLetValue decl₁.value decl₂.value <&&>
          LCNF.AlphaEqv.withFVar decl₁.fvarId decl₂.fvarId (eqv fuel k₁ k₂)
      | .fun decl₁ k₁ _, .fun decl₂ k₂ _
      | .jp decl₁ k₁, .jp decl₂ k₂ =>
          LCNF.AlphaEqv.eqvType decl₁.type decl₂.type <&&>
          LCNF.AlphaEqv.withParams decl₁.params decl₂.params
            (eqv fuel decl₁.value decl₂.value) <&&>
          LCNF.AlphaEqv.withFVar decl₁.fvarId decl₂.fvarId (eqv fuel k₁ k₂)
      | .return fvarId₁, .return fvarId₂ =>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂
      | .unreach type₁, .unreach type₂ =>
          LCNF.AlphaEqv.eqvType type₁ type₂
      | .jmp fvarId₁ args₁, .jmp fvarId₂ args₂ =>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          LCNF.AlphaEqv.eqvArgs args₁ args₂
      | .cases c₁, .cases c₂ =>
          LCNF.AlphaEqv.eqvFVar c₁.discr c₂.discr <&&>
          LCNF.AlphaEqv.eqvType c₁.resultType c₂.resultType <&&>
          eqvAltsUsing (eqv fuel) c₁.alts c₂.alts
      | .oset fvarId₁ i₁ y₁ k₁ _, .oset fvarId₂ i₂ y₂ k₂ _ =>
          pure (i₁ == i₂) <&&>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          LCNF.AlphaEqv.eqvArg y₁ y₂ <&&>
          eqv fuel k₁ k₂
      | .sset fvarId₁ i₁ offset₁ y₁ ty₁ k₁ _,
          .sset fvarId₂ i₂ offset₂ y₂ ty₂ k₂ _ =>
          pure (i₁ == i₂) <&&>
          pure (offset₁ == offset₂) <&&>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          LCNF.AlphaEqv.eqvFVar y₁ y₂ <&&>
          LCNF.AlphaEqv.eqvType ty₁ ty₂ <&&>
          eqv fuel k₁ k₂
      | .uset fvarId₁ i₁ y₁ k₁ _, .uset fvarId₂ i₂ y₂ k₂ _ =>
          pure (i₁ == i₂) <&&>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          LCNF.AlphaEqv.eqvFVar y₁ y₂ <&&>
          eqv fuel k₁ k₂
      | .setTag fvarId₁ c₁ k₁ _, .setTag fvarId₂ c₂ k₂ _ =>
          pure (c₁ == c₂) <&&>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          eqv fuel k₁ k₂
      | .inc fvarId₁ n₁ c₁ p₁ k₁ _, .inc fvarId₂ n₂ c₂ p₂ k₂ _ =>
          pure (n₁ == n₂) <&&>
          pure (c₁ == c₂) <&&>
          pure (p₁ == p₂) <&&>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          eqv fuel k₁ k₂
      | .dec fvarId₁ n₁ c₁ p₁ o₁ k₁ _, .dec fvarId₂ n₂ c₂ p₂ o₂ k₂ _ =>
          pure (n₁ == n₂) <&&>
          pure (c₁ == c₂) <&&>
          pure (p₁ == p₂) <&&>
          pure (o₁ == o₂) <&&>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          eqv fuel k₁ k₂
      | .del fvarId₁ k₁ _, .del fvarId₂ k₂ _ =>
          LCNF.AlphaEqv.eqvFVar fvarId₁ fvarId₂ <&&>
          eqv fuel k₁ k₂
      | _, _ => return false

/-- Executable local check at an explicit reader map and fuel bound. -/
def checkAt (fuel : Nat) (rho : FVarIdMap FVarId)
    (left right : LCNF.Code pu) : Bool :=
  (eqv fuel left right).run rho

/-- Executable top-level local check with the same empty initial map as Lean. -/
def check (fuel : Nat) (left right : LCNF.Code pu) : Bool :=
  checkAt fuel {} left right

/-- Fuel-independent acceptance by the total local checker. -/
def AcceptsAt (rho : FVarIdMap FVarId)
    (left right : LCNF.Code pu) : Prop :=
  ∃ fuel, checkAt fuel rho left right = true

/-- Top-level local acceptance from an empty renaming map. -/
def Accepts (left right : LCNF.Code pu) : Prop :=
  AcceptsAt {} left right

end Local

/--
The only correspondence needed from Lean's opaque checker: every successful
upstream top-level check has a finite accepting run in the transparent copy.
-/
structure UpstreamBridge : Prop where
  accepted : ∀ {pu : LCNF.Purity} (left right : LCNF.Code pu),
    left.alphaEqv right = true → Local.Accepts left right

end Fir.LeanIR.Passes.AlphaEqv
