import Fir.Wasm.WellFormed

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm

private theorem exceptArrayForM_ok_of_mem
    {α ε : Type} {f : α → Except ε Unit} {xs : Array α} {x : α}
    (run : xs.forM f = .ok ()) (member : x ∈ xs) :
    f x = .ok () := by
  have listRun :
      xs.toList.foldlM (fun _ item => f item) () = .ok () := by
    simpa [Array.forM] using run
  have listMember : x ∈ xs.toList := by simpa using member
  have go : ∀ (list : List α),
      list.foldlM (fun _ item => f item) () = .ok () →
        x ∈ list → f x = .ok () := by
    intro list
    induction list with
    | nil => simp
    | cons head tail ih =>
        intro tailRun itemMember
        simp only [List.mem_cons] at itemMember
        simp only [List.foldlM_cons] at tailRun
        cases headRun : f head with
        | error error =>
            simp only [headRun, Bind.bind, Except.bind] at tailRun
            contradiction
        | ok value =>
            have unitEq : value = () := Subsingleton.elim _ _
            subst value
            simp only [headRun, Bind.bind, Except.bind] at tailRun
            rcases itemMember with rfl | itemMember
            · exact headRun
            · exact ih tailRun itemMember
  exact go xs.toList listRun listMember

private theorem supportedChecks_of_validateSupportedDecl
    {program : Fir.LeanIR.ImpureProgram} {decl : LCNF.Decl .impure}
    (validated : validateSupportedDecl program decl = .ok ()) :
    supportedDecl program decl = true ∧
      (match decl.value with
        | .code code => reuseCapacitySafeCode [] code
        | .extern _ => true) = true := by
  cases bodyEq : decl.value with
  | extern metadata =>
      by_cases supported : supportedDecl program decl = true
      · exact ⟨supported, rfl⟩
      · simp [validateSupportedDecl, bodyEq, supported] at validated
  | code code =>
      by_cases supported : supportedDecl program decl = true
      · by_cases safe : reuseCapacitySafeCode [] code = true
        · exact ⟨supported, safe⟩
        · simp [validateSupportedDecl, bodyEq, supported, safe] at validated
      · simp [validateSupportedDecl, bodyEq, supported] at validated

/-- Successful supported lowering necessarily completed the executable source
validation. This exposes the existing compiler check, not a new validator. -/
theorem validateSupported_of_lowerSupported
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    (lowered : lowerSupported program = .ok source) :
    validateSupported program = .ok () := by
  unfold lowerSupported at lowered
  cases validationEq : validateSupported program with
  | error error =>
      simp only [validationEq, Bind.bind, Except.bind] at lowered
      contradiction
  | ok value =>
      cases value
      rfl

/-- The two whole-program checks actually performed by `validateSupported`:
every declaration is supported, and every code body has checked reuse
capacity. Closure-flow safety and top-level name uniqueness are not asserted. -/
theorem validateSupported_facts
    {program : Fir.LeanIR.ImpureProgram}
    (validated : validateSupported program = .ok ()) :
    program.decls.all (supportedDecl program) = true ∧
      reuseCapacitySafeProgram program = true := by
  have checked : ∀ decl ∈ program.decls,
      validateSupportedDecl program decl = .ok () := by
    intro decl member
    exact exceptArrayForM_ok_of_mem validated member
  constructor
  · apply Array.all_eq_true'.mpr
    intro decl member
    exact (supportedChecks_of_validateSupportedDecl (checked decl member)).1
  · unfold reuseCapacitySafeProgram
    apply Array.all_eq_true'.mpr
    intro decl member
    exact (supportedChecks_of_validateSupportedDecl (checked decl member)).2

/-- After executable source validation, `WasmSupported` has exactly one
remaining Boolean obligation: closure-flow safety. In particular validation
success alone is not promoted to the stronger supported-program predicate. -/
theorem wasmSupported_iff_closureFlowSafe_of_validateSupported
    {program : Fir.LeanIR.ImpureProgram}
    (validated : validateSupported program = .ok ()) :
    WasmSupported program ↔ closureFlowSafeProgram program = true := by
  obtain ⟨declarations, reuse⟩ := validateSupported_facts validated
  simp [WasmSupported, supportedProgram, declarations, reuse]

/-- The exact residual source check at a successful production lowering
boundary. This theorem supplies no dynamic admission, execution, resource,
entry-frame or capture-correspondence evidence. -/
theorem wasmSupported_iff_closureFlowSafe_of_lowerSupported
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    (lowered : lowerSupported program = .ok source) :
    WasmSupported program ↔ closureFlowSafeProgram program = true :=
  wasmSupported_iff_closureFlowSafe_of_validateSupported
    (validateSupported_of_lowerSupported lowered)

end FirTalos.Concrete
