import Lean.Compiler.LCNF.Basic

namespace Fir.LeanIR

namespace LCNFCore

open Lean
open Lean.Compiler

/-- Values modeled by the v1 FIR subset. -/
inductive Value where
  | lit (value : LCNF.LitValue)
  | erased
  deriving Inhabited, BEq

/-- A variable environment for the executable semantics. -/
abbrev Env := List (FVarId × Value)

/-- Add or shadow a variable binding. -/
def bind (env : Env) (x : FVarId) (value : Value) : Env :=
  (x, value) :: env

/-- Lookup the most recent binding for a variable. -/
def lookup : Env → FVarId → Option Value
  | [], _ => none
  | (y, value) :: env, x =>
      if y.name = x.name then
        some value
      else
        lookup env x

@[simp] theorem lookup_bind_self (env : Env) (x : FVarId) (value : Value) :
    lookup (bind env x value) x = some value := by
  cases x
  simp [bind, lookup]

/-- Errors reported by the executable semantics. -/
inductive EvalError where
  | unknownVar (x : FVarId)
  | unreachable
  | unsupported
  deriving Inhabited, BEq

/-- The supported v1 fragment of LCNF let-values. -/
inductive SupportedLetValue : LCNF.LetValue .impure → Prop where
  | lit (value : LCNF.LitValue) :
      SupportedLetValue (.lit value)
  | erased :
      SupportedLetValue .erased

/-- The supported v1 fragment of impure LCNF code. -/
inductive SupportedCode : LCNF.Code .impure → Prop where
  | letDecl {decl : LCNF.LetDecl .impure} {k : LCNF.Code .impure}
      (hval : SupportedLetValue decl.value) (hk : SupportedCode k) :
      SupportedCode (.let decl k)
  | inc {fvarId : FVarId} {n : Nat} {check persistent : Bool} {k : LCNF.Code .impure}
      (hk : SupportedCode k) :
      SupportedCode (.inc fvarId n check persistent k)
  | ret (x : FVarId) :
      SupportedCode (.return x)
  | unreach (type : Expr) :
      SupportedCode (.unreach type)

/-- Executable check for the supported v1 let-value fragment. -/
def supportedLetValue? : LCNF.LetValue .impure → Bool
  | .lit _ => true
  | .erased => true
  | _ => false

/-- Executable check for the supported v1 code fragment. -/
def supportedCode? : LCNF.Code .impure → Bool
  | .let decl k => supportedLetValue? decl.value && supportedCode? k
  | .inc _ _ _ _ k _ => supportedCode? k
  | .return _ => true
  | .unreach _ => true
  | _ => false

theorem supportedLetValue?_sound {value : LCNF.LetValue .impure} :
    supportedLetValue? value = true → SupportedLetValue value := by
  cases value <;> simp [supportedLetValue?]
  · exact SupportedLetValue.lit _
  · exact SupportedLetValue.erased

theorem supportedLetValue?_complete {value : LCNF.LetValue .impure} :
    SupportedLetValue value → supportedLetValue? value = true := by
  intro h
  cases h <;> rfl

def supportedCode?_sound :
    (code : LCNF.Code .impure) → supportedCode? code = true → SupportedCode code
  | .let decl k, h => by
      simp [supportedCode?] at h
      exact .letDecl (supportedLetValue?_sound h.1) (supportedCode?_sound k h.2)
  | .return x, _ => .ret x
  | .unreach type, _ => .unreach type
  | .fun decl k hpurity, h => by
      simp [supportedCode?] at h
  | .jp decl k, h => by
      simp [supportedCode?] at h
  | .jmp fvarId args, h => by
      simp [supportedCode?] at h
  | .cases cases, h => by
      simp [supportedCode?] at h
  | .oset fvarId i y k hpurity, h => by
      simp [supportedCode?] at h
  | .uset fvarId i y k hpurity, h => by
      simp [supportedCode?] at h
  | .sset fvarId i offset y ty k hpurity, h => by
      simp [supportedCode?] at h
  | .setTag fvarId cidx k hpurity, h => by
      simp [supportedCode?] at h
  | .inc fvarId n check persistent k hpurity, h => by
      simp [supportedCode?] at h
      exact .inc (supportedCode?_sound k h)
  | .dec fvarId n check persistent objs? k hpurity, h => by
      simp [supportedCode?] at h
  | .del fvarId k hpurity, h => by
      simp [supportedCode?] at h

theorem supportedCode?_complete {code : LCNF.Code .impure} :
    SupportedCode code → supportedCode? code = true := by
  intro h
  induction h with
  | letDecl hval hk ih =>
      simp [supportedCode?, supportedLetValue?_complete hval, ih]
  | inc hk ih =>
      simp [supportedCode?, ih]
  | ret x =>
      rfl
  | unreach type =>
      rfl

theorem supportedLetValue?_eq_true {value : LCNF.LetValue .impure} :
    supportedLetValue? value = true ↔ SupportedLetValue value :=
  ⟨supportedLetValue?_sound, supportedLetValue?_complete⟩

theorem supportedCode?_eq_true {code : LCNF.Code .impure} :
    supportedCode? code = true ↔ SupportedCode code :=
  ⟨supportedCode?_sound code, supportedCode?_complete⟩

def evalLetValue : LCNF.LetValue .impure → Except EvalError Value
  | .lit value => .ok (.lit value)
  | .erased => .ok .erased
  | _ => .error .unsupported

def eval (env : Env) : LCNF.Code .impure → Except EvalError Value
  | .let decl k => do
      let value ← evalLetValue decl.value
      eval (bind env decl.fvarId value) k
  | .inc _ _ _ _ k _ => eval env k
  | .return x =>
      match lookup env x with
      | some value => .ok value
      | none => .error (.unknownVar x)
  | .unreach _ => .error .unreachable
  | _ => .error .unsupported

/-- Big-step semantics for supported let-values. -/
inductive EvalLetValue : LCNF.LetValue .impure → Value → Prop where
  | lit {value : LCNF.LitValue} :
      EvalLetValue (.lit value) (.lit value)
  | erased :
      EvalLetValue .erased .erased

/-- Big-step semantics for the v1 FIR subset of impure LCNF. -/
inductive Eval : Env → LCNF.Code .impure → Value → Prop where
  | letDecl {env : Env} {decl : LCNF.LetDecl .impure} {k : LCNF.Code .impure} {value result : Value}
      (hval : EvalLetValue decl.value value)
      (hk : Eval (bind env decl.fvarId value) k result) :
      Eval env (.let decl k) result
  | inc {env : Env} {fvarId : FVarId} {n : Nat} {check persistent : Bool}
      {k : LCNF.Code .impure} {result : Value}
      (hk : Eval env k result) :
      Eval env (.inc fvarId n check persistent k) result
  | ret {env : Env} {x : FVarId} {value : Value}
      (hlookup : lookup env x = some value) :
      Eval env (.return x) value

theorem evalLetValue_sound {val : LCNF.LetValue .impure} {result : Value} :
    SupportedLetValue val → evalLetValue val = .ok result → EvalLetValue val result := by
  intro hsup h
  cases hsup <;> simp [evalLetValue] at h
  · cases h
    constructor
  · cases h
    constructor

theorem evalLetValue_complete {val : LCNF.LetValue .impure} {result : Value} :
    EvalLetValue val result → evalLetValue val = .ok result := by
  intro h
  cases h <;> rfl

theorem evalLetValue_supported_ok {val : LCNF.LetValue .impure}
    (hsup : SupportedLetValue val) : ∃ result, evalLetValue val = .ok result := by
  cases hsup with
  | lit value => exact ⟨.lit value, rfl⟩
  | erased => exact ⟨.erased, rfl⟩

theorem eval_sound {env : Env} {code : LCNF.Code .impure} {result : Value} :
    SupportedCode code → eval env code = .ok result → Eval env code result := by
  intro hsup h
  induction hsup generalizing env result with
  | letDecl hval hk ih =>
      rename_i decl k
      cases hvalue : evalLetValue decl.value with
      | ok value =>
        rw [show eval env (.let decl k) =
            (do
              let value ← evalLetValue decl.value
              eval (bind env decl.fvarId value) k) by rfl] at h
        rw [hvalue] at h
        change eval (bind env decl.fvarId value) k = .ok result at h
        exact Eval.letDecl (evalLetValue_sound hval hvalue) (ih h)
      | error err =>
        rw [show eval env (.let decl k) =
            (do
              let value ← evalLetValue decl.value
              eval (bind env decl.fvarId value) k) by rfl] at h
        rw [hvalue] at h
        contradiction
  | ret x =>
      cases hlookup : lookup env x with
      | some value =>
        simp [eval, hlookup] at h
        cases h
        exact Eval.ret hlookup
      | none =>
        simp [eval, hlookup] at h
  | unreach type =>
      simp [eval] at h
  | inc hk ih =>
      exact Eval.inc (ih h)

theorem eval_complete {env : Env} {code : LCNF.Code .impure} {result : Value} :
    Eval env code result → eval env code = .ok result := by
  intro h
  induction h with
  | letDecl hval hk ih =>
      rename_i env decl k value result
      rw [show eval env (.let decl k) =
          (do
            let value ← evalLetValue decl.value
            eval (bind env decl.fvarId value) k) by rfl]
      rw [evalLetValue_complete hval]
      change eval (bind env decl.fvarId value) k = .ok _
      exact ih
  | ret hlookup =>
      simp [eval, hlookup]
  | inc hk ih =>
      simp [eval, ih]

theorem eval_iff {env : Env} {code : LCNF.Code .impure} {result : Value} :
    SupportedCode code → (eval env code = .ok result ↔ Eval env code result) :=
  fun hsup => ⟨eval_sound hsup, eval_complete⟩

theorem eval_supported_ne_unsupported {env : Env} {code : LCNF.Code .impure}
    (hsup : SupportedCode code) :
    eval env code ≠ .error .unsupported := by
  induction hsup generalizing env with
  | letDecl hval hk ih =>
      rename_i decl k
      obtain ⟨value, hvalue⟩ := evalLetValue_supported_ok hval
      rw [show eval env (.let decl k) =
          (do
            let value ← evalLetValue decl.value
            eval (bind env decl.fvarId value) k) by rfl]
      rw [hvalue]
      change eval (bind env decl.fvarId value) k ≠ .error .unsupported
      exact ih
  | ret x =>
      cases hlookup : lookup env x <;> simp [eval, hlookup]
  | unreach type =>
      simp [eval]
  | inc hk ih =>
      simp [eval, ih]

theorem eval_supported?_ne_unsupported {env : Env} {code : LCNF.Code .impure}
    (hsup : supportedCode? code = true) :
    eval env code ≠ .error .unsupported :=
  eval_supported_ne_unsupported ((supportedCode?_eq_true).1 hsup)

theorem eval_return_eq {env : Env} {x : FVarId} {value : Value}
    (hlookup : lookup env x = some value) :
    eval env (.return x) = .ok value := by
  simp [eval, hlookup]

theorem eval_let_lit_return (env : Env) (x : FVarId) (type : Expr)
    (value : LCNF.LitValue) :
  eval env (.let { fvarId := x, binderName := x.name, type := type, value := .lit value }
      (.return x)) = .ok (.lit value) := by
  change eval (bind env x (.lit value)) (.return x) = .ok (.lit value)
  simp [eval]

theorem eval_unknown_return (x : FVarId) :
    eval ({} : Env) (.return x) = .error (.unknownVar x) := by
  simp [eval, lookup]

theorem eval_unreachable (env : Env) (type : Expr) :
    eval env (.unreach type) = .error .unreachable := by
  simp [eval]

theorem eval_inc (env : Env) (fvarId : FVarId) (n : Nat) (check persistent : Bool)
    (k : LCNF.Code .impure) :
    eval env (.inc fvarId n check persistent k) = eval env k := by
  rfl

theorem eval_let_erased_return (env : Env) (x : FVarId) (type : Expr) :
  eval env (.let { fvarId := x, binderName := x.name, type := type, value := .erased }
      (.return x)) = .ok .erased := by
  change eval (bind env x .erased) (.return x) = .ok .erased
  simp [eval]

end LCNFCore

end Fir.LeanIR
