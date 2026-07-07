import Fir.LeanIR.LCNFCore

namespace Fir.LeanIR

namespace LCNFExamples

open Lean
open Lean.Compiler
open LCNFCore

def x : FVarId := ⟨`x⟩
def y : FVarId := ⟨`y⟩

def type : Expr := .const ``Nat []

def lit42 : LCNF.LitValue := .nat 42
def lit7 : LCNF.LitValue := .nat 7

def letLitReturn : LCNF.Code .impure :=
  .let { fvarId := x, binderName := `x, type := type, value := .lit lit42 }
    (.return x)

def nestedLetReturnFirst : LCNF.Code .impure :=
  .let { fvarId := x, binderName := `x, type := type, value := .lit lit42 }
    (.let { fvarId := y, binderName := `y, type := type, value := .lit lit7 }
      (.return x))

def shadowingReturnLatest : LCNF.Code .impure :=
  .let { fvarId := x, binderName := `x, type := type, value := .lit lit42 }
    (.let { fvarId := x, binderName := `x, type := type, value := .lit lit7 }
      (.return x))

def erasedLetReturn : LCNF.Code .impure :=
  .let { fvarId := x, binderName := `x, type := type, value := .erased }
    (.return x)

def incLetReturn : LCNF.Code .impure :=
  .let { fvarId := x, binderName := `x, type := type, value := .lit lit42 }
    (.inc x 1 true false (.return x))

def idParam : LCNF.Param .impure :=
  { fvarId := x, binderName := `x, type := type, borrow := true }

def idDecl : LCNF.Decl .impure :=
  { name := `idDecl
    levelParams := []
    type := type
    params := #[idParam]
    value := .code (.inc x 1 true false (.return x))
    safe := true
    recursive := false
    inlineAttr? := none }

example : eval ({} : Env) letLitReturn = .ok (.lit lit42) := by
  rfl

example : Eval ({} : Env) letLitReturn (.lit lit42) := by
  exact eval_sound (SupportedCode.letDecl (SupportedLetValue.lit lit42) (SupportedCode.ret x)) rfl

example : eval ({} : Env) (.return y) = .error (.unknownVar y) := by
  rfl

example : eval ({} : Env) (.unreach type) = .error .unreachable := by
  rfl

example : eval ({} : Env) nestedLetReturnFirst = .ok (.lit lit42) := by
  rfl

example : eval ({} : Env) shadowingReturnLatest = .ok (.lit lit7) := by
  rfl

example : eval ({} : Env) erasedLetReturn = .ok .erased := by
  rfl

example : eval ({} : Env) incLetReturn = .ok (.lit lit42) := by
  rfl

example : bindParams ({} : Env) #[idParam] [.lit lit42] =
    .ok (bind ({} : Env) x (.lit lit42)) := by
  rfl

example : evalDecl [.lit lit42] idDecl = .ok (.lit lit42) := by
  rfl

example : evalDecl [] idDecl = .error (.arityMismatch 1 0) := by
  rfl

def unsupportedSetTag : LCNF.Code .impure :=
  .setTag x 0 (.return x)

example : eval ({} : Env) unsupportedSetTag = .error .unsupported := by
  rfl

example : supportedCode? letLitReturn = true := by
  rfl

example : supportedCode? nestedLetReturnFirst = true := by
  rfl

example : supportedCode? shadowingReturnLatest = true := by
  rfl

example : supportedCode? erasedLetReturn = true := by
  rfl

example : supportedCode? incLetReturn = true := by
  rfl

example : supportedCode? unsupportedSetTag = false := by
  rfl

example : eval ({} : Env) erasedLetReturn ≠ .error .unsupported :=
  eval_supported?_ne_unsupported (by rfl)

example : SupportedCode letLitReturn := by
  exact SupportedCode.letDecl (SupportedLetValue.lit lit42) (SupportedCode.ret x)

example : SupportedCode incLetReturn := by
  exact SupportedCode.letDecl (SupportedLetValue.lit lit42)
    (SupportedCode.inc (SupportedCode.ret x))

end LCNFExamples

end Fir.LeanIR
