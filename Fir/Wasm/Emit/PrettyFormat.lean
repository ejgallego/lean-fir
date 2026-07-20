import Fir.Wasm.Emit.Source
import Fir.Wasm.PrettyFormat

namespace Fir.Wasm.Emit.PrettyFormat

open Lean
open Lean.Compiler
open Fir.Wasm.Emit.Source

/-- The only compiler-generated helper deliberately retained during source internalization. -/
def weakMonadInhabitedName : String := "instInhabitedOfMonad._redArg"

private partial def weakCallCount : LCNF.Code .impure → Nat
  | .let decl continuation =>
      let own := match decl.value with
        | .fap name _ => if name.toString == weakMonadInhabitedName then 1 else 0
        | _ => 0
      own + weakCallCount continuation
  | .jp decl continuation => weakCallCount decl.value + weakCallCount continuation
  | .cases cases => cases.alts.foldl (init := 0) fun count alt =>
      count + weakCallCount alt.getCode
  | .jmp .. | .return .. | .unreach .. => 0
  | .oset (k := continuation) .. | .uset (k := continuation) .. |
      .sset (k := continuation) .. | .setTag (k := continuation) .. |
      .inc (k := continuation) .. | .dec (k := continuation) .. |
      .del (k := continuation) .. => weakCallCount continuation
  | .fun _ _ h => nomatch h

mutual

private partial def refineWeakCalls : LCNF.Code .impure → Except String (LCNF.Code .impure)
  | .let decl continuation => do
      let decl ← match decl.value with
        | .fap name _ =>
            if name.toString == weakMonadInhabitedName then
              unless decl.type == LCNF.ImpureType.tobject do
                throw "weak Monad Inhabited call no longer binds a tobject result"
              pure { decl with type := LCNF.ImpureType.object }
            else
              pure decl
        | _ => pure decl
      return .let decl (← refineWeakCalls continuation)
  | .jp (.mk id binder params type value) continuation =>
      return .jp (.mk id binder params type (← refineWeakCalls value))
        (← refineWeakCalls continuation)
  | .cases (.mk typeName resultType discr alts) =>
      return .cases (.mk typeName resultType discr (← alts.mapM refineWeakAlt))
  | code@(.jmp ..) | code@(.return ..) | code@(.unreach ..) => return code
  | .oset objectId index value continuation =>
      return .oset objectId index value (← refineWeakCalls continuation)
  | .uset objectId index value continuation =>
      return .uset objectId index value (← refineWeakCalls continuation)
  | .sset objectId width offset value type continuation =>
      return .sset objectId width offset value type (← refineWeakCalls continuation)
  | .setTag objectId tag continuation =>
      return .setTag objectId tag (← refineWeakCalls continuation)
  | .inc objectId amount check persistent continuation =>
      return .inc objectId amount check persistent (← refineWeakCalls continuation)
  | .dec objectId amount check persistent objects continuation =>
      return .dec objectId amount check persistent objects (← refineWeakCalls continuation)
  | .del objectId continuation =>
      return .del objectId (← refineWeakCalls continuation)
  | .fun _ _ h => nomatch h

private partial def refineWeakAlt : LCNF.Alt .impure → Except String (LCNF.Alt .impure)
  | .ctorAlt info code => return .ctorAlt info (← refineWeakCalls code)
  | .default code => return .default (← refineWeakCalls code)
  | .alt _ _ _ h => nomatch h

end

/--
Refine Lean 4.32's generated weak specialization at its one concrete use.

The generated helper implements `Inhabited (PrettyRenderM Unit)`, so its result
is a function closure and therefore a heap object. Final LCNF retains only the
generic `tobject` signature of `_redArg`; this checked rewrite restores the
monomorphic result on both the external declaration and its sole call binding.
-/
def refineWeakMonadInhabited (artifact : Fir.Validation.Lcnf.Artifact) :
    Except String Fir.Validation.Lcnf.Artifact := do
  unless artifact.externalNames.map (fun name => name.toString) == #[weakMonadInhabitedName] do
    throw s!"internalized Format helper inventory changed: {artifact.externalNames.map (fun name => name.toString)}"
  let targets := artifact.program.decls.filter fun decl =>
    decl.name.toString == weakMonadInhabitedName
  unless targets.size == 1 do
    throw s!"expected one weak Monad Inhabited declaration, found {targets.size}"
  let target := targets[0]!
  match target.value with
  | .code _ => throw "weak Monad Inhabited helper unexpectedly became local code"
  | .extern _ => pure ()
  unless Fir.Wasm.abiValueKind? target.type == some .tobject &&
      target.params.mapM (fun param => Fir.Wasm.abiValueKind? param.type) ==
        some #[.object, .tobject] do
    throw "weak Monad Inhabited signature changed"
  let callCount := artifact.program.decls.foldl (init := 0) fun count decl =>
    match decl.value with
    | .code code => count + weakCallCount code
    | .extern _ => count
  unless callCount == 1 do
    throw s!"expected one weak Monad Inhabited call, found {callCount}"
  let decls ← artifact.program.decls.mapM fun decl =>
    if decl.name.toString == weakMonadInhabitedName then
      return { decl with type := LCNF.ImpureType.object }
    else
      return { decl with value := ← decl.value.mapCodeM refineWeakCalls }
  let program : Fir.LeanIR.ImpureProgram := { decls }
  return { artifact with
    program
    forms := Fir.Validation.Lcnf.collectForms program }

/-- Capture, internalize, normalize, lower, and encode a locally expanded Format facade. -/
def compileModule (entry : Name) :
    CoreM (Except Source.CompileError Source.ModuleArtifact) := do
  let source ← compileEntryInternalized entry #[] #[weakMonadInhabitedName]
  let source ← match refineWeakMonadInhabited source with
    | .ok source => pure source
    | .error message => return .error (.manifest message)
  compileModuleArtifact source

end Fir.Wasm.Emit.PrettyFormat
