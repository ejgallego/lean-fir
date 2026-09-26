import Fir.Compiler.LCNF.Reify
import Lean.Elab.Command

/-! Kernel-checked regression corpus for the retained-program source boundary.
These are structural AST tests, not claims that arbitrary synthetic LCNF is
well formed as executable code. The real retained source is checked separately. -/
namespace Fir.Compiler.Lcnf.ReifyExamples
open Lean Lean.Compiler Fir.LeanIR Elab Command Reify Structural

private def x : FVarId := ⟨`x⟩
private def t := mkConst ``Nat
private def ci : LCNF.CtorInfo := ⟨`Fixture.ctor, 7, 2, 1, 8⟩
private def ret : LCNF.Code .impure := .return x
private def arg : LCNF.Arg .impure := .fvar x

private def expressions : Array Expr := #[
  .bvar 5, .fvar x, .mvar ⟨`m⟩,
  .sort (.imax (.max (.param `u) (.succ .zero)) (.mvar ⟨`v⟩)),
  .const `Fixture.type [.param `u, .zero], .app t (.bvar 1),
  .lam `named t (.bvar 0) .implicit,
  .forallE `other t (.bvar 0) .strictImplicit,
  .lam `instance t (.bvar 0) .instImplicit,
  .letE `bound t (mkNatLit 8) (.bvar 0) true,
  .letE `bound2 t (mkStrLit "λ☃") (.bvar 0) false,
  .proj `Fixture.ctor 3 (.fvar x)]

private def letValues : Array (LCNF.LetValue .impure) := #[
  .lit (.nat 999999999999999999999), .lit (.str "λ☃"),
  .lit (.uint8 255), .lit (.uint16 65535), .lit (.uint32 4294967295),
  .lit (.uint64 18446744073709551615), .lit (.usize 18446744073709551615),
  .erased, .fvar x #[.erased, arg], .ctor ci #[arg], .oproj 3 x,
  .uproj 4 x, .sproj 2 7 x, .fap `callee #[arg], .pap `callee #[arg],
  .reset 2 x, .reuse x ci true #[arg], .box t x, .unbox x, .isShared x]

private def codes : Array (LCNF.Code .impure) := #[
  .jp ⟨x, `join, #[⟨x, `p, t, true⟩], t, ret⟩ (.jmp x #[arg]),
  .cases ⟨`Fixture, t, x, #[.ctorAlt ci ret, .default (.unreach t)]⟩,
  .oset x 2 arg ret, .uset x 1 x ret, .sset x 1 2 x t ret,
  .setTag x 7 ret, .inc x 2 true false ret,
  .dec x 3 false true (some 2) ret, .dec x 1 true false none ret,
  .del x ret, .unreach t, ret]

private def fixture : ImpureProgram := Id.run do
  let mut ds : Array (LCNF.Decl .impure) := #[]
  for e in expressions do
    ds := ds.push {
      name := Name.num `expr ds.size, type := e, params := #[]
      levelParams := [`u, `v], safe := false, recursive := true,
      inlineAttr? := some .alwaysInline, value := .code ret }
  for v in letValues do
    ds := ds.push {
      name := Name.num `letValue ds.size, type := t, params := #[]
      levelParams := [], inlineAttr? := none
      value := .code (.let ⟨x, `local, t, v⟩ ret) }
  for c in codes do
    ds := ds.push {
      name := Name.num `code ds.size, type := t, params := #[]
      levelParams := [], inlineAttr? := none, value := .code c }
  for a in [InlineAttributeKind.inline, .noinline, .macroInline, .inlineIfReduce] do
    ds := ds.push {
      name := Name.num `external ds.size, type := t, params := #[]
      levelParams := []
      inlineAttr? := some a, value := .extern ⟨[.opaque, .adhoc `cpp,
        .inline `c "value", .standard `c "symbol"]⟩ }
  return ⟨ds⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
run_cmd do
  let checked ← liftCoreM <| defineProgram `Fir.Compiler.Lcnf.ReifyExamples.checkedProgram fixture
  unless (quoteProgram checked).toOption == (quoteProgram fixture).toOption do
    throwError "structural positive failed"
  liftTermElabM <| defineDeclEquations `Fir.Compiler.Lcnf.ReifyExamples.checkedProgram
    (.num `letValue expressions.size) `Fir.Compiler.Lcnf.ReifyExamples.initializer
  let malformed := [mkNatLit 0, mkConst ``Nat,
    app ``Program.mk #[mkConst ``LCNF.Phase.impure, mkNatLit 0]]
  for e in malformed do
    if (readProgram e).isOk then throwError "malformed input accepted"
  let bad := { fixture with decls := fixture.decls.map fun d =>
    { d with type := .mdata {} d.type } }
  if (quoteProgram bad).isOk then throwError "unsupported metadata accepted"
  let .ok quoted := quoteProgram fixture | throwError "positive quotation failed"
  let wrongPhase := mkAppN quoted.getAppFn
    #[mkConst ``LCNF.Phase.mono, quoted.getAppArgs[1]!]
  if (readProgram wrongPhase).isOk then throwError "wrong phase accepted"
  -- Binder names are data, not alpha-equivalent syntax at this boundary.
  let .ok left := quoteExpr (.lam `left t (.bvar 0) .default) | throwError "left failed"
  let .ok right := quoteExpr (.lam `right t (.bvar 0) .default) | throwError "right failed"
  if left == right then throwError "binder names erased"
  for n in [`Fir.Compiler.Lcnf.ReifyExamples.checkedProgram,
      `Fir.Compiler.Lcnf.ReifyExamples.initializer.findDecl,
      `Fir.Compiler.Lcnf.ReifyExamples.initializer.body] do
    let axioms ← liftCoreM <| collectAxioms n
    -- Array.find? brings Lean's standard propext through the theorem type;
    -- the generated proof itself is Eq.refl. No generated/native axioms.
    let expected := if n == `Fir.Compiler.Lcnf.ReifyExamples.initializer.findDecl
      then #[`propext] else #[]
    unless axioms == expected do
      throwError "unexpected axioms for {n}: {axioms}"

#check checkedProgram
#check initializer.findDecl
#check initializer.body
#print axioms initializer.findDecl
#print axioms initializer.body

end Fir.Compiler.Lcnf.ReifyExamples
