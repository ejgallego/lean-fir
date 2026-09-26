import Lean.Meta

/-! Constructor-only quotation and readback. These routines never evaluate generated code.
The public LCNF boundary kernel-checks definitions and requires canonical round trips. -/
namespace Fir.Compiler.Lcnf.Structural
open Lean

abbrev Result := Except String

class Codec (α : Type) where
  type : Expr
  quote : α → Result Expr
  read : Expr → Result α

def q [Codec α] (a : α) : Result Expr := Codec.quote a
def r [Codec α] (e : Expr) : Result α := Codec.read e
def ty (α : Type) [Codec α] : Expr := Codec.type (α := α)
def app (n : Name) (xs : Array Expr := #[]) : Expr := mkAppN (mkConst n) xs

def fields (e : Expr) (n : Name) (size : Nat) : Result (Array Expr) :=
  if e.getAppFn.isConstOf n && e.getAppNumArgs == size then .ok e.getAppArgs
  else .error s!"structural quotation: expected {n} with {size} arguments"

instance : Codec Nat where
  type := mkConst ``Nat
  quote n := .ok (mkRawNatLit n)
  read e := match e with
    | .lit (.natVal n) => .ok n
    | _ => .error s!"structural quotation: expected Nat literal, got {repr e}"

instance : Codec String where
  type := mkConst ``String
  quote s := .ok (mkStrLit s)
  read e := match e with
    | .lit (.strVal s) => .ok s
    | _ => .error "structural quotation: expected String literal"

instance : Codec Bool where
  type := mkConst ``Bool
  quote b := .ok (app (if b then ``Bool.true else ``Bool.false))
  read e := if e == app ``Bool.true then .ok true
    else if e == app ``Bool.false then .ok false
    else .error "structural quotation: expected Bool constructor"

private def quoteName : Name → Result Expr
  | .anonymous => pure (app ``Name.anonymous)
  | .str p s => return app ``Name.str #[← quoteName p, ← q s]
  | .num p n => return app ``Name.num #[← quoteName p, ← q n]

private partial def readName (e : Expr) : Result Name := do
  if e == app ``Name.anonymous then return .anonymous
  if e.getAppFn.isConstOf ``Name.str then
    let xs ← fields e ``Name.str 2
    return .str (← readName xs[0]!) (← r xs[1]!)
  let xs ← fields e ``Name.num 2
  return .num (← readName xs[0]!) (← r xs[1]!)

instance : Codec Name := ⟨mkConst ``Name, quoteName, readName⟩

private partial def readList [Codec α] (e : Expr) : Result (List α) := do
  if e.getAppFn.isConstOf ``List.nil then
    let _ ← fields e ``List.nil 1
    return []
  let xs ← fields e ``List.cons 3
  return (← r xs[1]!) :: (← readList xs[2]!)

instance [Codec α] : Codec (List α) where
  type := mkApp (mkConst ``List [.zero]) (ty α)
  quote xs := xs.foldrM (fun x tail => do
    return mkAppN (mkConst ``List.cons [.zero]) #[ty α, ← q x, tail])
    (mkApp (mkConst ``List.nil [.zero]) (ty α))
  read := readList

instance [Codec α] : Codec (Array α) where
  type := mkApp (mkConst ``Array [.zero]) (ty α)
  quote xs := return mkAppN (mkConst ``Array.mk [.zero]) #[ty α, ← q xs.toList]
  read e := do
    let xs ← fields e ``Array.mk 2
    return (← r (α := List α) xs[1]!).toArray

instance [Codec α] : Codec (Option α) where
  type := mkApp (mkConst ``Option [.zero]) (ty α)
  quote
    | none => pure (mkApp (mkConst ``Option.none [.zero]) (ty α))
    | some a => return mkAppN (mkConst ``Option.some [.zero]) #[ty α, ← q a]
  read e := do
    if e.getAppFn.isConstOf ``Option.none then
      let _ ← fields e ``Option.none 1
      return none
    let xs ← fields e ``Option.some 2
    return some (← r xs[1]!)

instance : Codec FVarId where
  type := mkConst ``FVarId
  quote x := return app ``FVarId.mk #[← q x.name]
  read e := do return ⟨← r (← fields e ``FVarId.mk 1)[0]!⟩

private def quoteLevel : Level → Result Expr
  | .zero => pure (app ``Level.zero)
  | .succ u => return app ``Level.succ #[← quoteLevel u]
  | .max u v => return app ``Level.max #[← quoteLevel u, ← quoteLevel v]
  | .imax u v => return app ``Level.imax #[← quoteLevel u, ← quoteLevel v]
  | .param n => return app ``Level.param #[← q n]
  | .mvar n => return app ``Level.mvar #[app ``LevelMVarId.mk #[← q n.name]]

private partial def readLevel (e : Expr) : Result Level := do
  if e == app ``Level.zero then return .zero
  if e.getAppFn.isConstOf ``Level.succ then
    return .succ (← readLevel (← fields e ``Level.succ 1)[0]!)
  if e.getAppFn.isConstOf ``Level.max then
    let xs ← fields e ``Level.max 2
    return .max (← readLevel xs[0]!) (← readLevel xs[1]!)
  if e.getAppFn.isConstOf ``Level.imax then
    let xs ← fields e ``Level.imax 2
    return .imax (← readLevel xs[0]!) (← readLevel xs[1]!)
  if e.getAppFn.isConstOf ``Level.param then
    return .param (← r (← fields e ``Level.param 1)[0]!)
  let xs ← fields e ``Level.mvar 1
  return .mvar ⟨← r (← fields xs[0]! ``LevelMVarId.mk 1)[0]!⟩

instance : Codec Level := ⟨mkConst ``Level, quoteLevel, readLevel⟩

private def quoteBinder : BinderInfo → Expr
  | .default => app ``BinderInfo.default
  | .implicit => app ``BinderInfo.implicit
  | .strictImplicit => app ``BinderInfo.strictImplicit
  | .instImplicit => app ``BinderInfo.instImplicit

private def readBinder (e : Expr) : Result BinderInfo :=
  if e == quoteBinder .default then .ok .default
  else if e == quoteBinder .implicit then .ok .implicit
  else if e == quoteBinder .strictImplicit then .ok .strictImplicit
  else if e == quoteBinder .instImplicit then .ok .instImplicit
  else .error "structural quotation: invalid binder info"

/-- Metadata is rejected explicitly for now, rather than silently discarded.
Final impure LCNF's erased types contain no metadata in the nominated capture. -/
partial def quoteExpr : Expr → Result Expr
  | .bvar n => return app ``Expr.bvar #[← q n]
  | .fvar x => return app ``Expr.fvar #[← q x]
  | .mvar x => return app ``Expr.mvar #[app ``MVarId.mk #[← q x.name]]
  | .sort u => return app ``Expr.sort #[← q u]
  | .const n us => return app ``Expr.const #[← q n, ← q us]
  | .app f a => return app ``Expr.app #[← quoteExpr f, ← quoteExpr a]
  | .lam n t b bi => return app ``Expr.lam #[← q n, ← quoteExpr t, ← quoteExpr b, quoteBinder bi]
  | .forallE n t b bi => return app ``Expr.forallE #[← q n, ← quoteExpr t, ← quoteExpr b, quoteBinder bi]
  | .letE n t v b nd => return app ``Expr.letE #[← q n, ← quoteExpr t, ← quoteExpr v, ← quoteExpr b, ← q nd]
  | .lit (.natVal n) => return app ``Expr.lit #[app ``Literal.natVal #[← q n]]
  | .lit (.strVal s) => return app ``Expr.lit #[app ``Literal.strVal #[← q s]]
  | .mdata .. => .error "structural quotation: Expr.mdata is unsupported (metadata would be lost)"
  | .proj n i e => return app ``Expr.proj #[← q n, ← q i, ← quoteExpr e]

partial def readExpr (e : Expr) : Result Expr := do
  let n := e.getAppFn.constName?.getD .anonymous
  if n == ``Expr.bvar then return .bvar (← r (← fields e n 1)[0]!)
  if n == ``Expr.fvar then return .fvar (← r (← fields e n 1)[0]!)
  if n == ``Expr.mvar then
    return .mvar ⟨← r (← fields (← fields e n 1)[0]! ``MVarId.mk 1)[0]!⟩
  if n == ``Expr.sort then return .sort (← r (← fields e n 1)[0]!)
  if n == ``Expr.const then
    let xs ← fields e n 2
    return .const (← r xs[0]!) (← r xs[1]!)
  if n == ``Expr.app then
    let xs ← fields e n 2
    return .app (← readExpr xs[0]!) (← readExpr xs[1]!)
  if n == ``Expr.lam || n == ``Expr.forallE then
    let xs ← fields e n 4
    let name ← r xs[0]!
    let type ← readExpr xs[1]!
    let body ← readExpr xs[2]!
    let bi ← readBinder xs[3]!
    return if n == ``Expr.lam then .lam name type body bi else .forallE name type body bi
  if n == ``Expr.letE then
    let xs ← fields e n 5
    return .letE (← r xs[0]!) (← readExpr xs[1]!) (← readExpr xs[2]!) (← readExpr xs[3]!) (← r xs[4]!)
  if n == ``Expr.lit then
    let lit := (← fields e n 1)[0]!
    if lit.getAppFn.isConstOf ``Literal.natVal then
      return .lit (.natVal (← r (← fields lit ``Literal.natVal 1)[0]!))
    return .lit (.strVal (← r (← fields lit ``Literal.strVal 1)[0]!))
  if n == ``Expr.proj then
    let xs ← fields e n 3
    return .proj (← r xs[0]!) (← r xs[1]!) (← readExpr xs[2]!)
  throw "structural quotation: unsupported Expr constructor"

instance : Codec Expr := ⟨mkConst ``Expr, quoteExpr, readExpr⟩

end Fir.Compiler.Lcnf.Structural
