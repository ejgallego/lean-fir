import Fir.LeanIR.Phase

namespace Fir.Wasm

open Lean
open Lean.Compiler

/-- The physical WebAssembly value classes used by FIR. -/
inductive ValueType where
  | i32
  | i64
  | f32
  | f64
  deriving Inhabited, BEq, Repr

/--
Semantic value classes at the LCNF/WebAssembly boundary.

Several of these classes have the same physical WebAssembly representation.  They
remain distinct here so that lowering, imports, and the future correctness
statements do not silently forget the LCNF contract.
-/
inductive AbiKind where
  | object
  | tagged
  | tobject
  | erased
  | reuseToken
  | uint8
  | uint16
  | uint32
  | uint64
  | usize
  | float32
  | float
  deriving Inhabited, BEq, Repr

def AbiKind.valueType : AbiKind → ValueType
  | .object | .tagged | .tobject | .erased | .reuseToken
  | .uint8 | .uint16 | .uint32 => .i32
  | .uint64 | .usize => .i64
  | .float32 => .f32
  | .float => .f64

/-- The only semantic subtyping in the ABI is a precise object representation into `tobject`. -/
def AbiKind.refines (actual expected : AbiKind) : Bool :=
  actual == expected ||
    expected == .tobject && (actual == .object || actual == .tagged)

def AbiKind.isObjectLike : AbiKind → Bool
  | .object | .tagged | .tobject => true
  | _ => false

def AbiKind.isObjectField : AbiKind → Bool
  | .object | .tagged | .tobject | .erased => true
  | _ => false

def AbiKind.isScalar : AbiKind → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 | .usize | .float32 | .float => true
  | _ => false

inductive AbiError where
  | unsupportedType (type : Expr)
  | expectedValueType (type : Expr)
  deriving Inhabited, BEq, Repr

/--
Classify an impure LCNF type. `none` is the ABI representation of `void`: it
contributes no parameter, local, or result. Unknown types are rejected.
-/
def abiKind? (type : Expr) : Except AbiError (Option AbiKind) :=
  if type == LCNF.ImpureType.object then
    pure (some .object)
  else if type == LCNF.ImpureType.tagged then
    pure (some .tagged)
  else if type == LCNF.ImpureType.tobject then
    pure (some .tobject)
  else if type == LCNF.ImpureType.erased then
    pure (some .erased)
  else if type == LCNF.ImpureType.uint8 then
    pure (some .uint8)
  else if type == LCNF.ImpureType.uint16 then
    pure (some .uint16)
  else if type == LCNF.ImpureType.uint32 then
    pure (some .uint32)
  else if type == LCNF.ImpureType.uint64 then
    pure (some .uint64)
  else if type == LCNF.ImpureType.usize then
    pure (some .usize)
  else if type == LCNF.ImpureType.float32 then
    pure (some .float32)
  else if type == LCNF.ImpureType.float then
    pure (some .float)
  else if type == LCNF.ImpureType.void then
    pure none
  else
    throw (.unsupportedType type)

def abiKind (type : Expr) : Except AbiError AbiKind := do
  let some kind ← abiKind? type | throw (.expectedValueType type)
  return kind

def resultKinds (type : Expr) : Except AbiError (Array AbiKind) := do
  match ← abiKind? type with
  | some kind => return #[kind]
  | none => return #[]

def literalKind : LCNF.LitValue → AbiKind
  | .nat _ => .tobject
  | .str _ => .object
  | .uint8 _ => .uint8
  | .uint16 _ => .uint16
  | .uint32 _ => .uint32
  | .uint64 _ => .uint64
  | .usize _ => .usize

def constructorKind (info : LCNF.CtorInfo) : AbiKind :=
  if info.size == 0 && info.usize == 0 && info.ssize == 0 then .tagged else .object

/-- Case dispatch uses an `i32` tag lane, so source `Nat` tags must not wrap. -/
def constructorTagFitsI32 (info : LCNF.CtorInfo) : Bool :=
  decide (info.cidx < UInt32.size)

/-- A scalar `UInt8` case discriminator can only denote constructor tags below `2^8`. -/
def constructorTagFitsUInt8 (info : LCNF.CtorInfo) : Bool :=
  decide (info.cidx < UInt8.size)

/--
Scalar literals must match exactly. The wider object-like cases preserve the
existing hand-built fixtures tracked by
`FIR-BUG-wasm-none-object-nat-fixture`; compiler-produced `Nat` literals are
expected to use `tobject`.
-/
def AbiKind.acceptsLiteral (kind : AbiKind) (literal : LCNF.LitValue) : Bool :=
  match literal with
  | .nat _ => kind == .object || kind == .tagged || kind == .tobject
  | .str _ => kind == .object || kind == .tobject
  | literal => kind == literalKind literal

/--
The invariant expected of compiler-produced final impure LCNF. Small natural
literals may receive Lean's precise `tagged` representation; otherwise a
natural literal retains the representation-polymorphic `tobject` kind.
-/
def AbiKind.acceptsLiteralInvariant (kind : AbiKind)
    (literal : LCNF.LitValue) : Bool :=
  match literal with
  | .nat _ => kind == .tagged || kind == .tobject
  | literal => kind.acceptsLiteral literal

/-- Every compiler-invariant literal annotation is accepted by lowering. -/
theorem AbiKind.acceptsLiteral_of_acceptsLiteralInvariant
    {kind : AbiKind} {literal : LCNF.LitValue}
    (accepted : kind.acceptsLiteralInvariant literal = true) :
    kind.acceptsLiteral literal = true := by
  cases literal with
  | nat =>
      simp only [AbiKind.acceptsLiteralInvariant, AbiKind.acceptsLiteral,
        Bool.or_eq_true] at accepted ⊢
      rcases accepted with tagged | tobject
      · exact .inl (.inr tagged)
      · exact .inr tobject
  | str | uint8 | uint16 | uint32 | uint64 | usize => exact accepted

structure Signature where
  params : Array AbiKind
  results : Array AbiKind
  deriving Inhabited, BEq

structure PhysicalSignature where
  params : Array ValueType
  results : Array ValueType
  deriving Inhabited, BEq

/-- The source-level types carried by an external declaration.  Keeping this
metadata at the symbolic boundary lets the semantic host reconstruct exactly
the `ExternalRequest` seen by the LCNF interpreter, rather than guessing from
the coarser physical Wasm lanes. -/
structure ExternalTypes where
  params : Array Expr
  result : Expr
  deriving Inhabited, BEq

def Signature.physical (signature : Signature) : PhysicalSignature :=
  { params := signature.params.map AbiKind.valueType
    results := signature.results.map AbiKind.valueType }

inductive RuntimeOp where
  | literal (value : LCNF.LitValue) (result : AbiKind)
  | allocCtor (info : LCNF.CtorInfo) (fields : Array AbiKind) (result : AbiKind)
  | objectProj (index : Nat) (result : AbiKind)
  | usizeProj (index : Nat)
  | scalarProj (width offset : Nat) (result : AbiKind)
  | cacheSet (declaration : Name) (value : AbiKind)
  | partialApply (function : Name) (arity fixed : Nat) (fields : Array AbiKind)
      (result : AbiKind)
  | closureApply (args : Array AbiKind) (result : Array AbiKind)
  | closureMatches (function : Name) (arity fixed : Nat)
  | closureProj (function : Name) (arity fixed index : Nat) (result : AbiKind)
  | reset (objectFields : Nat)
  | reuse (info : LCNF.CtorInfo) (updateHeader : Bool) (fields : Array AbiKind)
      (result : AbiKind)
  | box (scalar result : AbiKind)
  | unbox (scalar : AbiKind)
  | isShared
  | objectSet (index : Nat) (field : AbiKind)
  | usizeSet (index : Nat)
  | scalarSet (width offset : Nat) (field : AbiKind)
  | setTag (tag : Nat)
  | inc (amount : Nat) (check : Bool)
  | dec (amount : Nat) (check : Bool) (objectFields? : Option Nat)
  | delete
  | getTag
  deriving Inhabited, BEq

/-- Operation-specific semantic constraints not expressible by the plain constructor fields. -/
def RuntimeOp.abiWellFormed : RuntimeOp → Bool
  | .literal value result => result.acceptsLiteral value
  | .allocCtor info fields result =>
      info.size == fields.size && fields.all AbiKind.isObjectField &&
        (constructorKind info).refines result
  | .objectProj _ result => result.isObjectField
  | .usizeProj _ => true
  | .scalarProj _ _ result => result.isScalar
  | .cacheSet _ value => value != .erased
  | .partialApply _ arity fixed fields result =>
      fixed < arity && fields.size == fixed && result.isObjectLike
  | .closureApply _ results => results.size <= 1
  | .closureMatches _ arity fixed => fixed < arity
  | .closureProj _ arity fixed index result =>
      fixed < arity && index < fixed && result != .erased
  | .reset _ => true
  | .reuse info _ fields result =>
      info.size == fields.size && fields.all AbiKind.isObjectField &&
        (constructorKind info).refines result
  | .box scalar result => scalar.isScalar && result.isObjectLike
  | .unbox scalar => scalar.isScalar
  | .isShared => true
  | .objectSet _ field => field.isObjectField
  | .usizeSet _ => true
  | .scalarSet _ _ field => field.isScalar
  | .setTag _ | .inc _ _ | .dec _ _ _ | .delete | .getTag => true

def RuntimeOp.signature : RuntimeOp → Signature
  | .literal _ result => { params := #[], results := #[result] }
  | .allocCtor _ fields result => { params := fields, results := #[result] }
  | .objectProj _ result => { params := #[.tobject], results := #[result] }
  | .usizeProj _ => { params := #[.tobject], results := #[.usize] }
  | .scalarProj _ _ result => { params := #[.tobject], results := #[result] }
  | .cacheSet _ value => { params := #[value], results := #[value] }
  | .partialApply _ _ _ fields result => { params := fields, results := #[result] }
  | .closureApply args result => { params := #[.tobject] ++ args, results := result }
  | .closureMatches _ _ _ => { params := #[.tobject], results := #[.uint32] }
  | .closureProj _ _ _ _ result => { params := #[.tobject], results := #[result] }
  | .reset _ => { params := #[.tobject], results := #[.reuseToken] }
  | .reuse _ _ fields result =>
      { params := #[.reuseToken] ++ fields, results := #[result] }
  | .box scalar result => { params := #[scalar], results := #[result] }
  | .unbox scalar => { params := #[.tobject], results := #[scalar] }
  | .isShared => { params := #[.tobject], results := #[.uint8] }
  | .objectSet _ field => { params := #[.object, field], results := #[] }
  | .usizeSet _ => { params := #[.object, .usize], results := #[] }
  | .scalarSet _ _ field => { params := #[.object, field], results := #[] }
  | .setTag _ => { params := #[.object], results := #[] }
  | .inc _ _ => { params := #[.tobject], results := #[] }
  | .dec _ _ _ => { params := #[.tobject], results := #[] }
  | .delete => { params := #[.object], results := #[] }
  | .getTag => { params := #[.tobject], results := #[.uint32] }

def RuntimeOp.stem : RuntimeOp → String
  | .literal .. => "literal"
  | .allocCtor .. => "alloc_ctor"
  | .objectProj .. => "oproj"
  | .usizeProj .. => "uproj"
  | .scalarProj .. => "sproj"
  | .cacheSet .. => "cache_set"
  | .partialApply .. => "pap"
  | .closureApply .. => "apply"
  | .closureMatches .. => "closure_matches"
  | .closureProj .. => "closure_proj"
  | .reset .. => "reset"
  | .reuse .. => "reuse"
  | .box .. => "box"
  | .unbox .. => "unbox"
  | .isShared => "is_shared"
  | .objectSet .. => "oset"
  | .usizeSet .. => "uset"
  | .scalarSet .. => "sset"
  | .setTag .. => "set_tag"
  | .inc .. => "inc"
  | .dec .. => "dec"
  | .delete => "delete"
  | .getTag => "get_tag"

/-- Stable semantic identity, independent of an import's presentation ordinal. -/
inductive ImportKey where
  | runtime (operation : RuntimeOp)
  | external (declaration : Name)
  deriving Inhabited, BEq

structure Import where
  key : ImportKey
  moduleName : String
  itemName : String
  signature : Signature
  externalTypes? : Option ExternalTypes := none
  deriving Inhabited, BEq

def Import.operation? (import_ : Import) : Option RuntimeOp :=
  match import_.key with
  | .runtime operation => some operation
  | .external _ => none

def Import.declaration? (import_ : Import) : Option Name :=
  match import_.key with
  | .runtime _ => none
  | .external declaration => some declaration

/-- Runtime imports are numbered in first-use order; their semantic key is stable. -/
def runtimeImport (index : Nat) (operation : RuntimeOp) : Import :=
  { key := .runtime operation
    moduleName := "fir"
    itemName := s!"{operation.stem}_{index}"
    signature := operation.signature }

def ExternalTypes.signature (types : ExternalTypes) : Except AbiError Signature := do
  let params ← types.params.foldlM (init := #[]) fun params type => do
    match ← abiKind? type with
    | some kind => return params.push kind
    | none => return params
  return { params, results := ← resultKinds types.result }

def externalImport (decl : LCNF.Decl .impure) : Except AbiError Import := do
  let externalTypes : ExternalTypes := {
    params := decl.params.map (·.type)
    result := decl.type }
  let signature ← externalTypes.signature
  return {
    key := .external decl.name
    moduleName := "lean.extern"
    itemName := decl.name.toString
    signature
    externalTypes? := some externalTypes }

end Fir.Wasm
