import Fir.LeanIR.Phase

namespace Fir.Wasm

open Lean
open Lean.Compiler

inductive ValueType where
  | i32
  | i64
  deriving Inhabited, BEq, Repr

def valueType (type : Expr) : ValueType :=
  if type == LCNF.ImpureType.uint64 || type == LCNF.ImpureType.usize then .i64 else .i32

def resultTypes (type : Expr) : Array ValueType :=
  if type.isVoid then #[] else #[valueType type]

structure Signature where
  params : Array ValueType
  results : Array ValueType
  deriving Inhabited, BEq, Repr

inductive RuntimeOp where
  | literal (value : LCNF.LitValue)
  | allocCtor (info : LCNF.CtorInfo) (fields : Array ValueType)
  | objectProj (index : Nat)
  | usizeProj (index : Nat)
  | scalarProj (width offset : Nat) (result : ValueType)
  | partialApply (function : Name) (arity fixed : Nat) (fields : Array ValueType)
  | closureApply (args : Array ValueType) (result : Array ValueType)
  | reset (objectFields : Nat)
  | reuse (info : LCNF.CtorInfo) (updateHeader : Bool) (fields : Array ValueType)
  | box (scalar : ValueType)
  | unbox (scalar : ValueType)
  | isShared
  | objectSet (index : Nat) (field : ValueType)
  | usizeSet (index : Nat)
  | scalarSet (width offset : Nat) (field : ValueType)
  | setTag (tag : Nat)
  | inc (amount : Nat) (check : Bool)
  | dec (amount : Nat) (check : Bool) (objectFields? : Option Nat)
  | delete
  | getTag
  deriving Inhabited, BEq

def RuntimeOp.signature : RuntimeOp → Signature
  | .literal _ => { params := #[], results := #[.i32] }
  | .allocCtor _ fields => { params := fields, results := #[.i32] }
  | .objectProj _ => { params := #[.i32], results := #[.i32] }
  | .usizeProj _ => { params := #[.i32], results := #[.i64] }
  | .scalarProj _ _ result => { params := #[.i32], results := #[result] }
  | .partialApply _ _ _ fields => { params := fields, results := #[.i32] }
  | .closureApply args result => { params := #[.i32] ++ args, results := result }
  | .reset _ => { params := #[.i32], results := #[.i32] }
  | .reuse _ _ fields => { params := #[.i32] ++ fields, results := #[.i32] }
  | .box scalar => { params := #[scalar], results := #[.i32] }
  | .unbox scalar => { params := #[.i32], results := #[scalar] }
  | .isShared => { params := #[.i32], results := #[.i32] }
  | .objectSet _ field => { params := #[.i32, field], results := #[] }
  | .usizeSet _ => { params := #[.i32, .i64], results := #[] }
  | .scalarSet _ _ field => { params := #[.i32, field], results := #[] }
  | .setTag _ => { params := #[.i32], results := #[] }
  | .inc _ _ => { params := #[.i32], results := #[] }
  | .dec _ _ _ => { params := #[.i32], results := #[] }
  | .delete => { params := #[.i32], results := #[] }
  | .getTag => { params := #[.i32], results := #[.i32] }

def RuntimeOp.stem : RuntimeOp → String
  | .literal _ => "literal"
  | .allocCtor .. => "alloc_ctor"
  | .objectProj .. => "oproj"
  | .usizeProj .. => "uproj"
  | .scalarProj .. => "sproj"
  | .partialApply .. => "pap"
  | .closureApply .. => "apply"
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

structure Import where
  moduleName : String
  itemName : String
  signature : Signature
  operation? : Option RuntimeOp := none
  declaration? : Option Name := none
  deriving Inhabited, BEq

def runtimeImport (index : Nat) (operation : RuntimeOp) : Import :=
  { moduleName := "fir"
    itemName := s!"{operation.stem}_{index}"
    signature := operation.signature
    operation? := some operation }

def externalImport (decl : LCNF.Decl .impure) : Import :=
  { moduleName := "lean.extern"
    itemName := decl.name.toString
    signature := {
      params := decl.params.map (valueType ·.type)
      results := resultTypes decl.type }
    declaration? := some decl.name }

end Fir.Wasm
