import Fir.Wasm.ABI

namespace Fir.Wasm

open Lean
open Lean.Compiler

inductive CallTarget where
  | declaration (name : Name)
  | runtime (operation : RuntimeOp)
  deriving Inhabited, BEq

inductive Instruction where
  | i32Const (value : UInt32)
  | i64Const (value : UInt64)
  | localGet (fvarId : FVarId)
  | localSet (fvarId : FVarId)
  | call (target : CallTarget)
  | i32Eq
  | block (label : FVarId) (body : List Instruction)
  | ifElse (thenBody elseBody : List Instruction)
  | br (label : FVarId)
  | ret
  | unreachable
  deriving Inhabited, BEq

structure Function where
  name : Name
  params : Array (FVarId × ValueType)
  results : Array ValueType
  locals : Array (FVarId × ValueType)
  body : List Instruction
  deriving Inhabited, BEq

structure Module where
  imports : Array Import
  functions : Array Function
  exports : Array Name
  initializers : Array Name
  runtimeOperations : Array RuntimeOp
  deriving Inhabited, BEq

inductive CompileError where
  | unknownVariable (fvarId : FVarId)
  | unknownDeclaration (name : Name)
  | unknownJoinPoint (fvarId : FVarId)
  | arityMismatch (expected actual : Nat)
  | malformed (message : String)
  deriving Inhabited, BEq, Repr

abbrev LocalTypes := List (FVarId × ValueType)
abbrev JoinPoints := List (FVarId × LCNF.FunDecl .impure)

structure Context where
  program : Fir.LeanIR.ImpureProgram
  localTypes : LocalTypes
  joins : JoinPoints := []

def insertLocal (locals : LocalTypes) (fvarId : FVarId) (type : ValueType) : LocalTypes :=
  (fvarId, type) :: locals.filter fun entry => entry.fst.name != fvarId.name

def findLocalType? : LocalTypes → FVarId → Option ValueType
  | [], _ => none
  | (candidate, type) :: rest, fvarId =>
      if candidate.name == fvarId.name then some type else findLocalType? rest fvarId

def findJoinPoint? : JoinPoints → FVarId → Option (LCNF.FunDecl .impure)
  | [], _ => none
  | (candidate, decl) :: rest, fvarId =>
      if candidate.name == fvarId.name then some decl else findJoinPoint? rest fvarId

def addParams (locals : LocalTypes) (params : Array (LCNF.Param .impure)) : LocalTypes :=
  params.foldl (init := locals) fun locals param =>
    insertLocal locals param.fvarId (valueType param.type)

partial def collectLocals (locals : LocalTypes) : LCNF.Code .impure → LocalTypes
  | .let decl continuation =>
      collectLocals (insertLocal locals decl.fvarId (valueType decl.type)) continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      let locals := addParams locals decl.params
      collectLocals (collectLocals locals decl.value) continuation
  | .jmp .. | .return .. | .unreach .. => locals
  | .cases cases =>
      cases.alts.foldl (init := locals) fun locals alt =>
        match alt with
        | .ctorAlt _ code => collectLocals locals code
        | .default code => collectLocals locals code
        | .alt _ _ _ h => nomatch h
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation => collectLocals locals continuation

def compileArg (context : Context) : LCNF.Arg .impure → Except CompileError (List Instruction × ValueType)
  | .erased => .ok ([.i32Const 0], .i32)
  | .fvar fvarId =>
      match findLocalType? context.localTypes fvarId with
      | some type => .ok ([.localGet fvarId], type)
      | none => .error (.unknownVariable fvarId)
  | .type _ h => nomatch h

def compileArgs (context : Context) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction × Array ValueType) := do
  args.foldlM (init := ([], #[])) fun (instructions, types) arg => do
    let (argument, type) ← compileArg context arg
    return (instructions ++ argument, types.push type)

def getLocal (context : Context) (fvarId : FVarId) : Except CompileError (Instruction × ValueType) :=
  match findLocalType? context.localTypes fvarId with
  | some type => .ok (.localGet fvarId, type)
  | none => .error (.unknownVariable fvarId)

def compileLiteral : LCNF.LitValue → List Instruction
  | .uint8 value => [.i32Const (UInt32.ofNat value.toNat)]
  | .uint16 value => [.i32Const (UInt32.ofNat value.toNat)]
  | .uint32 value => [.i32Const value]
  | .uint64 value => [.i64Const value]
  | .usize value => [.i64Const value]
  | value@(.nat _) | value@(.str _) => [.call (.runtime (.literal value))]

def compileLetValue (context : Context) (decl : LCNF.LetDecl .impure) :
    Except CompileError (List Instruction) := do
  match decl.value with
  | .lit literal => return compileLiteral literal
  | .erased => return [.i32Const 0]
  | .proj _ _ _ h => nomatch h
  | .const _ _ _ h => nomatch h
  | .fvar fvarId args =>
      let (function, _) ← getLocal context fvarId
      let (arguments, types) ← compileArgs context args
      return function :: arguments ++
        [.call (.runtime (.closureApply types (resultTypes decl.type)))]
  | .ctor info args =>
      let (arguments, types) ← compileArgs context args
      return arguments ++ [.call (.runtime (.allocCtor info types))]
  | .oproj index fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.objectProj index))]
  | .uproj index fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.usizeProj index))]
  | .sproj width offset fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.scalarProj width offset (valueType decl.type)))]
  | .fap name args =>
      let (arguments, _) ← compileArgs context args
      let some _ := context.program.findDecl? name | throw (.unknownDeclaration name)
      return arguments ++ [.call (.declaration name)]
  | .pap name args =>
      let (arguments, types) ← compileArgs context args
      let some target := context.program.findDecl? name | throw (.unknownDeclaration name)
      if args.size >= target.params.size then
        throw (.malformed s!"partial application {name} fixes too many parameters")
      return arguments ++ [
        .call (.runtime (.partialApply name target.params.size args.size types))]
  | .reset count fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.reset count))]
  | .reuse fvarId info updateHeader args =>
      let (token, _) ← getLocal context fvarId
      let (arguments, types) ← compileArgs context args
      return token :: arguments ++ [.call (.runtime (.reuse info updateHeader types))]
  | .box type fvarId =>
      let (scalar, scalarType) ← getLocal context fvarId
      if valueType type != scalarType then
        throw (.malformed "box operand type does not match its annotation")
      return [scalar, .call (.runtime (.box scalarType))]
  | .unbox fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.unbox (valueType decl.type)))]
  | .isShared fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime .isShared)]

def compileJump (context : Context) (fvarId : FVarId) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction) := do
  let some decl := findJoinPoint? context.joins fvarId | throw (.unknownJoinPoint fvarId)
  if args.size != decl.params.size then
    throw (.arityMismatch decl.params.size args.size)
  let (arguments, _) ← compileArgs context args
  let assignments := decl.params.toList.reverse.map fun param => .localSet param.fvarId
  return arguments ++ assignments ++ [.br fvarId]

mutual

partial def compileCaseChain (context : Context) (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) :
    Except CompileError (List Instruction) := do
  match alts with
  | [] => return fallback
  | .default _ :: rest => compileCaseChain context discr rest fallback
  | .alt _ _ _ h :: _ => nomatch h
  | .ctorAlt info code :: rest =>
      let thenBody ← compileCode context code
      let elseBody ← compileCaseChain context discr rest fallback
      return [
        .localGet discr,
        .call (.runtime .getTag),
        .i32Const (UInt32.ofNat info.cidx),
        .i32Eq,
        .ifElse thenBody elseBody]

partial def compileCode (context : Context) : LCNF.Code .impure → Except CompileError (List Instruction)
  | .let decl continuation => do
      let value ← compileLetValue context decl
      let rest ← compileCode context continuation
      return value ++ [.localSet decl.fvarId] ++ rest
  | .fun _ _ h => nomatch h
  | .jp decl continuation => do
      let context := { context with joins := (decl.fvarId, decl) :: context.joins }
      let entry ← compileCode context continuation
      let body ← compileCode context decl.value
      return [.block decl.fvarId entry] ++ body
  | .jmp fvarId args => compileJump context fvarId args
  | .cases cases => do
      let fallback ←
        match cases.alts.toList.find? fun alt =>
          match alt with | .default _ => true | _ => false with
        | some (.default code) => compileCode context code
        | some (.alt _ _ _ h) => nomatch h
        | some (.ctorAlt _ _) | none => pure [.unreachable]
      compileCaseChain context cases.discr cases.alts.toList fallback
  | .return fvarId => do
      let (value, _) ← getLocal context fvarId
      return [value, .ret]
  | .unreach _ => return [.unreachable]
  | .oset fvarId index arg continuation => do
      let (object, _) ← getLocal context fvarId
      let (field, fieldType) ← compileArg context arg
      let rest ← compileCode context continuation
      return object :: field ++ [.call (.runtime (.objectSet index fieldType))] ++ rest
  | .uset fvarId index fieldId continuation => do
      let (object, _) ← getLocal context fvarId
      let (field, _) ← getLocal context fieldId
      let rest ← compileCode context continuation
      return [object, field, .call (.runtime (.usizeSet index))] ++ rest
  | .sset fvarId width offset fieldId _ continuation => do
      let (object, _) ← getLocal context fvarId
      let (field, fieldType) ← getLocal context fieldId
      let rest ← compileCode context continuation
      return [object, field, .call (.runtime (.scalarSet width offset fieldType))] ++ rest
  | .setTag fvarId tag continuation => do
      let (object, _) ← getLocal context fvarId
      let rest ← compileCode context continuation
      return [object, .call (.runtime (.setTag tag))] ++ rest
  | .inc fvarId amount check persistent continuation => do
      let rest ← compileCode context continuation
      if persistent then return rest
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.inc amount check))] ++ rest
  | .dec fvarId amount check persistent objectFields? continuation => do
      let rest ← compileCode context continuation
      if persistent then return rest
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.dec amount check objectFields?))] ++ rest
  | .del fvarId continuation => do
      let (object, _) ← getLocal context fvarId
      let rest ← compileCode context continuation
      return [object, .call (.runtime .delete)] ++ rest

end

def addUnique [BEq α] (values : Array α) (value : α) : Array α :=
  if values.contains value then values else values.push value

partial def collectRuntimeOpsInstruction (operations : Array RuntimeOp) : Instruction → Array RuntimeOp
  | .call (.runtime operation) => addUnique operations operation
  | .block _ body => body.foldl collectRuntimeOpsInstruction operations
  | .ifElse thenBody elseBody =>
      elseBody.foldl collectRuntimeOpsInstruction
        (thenBody.foldl collectRuntimeOpsInstruction operations)
  | _ => operations

def collectRuntimeOps (functions : Array Function) : Array RuntimeOp :=
  functions.foldl (init := #[]) fun operations function =>
    function.body.foldl collectRuntimeOpsInstruction operations

def lowerDecl (program : Fir.LeanIR.ImpureProgram) (decl : LCNF.Decl .impure) :
    Except CompileError (Option Function) := do
  match decl.value with
  | .extern _ => return none
  | .code code =>
      let paramLocals := addParams [] decl.params
      let allLocals := collectLocals paramLocals code
      let context : Context := { program, localTypes := allLocals }
      let body ← compileCode context code
      let isParam (fvarId : FVarId) := decl.params.any (·.fvarId.name == fvarId.name)
      let locals := allLocals.reverse.filter fun entry => !isParam entry.fst
      return some {
        name := decl.name
        params := decl.params.map fun param => (param.fvarId, valueType param.type)
        results := resultTypes decl.type
        locals := locals.toArray
        body }

def lower (program : Fir.LeanIR.ImpureProgram) : Except CompileError Module := do
  let functions ← program.decls.filterMapM (lowerDecl program)
  let operations := collectRuntimeOps functions
  let runtimeImports := operations.mapIdx runtimeImport
  let externalImports := program.decls.filterMap fun decl =>
    match decl.value with
    | .extern _ => some (externalImport decl)
    | .code _ => none
  let exports := functions.map (·.name)
  let initializers := program.decls.filterMap fun decl =>
    if decl.params.isEmpty then some decl.name else none
  return {
    imports := runtimeImports ++ externalImports
    functions
    exports
    initializers
    runtimeOperations := operations }

end Fir.Wasm
