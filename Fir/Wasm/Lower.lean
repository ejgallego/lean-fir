import Fir.Wasm.ABI

namespace Fir.Wasm

open Lean
open Lean.Compiler

inductive CallTarget where
  | declaration (name : Name)
  | runtime (operation : RuntimeOp)
  deriving Inhabited, BEq

inductive Instruction where
  | i32Const (kind : AbiKind) (value : UInt32)
  | i64Const (kind : AbiKind) (value : UInt64)
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
  params : Array (FVarId × AbiKind)
  results : Array AbiKind
  locals : Array (FVarId × AbiKind)
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
  | abi (error : AbiError)
  | unknownVariable (fvarId : FVarId)
  | unknownDeclaration (name : Name)
  | unknownJoinPoint (fvarId : FVarId)
  | arityMismatch (expected actual : Nat)
  | malformed (message : String)
  deriving Inhabited, BEq, Repr

abbrev LocalKinds := List (FVarId × AbiKind)
abbrev JoinPoints := List (FVarId × LCNF.FunDecl .impure)

structure Context where
  program : Fir.LeanIR.ImpureProgram
  localKinds : LocalKinds
  joins : JoinPoints := []

def insertLocal (locals : LocalKinds) (fvarId : FVarId) (kind : AbiKind) : LocalKinds :=
  (fvarId, kind) :: locals.filter fun entry => entry.fst.name != fvarId.name

def findLocalKind? : LocalKinds → FVarId → Option AbiKind
  | [], _ => none
  | (candidate, kind) :: rest, fvarId =>
      if candidate.name == fvarId.name then some kind else findLocalKind? rest fvarId

def findJoinPoint? : JoinPoints → FVarId → Option (LCNF.FunDecl .impure)
  | [], _ => none
  | (candidate, decl) :: rest, fvarId =>
      if candidate.name == fvarId.name then some decl else findJoinPoint? rest fvarId

def checkedAbiKind? (type : Expr) : Except CompileError (Option AbiKind) :=
  match abiKind? type with
  | .ok kind? => pure kind?
  | .error error => throw (.abi error)

def checkedAbiKind (type : Expr) : Except CompileError AbiKind :=
  match abiKind type with
  | .ok kind => pure kind
  | .error error => throw (.abi error)

def letValueKind (decl : LCNF.LetDecl .impure) : Except CompileError AbiKind :=
  match decl.value with
  | .erased => pure .erased
  | .reset .. => pure .reuseToken
  | _ => checkedAbiKind decl.type

def addParams (locals : LocalKinds) (params : Array (LCNF.Param .impure)) :
    Except CompileError LocalKinds := do
  params.foldlM (init := locals) fun locals param => do
    match ← checkedAbiKind? param.type with
    | some kind => return insertLocal locals param.fvarId kind
    | none => return locals

partial def collectLocals (locals : LocalKinds) :
    LCNF.Code .impure → Except CompileError LocalKinds
  | .let decl continuation => do
      let kind ← letValueKind decl
      collectLocals (insertLocal locals decl.fvarId kind) continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation => do
      let locals ← addParams locals decl.params
      let locals ← collectLocals locals decl.value
      collectLocals locals continuation
  | .jmp .. | .return .. | .unreach .. => pure locals
  | .cases cases => do
      cases.alts.foldlM (init := locals) fun locals alt =>
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

def compileArg (context : Context) :
    LCNF.Arg .impure → Except CompileError (List Instruction × AbiKind)
  | .erased => .ok ([.i32Const .erased 0], .erased)
  | .fvar fvarId =>
      match findLocalKind? context.localKinds fvarId with
      | some kind => .ok ([.localGet fvarId], kind)
      | none => .error (.unknownVariable fvarId)
  | .type _ h => nomatch h

def compileArgs (context : Context) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction × Array AbiKind) := do
  args.foldlM (init := ([], #[])) fun (instructions, kinds) arg => do
    let (argument, kind) ← compileArg context arg
    return (instructions ++ argument, kinds.push kind)

def getLocal (context : Context) (fvarId : FVarId) :
    Except CompileError (Instruction × AbiKind) :=
  match findLocalKind? context.localKinds fvarId with
  | some kind => .ok (.localGet fvarId, kind)
  | none => .error (.unknownVariable fvarId)

def compileLiteral (result : AbiKind) : LCNF.LitValue → List Instruction
  | .uint8 value => [.i32Const .uint8 (UInt32.ofNat value.toNat)]
  | .uint16 value => [.i32Const .uint16 (UInt32.ofNat value.toNat)]
  | .uint32 value => [.i32Const .uint32 value]
  | .uint64 value => [.i64Const .uint64 value]
  | .usize value => [.i64Const .usize value]
  | value@(.nat _) | value@(.str _) => [.call (.runtime (.literal value result))]

def compileLetValue (context : Context) (decl : LCNF.LetDecl .impure) :
    Except CompileError (List Instruction) := do
  let resultKind ← letValueKind decl
  match decl.value with
  | .lit literal =>
      unless resultKind.acceptsLiteral literal do
        throw (.malformed "literal kind does not match its declaration")
      return compileLiteral resultKind literal
  | .erased => return [.i32Const .erased 0]
  | .proj _ _ _ h => nomatch h
  | .const _ _ _ h => nomatch h
  | .fvar fvarId args =>
      let (function, _) ← getLocal context fvarId
      let (arguments, kinds) ← compileArgs context args
      return function :: arguments ++
        [.call (.runtime (.closureApply kinds #[resultKind]))]
  | .ctor info args =>
      unless constructorTagFitsI32 info do
        throw (.malformed s!"allocated constructor tag {info.cidx} does not fit the i32 tag ABI")
      let (arguments, kinds) ← compileArgs context args
      return arguments ++ [.call (.runtime (.allocCtor info kinds resultKind))]
  | .oproj index fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.objectProj index resultKind))]
  | .uproj index fvarId =>
      let (object, _) ← getLocal context fvarId
      unless resultKind == .usize do
        throw (.malformed "usize projection must produce USize")
      return [object, .call (.runtime (.usizeProj index))]
  | .sproj width offset fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.scalarProj width offset resultKind))]
  | .fap name args =>
      let (arguments, _) ← compileArgs context args
      let some _ := context.program.findDecl? name | throw (.unknownDeclaration name)
      return arguments ++ [.call (.declaration name)]
  | .pap name args =>
      let (arguments, kinds) ← compileArgs context args
      let some target := context.program.findDecl? name | throw (.unknownDeclaration name)
      if args.size >= target.params.size then
        throw (.malformed s!"partial application {name} fixes too many parameters")
      return arguments ++ [
        .call (.runtime (.partialApply name target.params.size args.size kinds resultKind))]
  | .reset count fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.reset count))]
  | .reuse fvarId info updateHeader args =>
      let (token, _) ← getLocal context fvarId
      let (arguments, kinds) ← compileArgs context args
      return token :: arguments ++
        [.call (.runtime (.reuse info updateHeader kinds resultKind))]
  | .box type fvarId =>
      let (scalar, scalarKind) ← getLocal context fvarId
      let annotationKind ← checkedAbiKind type
      if annotationKind != scalarKind then
        throw (.malformed "box operand type does not match its annotation")
      return [scalar, .call (.runtime (.box scalarKind resultKind))]
  | .unbox fvarId =>
      let (object, _) ← getLocal context fvarId
      return [object, .call (.runtime (.unbox resultKind))]
  | .isShared fvarId =>
      let (object, _) ← getLocal context fvarId
      unless resultKind == .uint8 do
        throw (.malformed "isShared must produce UInt8")
      return [object, .call (.runtime .isShared)]

def compileJump (context : Context) (fvarId : FVarId) (args : Array (LCNF.Arg .impure)) :
    Except CompileError (List Instruction) := do
  let some decl := findJoinPoint? context.joins fvarId | throw (.unknownJoinPoint fvarId)
  if args.size != decl.params.size then
    throw (.arityMismatch decl.params.size args.size)
  let (arguments, _) ← compileArgs context args
  let assignments := decl.params.toList.reverse.map fun param => .localSet param.fvarId
  return arguments ++ assignments ++ [.br fvarId]

def compileCaseChainWithM [Monad m] [MonadExceptOf CompileError m]
    (compile : LCNF.Code .impure → m (List Instruction))
    (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) : m (List Instruction) := do
  match alts with
  | [] => return fallback
  | .default _ :: rest => compileCaseChainWithM compile discr rest fallback
  | .alt _ _ _ h :: _ => nomatch h
  | .ctorAlt info code :: rest =>
      unless constructorTagFitsI32 info do
        throw (.malformed s!"constructor tag {info.cidx} does not fit the i32 case ABI")
      let thenBody ← compile code
      let elseBody ← compileCaseChainWithM compile discr rest fallback
      return [
        .localGet discr,
        .call (.runtime .getTag),
        .i32Const .uint32 (UInt32.ofNat info.cidx),
        .i32Eq,
        .ifElse thenBody elseBody]

termination_by sizeOf alts

def compileCaseChainWith
    (compile : LCNF.Code .impure → Except CompileError (List Instruction))
    (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) :
    Except CompileError (List Instruction) :=
  compileCaseChainWithM compile discr alts fallback

/--
Proof-transparent partiality for the recursive compiler. `Option.none` is the
least element used by `partial_fixpoint`; every finite compiler result observed
through `compileCode` is an `Except` value inside `some`.
-/
abbrev CompileM (α : Type) := ExceptT CompileError Option α

def liftCompileResult {α : Type} (result : Except CompileError α) : CompileM α :=
  some result

open Lean.Order in
@[partial_fixpoint_monotone]
theorem monotone_compileCaseChainWithM
    {γ : Type} [PartialOrder γ]
    (compile : γ → LCNF.Code .impure → CompileM (List Instruction))
    (discr : FVarId) (alts : List (LCNF.Alt .impure)) (fallback : List Instruction)
    (hmono : monotone compile) :
    monotone (fun x => compileCaseChainWithM (compile x) discr alts fallback) := by
  induction alts with
  | nil =>
      simp only [compileCaseChainWithM]
      apply monotone_const
  | cons alt alts ih =>
      cases alt with
      | alt _ _ _ impossible => nomatch impossible
      | default code =>
          simp only [compileCaseChainWithM]
          exact ih
      | ctorAlt info code =>
          simp only [compileCaseChainWithM]
          by_cases fits : constructorTagFitsI32 info = true
          · simp only [fits, ↓reduceIte]
            apply monotone_bind
            · apply monotone_apply
              exact hmono
            · apply monotone_of_monotone_apply
              intro thenBody
              apply monotone_bind
              · exact ih
              · apply monotone_const
          · simp [fits]
            apply monotone_const

def compileCodeCore (context : Context) : LCNF.Code .impure → CompileM (List Instruction)
  | .let decl continuation => do
      let value ← liftCompileResult (compileLetValue context decl)
      let rest ← compileCodeCore context continuation
      return value ++ [.localSet decl.fvarId] ++ rest
  | .fun _ _ h => nomatch h
  | .jp decl continuation => do
      let context := { context with joins := (decl.fvarId, decl) :: context.joins }
      let entry ← compileCodeCore context continuation
      let body ← compileCodeCore context decl.value
      return [.block decl.fvarId entry] ++ body
  | .jmp fvarId args => liftCompileResult (compileJump context fvarId args)
  | .cases cases => do
      let fallback ←
        match cases.alts.toList.find? fun alt =>
          match alt with | .default _ => true | _ => false with
        | some (.default code) => compileCodeCore context code
        | some (.alt _ _ _ h) => nomatch h
        | some (.ctorAlt _ _) | none => pure [.unreachable]
      compileCaseChainWithM (compileCodeCore context) cases.discr cases.alts.toList fallback
  | .return fvarId => do
      let (value, _) ← liftCompileResult (getLocal context fvarId)
      return [value, .ret]
  | .unreach _ => return [.unreachable]
  | .oset fvarId index arg continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let (field, fieldType) ← liftCompileResult (compileArg context arg)
      let rest ← compileCodeCore context continuation
      return object :: field ++ [.call (.runtime (.objectSet index fieldType))] ++ rest
  | .uset fvarId index fieldId continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let (field, _) ← liftCompileResult (getLocal context fieldId)
      let rest ← compileCodeCore context continuation
      return [object, field, .call (.runtime (.usizeSet index))] ++ rest
  | .sset fvarId width offset fieldId _ continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let (field, fieldType) ← liftCompileResult (getLocal context fieldId)
      let rest ← compileCodeCore context continuation
      return [object, field, .call (.runtime (.scalarSet width offset fieldType))] ++ rest
  | .setTag fvarId tag continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let rest ← compileCodeCore context continuation
      return [object, .call (.runtime (.setTag tag))] ++ rest
  | .inc fvarId amount check persistent continuation => do
      let rest ← compileCodeCore context continuation
      if persistent then return rest
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      return [object, .call (.runtime (.inc amount check))] ++ rest
  | .dec fvarId amount check persistent objectFields? continuation => do
      let rest ← compileCodeCore context continuation
      if persistent then return rest
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      return [object, .call (.runtime (.dec amount check objectFields?))] ++ rest
  | .del fvarId continuation => do
      let (object, _) ← liftCompileResult (getLocal context fvarId)
      let rest ← compileCodeCore context continuation
      return [object, .call (.runtime .delete)] ++ rest
partial_fixpoint

def finishCompileResult {α : Type} (result : CompileM α) : Except CompileError α :=
  result.getD (.error (.malformed "recursive compiler produced no result"))

def compileCode (context : Context) (code : LCNF.Code .impure) :
    Except CompileError (List Instruction) :=
  finishCompileResult (compileCodeCore context code)

theorem finishCompileResult_eq_ok_iff {α : Type} {result : CompileM α} {value : α} :
    finishCompileResult result = .ok value ↔ result = some (.ok value) := by
  cases result with
  | none => simp [finishCompileResult]
  | some result =>
      change result = .ok value ↔ some result = some (.ok value)
      exact ⟨congrArg some, Option.some.inj⟩

/-- Transparent one-layer equation for a successfully compiled `let`. -/
theorem compileCode_let
    {context : Context} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure} {valueCode restCode : List Instruction}
    (valueCompiled : compileLetValue context decl = .ok valueCode)
    (restCompiled : compileCode context continuation = .ok restCode) :
    compileCode context (.let decl continuation) =
      .ok (valueCode ++ [.localSet decl.fvarId] ++ restCode) := by
  apply finishCompileResult_eq_ok_iff.mpr
  have restCore : compileCodeCore context continuation = some (.ok restCode) := by
    apply finishCompileResult_eq_ok_iff.mp
    exact restCompiled
  rw [compileCodeCore.eq_def]
  simp only
  rw [valueCompiled, restCore]
  rfl

/-- Transparent successful equation for a source return. -/
theorem compileCode_return
    {context : Context} {fvarId : FVarId} {value : Instruction} {kind : AbiKind}
    (localCompiled : getLocal context fvarId = .ok (value, kind)) :
    compileCode context (.return fvarId) = .ok [value, .ret] := by
  apply finishCompileResult_eq_ok_iff.mpr
  rw [compileCodeCore.eq_def]
  simp only
  rw [localCompiled]
  rfl

/-- Transparent successful equation for source unreachability. -/
@[simp] theorem compileCode_unreach (context : Context) (type : Expr) :
    compileCode context (.unreach type) = .ok [.unreachable] := by
  apply finishCompileResult_eq_ok_iff.mpr
  rw [compileCodeCore.eq_def]
  rfl

def compileCaseChain (context : Context) (discr : FVarId)
    (alts : List (LCNF.Alt .impure)) (fallback : List Instruction) :
    Except CompileError (List Instruction) :=
  compileCaseChainWith (compileCode context) discr alts fallback

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
      let paramLocals ← addParams [] decl.params
      let allLocals ← collectLocals paramLocals code
      let context : Context := { program, localKinds := allLocals }
      let body ← compileCode context code
      let isParam (fvarId : FVarId) := decl.params.any (·.fvarId.name == fvarId.name)
      let locals := allLocals.reverse.filter fun entry => !isParam entry.fst
      let results ←
        match resultKinds decl.type with
        | .ok results => pure results
        | .error error => throw (.abi error)
      return some {
        name := decl.name
        params := paramLocals.reverse.toArray
        results
        locals := locals.toArray
        body }

def lower (program : Fir.LeanIR.ImpureProgram) : Except CompileError Module := do
  let functions ← program.decls.filterMapM (lowerDecl program)
  let operations := collectRuntimeOps functions
  unless operations.all RuntimeOp.abiWellFormed do
    throw (.malformed "generated runtime operation violates the semantic ABI")
  let runtimeImports := operations.mapIdx runtimeImport
  let externalImports ← program.decls.filterMapM fun decl =>
    match decl.value with
    | .extern _ => do
        match externalImport decl with
        | .ok import_ => return some import_
        | .error error => throw (.abi error)
    | .code _ => pure none
  let exports := functions.map (·.name)
  return {
    imports := runtimeImports ++ externalImports
    functions
    exports
    initializers := #[]
    runtimeOperations := operations }

end Fir.Wasm
