import Fir.Wasm.Validate
import Interpreter.Wasm.Validate

namespace FirTalos

open Lean

inductive AdapterError where
  | invalidModule (error : Fir.Wasm.SymbolicError)
  | targetValidation (message : String)
  | unknownLocal (fvarId : FVarId)
  | unknownLabel (fvarId : FVarId)
  | unknownCallTarget
  deriving Inhabited, BEq, Repr

inductive FunctionOrigin where
  | import (key : Fir.Wasm.ImportKey)
  | definition (name : Name)
  deriving Inhabited, BEq

structure SourceMap where
  functionOrigins : Array FunctionOrigin
  deriving Inhabited, BEq

def SourceMap.origin? (sourceMap : SourceMap) (index : Nat) : Option FunctionOrigin :=
  sourceMap.functionOrigins[index]?

structure AdaptedModule where
  wasmModule : Wasm.Module
  sourceMap : SourceMap

def valueType : Fir.Wasm.ValueType → Wasm.ValueType
  | .i32 => .i32
  | .i64 => .i64
  | .f32 => .f32
  | .f64 => .f64

def abiKind (kind : Fir.Wasm.AbiKind) : Wasm.ValueType :=
  valueType kind.valueType

def findFVar? : List (FVarId × α) → FVarId → Option Nat
  | [], _ => none
  | (candidate, _) :: rest, fvarId =>
      if candidate.name == fvarId.name then some 0 else (findFVar? rest fvarId).map (· + 1)

def findLabel? : List FVarId → FVarId → Option Nat
  | [], _ => none
  | candidate :: rest, fvarId =>
      if candidate.name == fvarId.name then some 0 else (findLabel? rest fvarId).map (· + 1)

def findImportTarget? (module : Fir.Wasm.Module) (target : Fir.Wasm.CallTarget) : Option Nat :=
  module.imports.findIdx? fun sourceImport =>
    match target with
    | .runtime operation => sourceImport.operation? == some operation
    | .declaration name => sourceImport.declaration? == some name

def findFunctionTarget? (module : Fir.Wasm.Module) (name : Name) : Option Nat :=
  (module.functions.findIdx? (·.name == name)).map (module.imports.size + ·)

def callIndex? (module : Fir.Wasm.Module) : Fir.Wasm.CallTarget → Option Nat
  | target@(.runtime _) => findImportTarget? module target
  | target@(.declaration name) =>
      findImportTarget? module target <|> findFunctionTarget? module name

mutual

def instruction (module : Fir.Wasm.Module) (function : Fir.Wasm.Function)
    (labels : List FVarId) : Fir.Wasm.Instruction → Except AdapterError Wasm.Instruction
  | .i32Const _ value => return .const value
  | .i64Const _ value => return .constI64 value
  | .localGet fvarId => do
      let locals := function.params.toList ++ function.locals.toList
      let some index := findFVar? locals fvarId | throw (.unknownLocal fvarId)
      return .localGet index
  | .localGetObject fvarId => do
      let locals := function.params.toList ++ function.locals.toList
      let some index := findFVar? locals fvarId | throw (.unknownLocal fvarId)
      return .localGet index
  | .localSet fvarId => do
      let locals := function.params.toList ++ function.locals.toList
      let some index := findFVar? locals fvarId | throw (.unknownLocal fvarId)
      return .localSet index
  | .globalGet index _ => return .globalGet index
  | .globalSet index _ => return .globalSet index
  | .call target => do
      let some index := callIndex? module target | throw .unknownCallTarget
      return .call index
  | .i32Eq => return .eq
  | .block label body => do
      return .block 0 0 (← instructions module function (label :: labels) body)
  | .ifElse thenBody elseBody => do
      return .iff 0 0
        (← instructions module function labels thenBody)
        (← instructions module function labels elseBody)
  | .br label => do
      let some index := findLabel? labels label | throw (.unknownLabel label)
      return .br index
  | .ret => return .ret
  | .unreachable => return .unreachable

termination_by source => sizeOf source

def instructions (module : Fir.Wasm.Module) (function : Fir.Wasm.Function)
    (labels : List FVarId) (body : List Fir.Wasm.Instruction) :
    Except AdapterError (List Wasm.Instruction) := do
  match body with
  | [] => return []
  | source :: rest =>
      return (← instruction module function labels source) ::
        (← instructions module function labels rest)

termination_by sizeOf body

end

def importDecl (sourceImport : Fir.Wasm.Import) : Wasm.ImportDecl :=
  { module := sourceImport.moduleName
    name := sourceImport.itemName
    params := sourceImport.signature.params.toList.map abiKind
    results := sourceImport.signature.results.toList.map abiKind }

def zeroValue (kind : Fir.Wasm.AbiKind) : Wasm.Value :=
  match abiKind kind with
  | .i32 => .i32 0
  | .i64 => .i64 0
  | .f32 => .f32 0
  | .f64 => .f64 0
  | _ => .i32 0

def function (module : Fir.Wasm.Module) (source : Fir.Wasm.Function) :
    Except AdapterError Wasm.Function := do
  return {
    params := source.params.toList.map fun entry => abiKind entry.snd
    locals := source.locals.toList.map fun entry => abiKind entry.snd
    results := source.results.toList.map abiKind
    body := ← instructions module source [] source.body }

def adapt (source : Fir.Wasm.Module) : Except AdapterError AdaptedModule := do
  match Fir.Wasm.validateModule source with
  | .ok _ => pure ()
  | .error error => throw (.invalidModule error)
  let functions ← source.functions.toList.mapM (function source)
  let exports := source.exports.toList.filterMap fun name =>
    (source.functions.findIdx? (·.name == name)).map fun index =>
      { name := name.toString, funcIdx := source.imports.size + index : Wasm.Export }
  let wasmModule : Wasm.Module := {
    funcs := functions
    imports := source.imports.toList.map importDecl
    exports
    globals := source.cacheGlobalKinds.toList.map fun kind =>
      { init := zeroValue kind } }
  match wasmModule.validate with
  | .ok _ => pure ()
  | .error message => throw (.targetValidation message)
  return {
    wasmModule
    sourceMap := {
      functionOrigins :=
        source.imports.map (FunctionOrigin.import ·.key) ++
        source.functions.map (FunctionOrigin.definition ·.name) } }

def module (source : Fir.Wasm.Module) : Except AdapterError Wasm.Module :=
  (adapt source).map (·.wasmModule)

end FirTalos
