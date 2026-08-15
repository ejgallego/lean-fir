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
  | .f32Const value => return .f32Const value
  | .f64Const value => return .f64Const value
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
  | .i32Eqz => return .eqz
  | .i32Eq => return .eq
  | .i32Ne => return .ne
  | .i32LtS => return .ltS
  | .i32LtU => return .ltU
  | .i32GtS => return .gtS
  | .i32GtU => return .gtU
  | .i32LeS => return .leS
  | .i32LeU => return .leU
  | .i32GeS => return .geS
  | .i32GeU => return .geU
  | .i32Clz => return .clz
  | .i32Ctz => return .ctz
  | .i32Popcnt => return .popcnt
  | .i32Add => return .add
  | .i32Sub => return .sub
  | .i32Mul => return .mul
  | .i32DivS => return .divS
  | .i32DivU => return .divU
  | .i32RemS => return .remS
  | .i32RemU => return .remU
  | .i32And => return .and
  | .i32Or => return .or
  | .i32Xor => return .xor
  | .i32Shl => return .shl
  | .i32ShrS => return .shrS
  | .i32ShrU => return .shrU
  | .i32Rotl => return .rotl
  | .i32Rotr => return .rotr
  | .i64Eqz => return .eqzI64
  | .i64Eq => return .eqI64
  | .i64Ne => return .neI64
  | .i64LtS => return .ltSI64
  | .i64LtU => return .ltUI64
  | .i64GtS => return .gtSI64
  | .i64GtU => return .gtUI64
  | .i64LeS => return .leSI64
  | .i64LeU => return .leUI64
  | .i64GeS => return .geSI64
  | .i64GeU => return .geUI64
  | .i64Clz => return .clzI64
  | .i64Ctz => return .ctzI64
  | .i64Popcnt => return .popcntI64
  | .i64Add => return .addI64
  | .i64Sub => return .subI64
  | .i64Mul => return .mulI64
  | .i64DivS => return .divSI64
  | .i64DivU => return .divUI64
  | .i64RemS => return .remSI64
  | .i64RemU => return .remUI64
  | .i64And => return .andI64
  | .i64Or => return .orI64
  | .i64Xor => return .xorI64
  | .i64Shl => return .shlI64
  | .i64ShrS => return .shrSI64
  | .i64ShrU => return .shrUI64
  | .i64Rotl => return .rotlI64
  | .i64Rotr => return .rotrI64
  | .f32Eq => return .f32Eq
  | .f32Ne => return .f32Ne
  | .f32Lt => return .f32Lt
  | .f32Gt => return .f32Gt
  | .f32Le => return .f32Le
  | .f32Ge => return .f32Ge
  | .f32Abs => return .f32Abs
  | .f32Neg => return .f32Neg
  | .f32Ceil => return .f32Ceil
  | .f32Floor => return .f32Floor
  | .f32Trunc => return .f32Trunc
  | .f32Nearest => return .f32Nearest
  | .f32Sqrt => return .f32Sqrt
  | .f32Add => return .f32Add
  | .f32Sub => return .f32Sub
  | .f32Mul => return .f32Mul
  | .f32Div => return .f32Div
  | .f32Min => return .f32Min
  | .f32Max => return .f32Max
  | .f32Copysign => return .f32Copysign
  | .f64Eq => return .f64Eq
  | .f64Ne => return .f64Ne
  | .f64Lt => return .f64Lt
  | .f64Gt => return .f64Gt
  | .f64Le => return .f64Le
  | .f64Ge => return .f64Ge
  | .f64Abs => return .f64Abs
  | .f64Neg => return .f64Neg
  | .f64Ceil => return .f64Ceil
  | .f64Floor => return .f64Floor
  | .f64Trunc => return .f64Trunc
  | .f64Nearest => return .f64Nearest
  | .f64Sqrt => return .f64Sqrt
  | .f64Add => return .f64Add
  | .f64Sub => return .f64Sub
  | .f64Mul => return .f64Mul
  | .f64Div => return .f64Div
  | .f64Min => return .f64Min
  | .f64Max => return .f64Max
  | .f64Copysign => return .f64Copysign
  | .i32Load _ offset => return .load32 offset
  | .i32Load8S _ offset => return .load8S offset
  | .i32Load8U _ offset => return .load8U offset
  | .i32Load16S _ offset => return .load16S offset
  | .i32Load16U _ offset => return .load16U offset
  | .i64Load _ offset => return .load64 offset
  | .i64Load8S _ offset => return .load8SI64 offset
  | .i64Load8U _ offset => return .load8UI64 offset
  | .i64Load16S _ offset => return .load16SI64 offset
  | .i64Load16U _ offset => return .load16UI64 offset
  | .i64Load32S _ offset => return .load32SI64 offset
  | .i64Load32U _ offset => return .load32UI64 offset
  | .f32Load offset => return .f32Load offset
  | .f64Load offset => return .f64Load offset
  | .i32Store8 _ offset => return .store8 offset
  | .i32Store16 _ offset => return .store16 offset
  | .i32Store _ offset => return .store32 offset
  | .i64Store _ offset => return .store64 offset
  | .i64Store8 _ offset => return .store8I64 offset
  | .i64Store16 _ offset => return .store16I64 offset
  | .i64Store32 _ offset => return .store32I64 offset
  | .f32Store offset => return .f32Store offset
  | .f64Store offset => return .f64Store offset
  | .memorySize => return .memorySize
  | .memoryGrow => return .memoryGrow
  | .i32WrapI64 _ => return .wrapI64
  | .i64ExtendI32S _ => return .extendSI32
  | .i64ExtendI32U _ => return .extendUI32
  | .i32Extend8S _ => return .extend8S
  | .i32Extend16S _ => return .extend16S
  | .i64Extend8S _ => return .extend8SI64
  | .i64Extend16S _ => return .extend16SI64
  | .i64Extend32S _ => return .extend32SI64
  | .f32ConvertI32S => return .f32ConvertI32S
  | .f32ConvertI32U => return .f32ConvertI32U
  | .f32ConvertI64S => return .f32ConvertI64S
  | .f32ConvertI64U => return .f32ConvertI64U
  | .f64ConvertI32S => return .f64ConvertI32S
  | .f64ConvertI32U => return .f64ConvertI32U
  | .f64ConvertI64S => return .f64ConvertI64S
  | .f64ConvertI64U => return .f64ConvertI64U
  | .i32TruncF32S _ => return .i32TruncF32S
  | .i32TruncF32U _ => return .i32TruncF32U
  | .i32TruncF64S _ => return .i32TruncF64S
  | .i32TruncF64U _ => return .i32TruncF64U
  | .i64TruncF32S _ => return .i64TruncF32S
  | .i64TruncF32U _ => return .i64TruncF32U
  | .i64TruncF64S _ => return .i64TruncF64S
  | .i64TruncF64U _ => return .i64TruncF64U
  | .i32TruncSatF32S _ => return .i32TruncSatF32S
  | .i32TruncSatF32U _ => return .i32TruncSatF32U
  | .i32TruncSatF64S _ => return .i32TruncSatF64S
  | .i32TruncSatF64U _ => return .i32TruncSatF64U
  | .i64TruncSatF32S _ => return .i64TruncSatF32S
  | .i64TruncSatF32U _ => return .i64TruncSatF32U
  | .i64TruncSatF64S _ => return .i64TruncSatF64S
  | .i64TruncSatF64U _ => return .i64TruncSatF64U
  | .f32DemoteF64 => return .f32DemoteF64
  | .f64PromoteF32 => return .f64PromoteF32
  | .i32ReinterpretF32 _ => return .i32ReinterpretF32
  | .i64ReinterpretF64 _ => return .i64ReinterpretF64
  | .f32ReinterpretI32 _ => return .f32ReinterpretI32
  | .f64ReinterpretI64 _ => return .f64ReinterpretI64
  | .block label body => do
      return .block 0 0 (← instructions module function (label :: labels) body)
  | .loop label body => do
      return .loop 0 0 (← instructions module function (label :: labels) body)
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

def globalValue : Fir.Wasm.GlobalInit → Wasm.Value
  | .i32 value => .i32 value
  | .i64 value => .i64 value
  | .f32 bits => .f32 bits
  | .f64 bits => .f64 bits

/-- Exact physical global order shared by adaptation and its layout theorem. -/
def globalDecls (source : Fir.Wasm.Module) : List Wasm.GlobalDecl :=
  source.cacheGlobalKinds.toList.map (fun kind => { init := zeroValue kind }) ++
    source.globals.toList.map (fun global => { init := globalValue global.init })

/-- Physical validator marker added after a structured function body that has
no fallthrough but does not already end in an explicit terminal instruction. -/
def functionTerminal (module : Fir.Wasm.Module)
    (source : Fir.Wasm.Function) : Wasm.Program :=
  let context : Fir.Wasm.CheckContext := {
    module
    function := source
    locals := (source.params ++ source.locals).toList }
  match Fir.Wasm.checkInstructions context (some []) source.body with
  | .ok flow =>
      if flow.fallthrough.isNone then
        match source.body.getLast? with
        | some .ret | some .unreachable | some (.br _) => []
        | _ => [.unreachable]
      else
        []
  | .error _ => []

def function (module : Fir.Wasm.Module) (source : Fir.Wasm.Function) :
    Except AdapterError Wasm.Function := do
  return {
    params := source.params.toList.map fun entry => abiKind entry.snd
    locals := source.locals.toList.map fun entry => abiKind entry.snd
    results := source.results.toList.map abiKind
    -- Match the binary encoder's explicit terminal for a zero-result
    -- structured construct whose branches cannot fall through. Talos's full
    -- Wasm stack checker needs the same polymorphic-stack marker that the
    -- encoded artifact already carries.
    body := (← instructions module source [] source.body) ++
      functionTerminal module source }

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
    memory := source.memory.map fun memory =>
      { pagesMin := memory.pagesMin, pagesMax := memory.pagesMax }
    memoryExports := source.memory.toList.filterMap fun memory =>
      memory.exportName.map fun name => (name, 0)
    globals := globalDecls source }
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
