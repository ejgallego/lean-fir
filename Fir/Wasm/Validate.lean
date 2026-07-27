import Fir.Wasm.Lower

namespace Fir.Wasm

open Lean

/-!
This is the authoritative checker for the symbolic FIR-to-Wasm subset. It
tracks semantic ABI kinds, not only physical Wasm lanes, and validates code
that has become unreachable so unresolved locals, labels, and calls cannot be
hidden after a terminator. Blocks have no parameters or results in this IR;
their named branches must restore the operand stack present at block entry.
-/

inductive SymbolicError where
  | duplicateFunction (name : Name)
  | duplicateDeclaration (name : Name)
  | duplicateImportKey
  | duplicateImportName (moduleName itemName : String)
  | runtimeOperationOrder
  | duplicateClosureTarget (name : Name)
  | missingClosureTarget (name : Name)
  | duplicateClosureDescriptor (descriptor : Array AbiKind)
  | missingClosureDescriptor (descriptor : Array AbiKind)
  | invalidRuntimeOperation (index : Nat)
  | invalidRuntimeImport (index : Nat)
  | invalidExternalImport (index : Nat)
  | nonExternalImport (index : Nat)
  | unsupportedClosure (index : Nat)
  | duplicateExport (name : Name)
  | unknownExport (name : Name)
  | duplicateLocal (function : Name) (fvarId : FVarId)
  | duplicateLabel (function : Name) (fvarId : FVarId)
  | unknownLocal (function : Name) (fvarId : FVarId)
  | unknownLabel (function : Name) (fvarId : FVarId)
  | unknownGlobal (function : Name) (index : Nat)
  | invalidGlobalKind (function : Name) (index : Nat)
  | unknownCallTarget (function : Name)
  | invalidInitializer (name : Name)
  | invalidGlobalInitializer (index : Nat)
  | invalidConstant (function : Name) (kind : AbiKind) (physical : ValueType)
  | invalidLocalRefinement (function : Name) (fvarId : FVarId) (kind : AbiKind)
  | invalidMemoryLimits
  | memoryInstructionWithoutMemory (function : Name)
  | stackUnderflow (function : Name) (expected : List AbiKind)
  | stackMismatch (function : Name) (expected actual : List AbiKind)
  | branchStackMismatch (function : Name) (label : FVarId)
      (expected actual : List AbiKind)
  | branchMergeMismatch (function : Name) (left right : List AbiKind)
  | escapingBranch (function : Name) (label : FVarId)
  deriving Inhabited, BEq, Repr

def listAllUnique [BEq α] : List α → Bool
  | [] => true
  | value :: rest => !rest.contains value && listAllUnique rest

def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest => if rest.contains value then some value else firstDuplicate? rest

def firstDuplicateFVar? : List FVarId → Option FVarId
  | [] => none
  | fvarId :: rest =>
      if rest.any (·.name == fvarId.name) then some fvarId else firstDuplicateFVar? rest

def RuntimeOp.isClosure : RuntimeOp → Bool
  | .closureApply .. => true
  | _ => false

def Function.signature (function : Function) : Signature :=
  { params := function.params.map (·.snd), results := function.results }

def Module.callSignature? (module : Module) : CallTarget → Option Signature
  | .runtime operation =>
      if module.imports.any (·.key == .runtime operation) then some operation.signature else none
  | .declaration name =>
      match module.imports.find? (·.declaration? == some name) with
      | some import_ => some import_.signature
      | none => (module.functions.find? (·.name == name)).map Function.signature

/-- Physical lazy-cache layout: an i32 initialized flag followed by the
declaration's singleton semantic result. -/
def Module.cacheGlobalKinds (module : Module) : Array AbiKind :=
  module.initializers.foldl (init := #[]) fun kinds name =>
    match module.callSignature? (.declaration name) with
    | some signature =>
        match signature.results[0]? with
        | some result => (kinds.push .uint32).push result
        | none => kinds
    | none => kinds

/--
Physical global order is a shared ABI: lazy-cache flag/value pairs retain
their historical prefix and resident-runtime globals follow in declaration
order.
-/
def Module.globalKinds (module : Module) : Array AbiKind :=
  module.cacheGlobalKinds ++ module.globals.map (·.kind)

def validateOperations : List RuntimeOp → Nat → Except SymbolicError Unit
  | [], _ => pure ()
  | operation :: rest, index => do
      unless operation.abiWellFormed do
        throw (.invalidRuntimeOperation index)
      if operation.isClosure then
        throw (.unsupportedClosure index)
      validateOperations rest (index + 1)

def validateImportPrefix : List Import → List Import → Nat → Except SymbolicError Unit
  | [], actual, index =>
      let rec go : List Import → Nat → Except SymbolicError Unit
        | [], _ => pure ()
        | import_ :: rest, index => do
            match import_.key with
            | .runtime _ => throw (.nonExternalImport index)
            | .external _ =>
                let some types := import_.externalTypes? |
                  throw (.invalidExternalImport index)
                match types.signature with
                | .error _ => throw (.invalidExternalImport index)
                | .ok signature =>
                    unless signature == import_.signature do
                      throw (.invalidExternalImport index)
            go rest (index + 1)
      go actual index
  | _ :: _, [], index => throw (.invalidRuntimeImport index)
  | expected :: expectedRest, actual :: actualRest, index => do
      unless actual == expected do
        throw (.invalidRuntimeImport index)
      validateImportPrefix expectedRest actualRest (index + 1)

def validateModuleShape (module : Module) : Except SymbolicError Unit := do
  let functionNames := module.functions.toList.map (·.name)
  if let some name := firstDuplicate? functionNames then
    throw (.duplicateFunction name)
  if let some name := firstDuplicate? module.closureDispatch.toList then
    throw (.duplicateClosureTarget name)
  if let some descriptor := firstDuplicate? module.closureDescriptors.toList then
    throw (.duplicateClosureDescriptor descriptor)
  for operation in module.runtimeOperations do
    if let some name := operation.closureTarget? then
      unless module.closureDispatch.contains name do
        throw (.missingClosureTarget name)
    if let some descriptor := operation.closureDescriptor? then
      unless module.closureDescriptors.contains descriptor do
        throw (.missingClosureDescriptor descriptor)
  let expectedOperations := collectRuntimeOps module.functions
  unless module.runtimeOperations == expectedOperations do
    throw .runtimeOperationOrder
  validateOperations module.runtimeOperations.toList 0
  let expectedImports := module.runtimeOperations.mapIdx runtimeImport
  validateImportPrefix expectedImports.toList module.imports.toList 0
  unless listAllUnique (module.imports.toList.map (·.key)) do
    throw .duplicateImportKey
  let importNames := module.imports.toList.map fun import_ =>
    (import_.moduleName, import_.itemName)
  if let some (moduleName, itemName) := firstDuplicate? importNames then
    throw (.duplicateImportName moduleName itemName)
  let externalNames := module.imports.toList.filterMap (·.declaration?)
  if let some name := firstDuplicate? (externalNames ++ functionNames) then
    throw (.duplicateDeclaration name)
  if let some name := firstDuplicate? module.exports.toList then
    throw (.duplicateExport name)
  for name in module.exports do
    unless module.functions.any (·.name == name) do
      throw (.unknownExport name)
  if let some memory := module.memory then
    unless memory.pagesMin.toNat ≤ 65536 do
      throw .invalidMemoryLimits
    if let some pagesMax := memory.pagesMax then
      unless memory.pagesMin.toNat ≤ pagesMax.toNat &&
          pagesMax.toNat ≤ 65536 do
        throw .invalidMemoryLimits
    if let some exportName := memory.exportName then
      if module.exports.any (·.toString == exportName) then
        throw (.duplicateExport (Name.mkSimple exportName))
  unless listAllUnique module.initializers.toList do
    throw (.invalidInitializer module.initializers[0]!)
  for initializer in module.initializers do
    let some signature := module.callSignature? (.declaration initializer) |
      throw (.invalidInitializer initializer)
    unless signature.params.isEmpty && signature.results.size == 1 do
      throw (.invalidInitializer initializer)
  for (global, index) in module.globals.toList.zipIdx do
    unless global.kind.valueType == global.init.valueType do
      throw (.invalidGlobalInitializer index)

abbrev OperandStack := List AbiKind

def stackMatches (actual expected : OperandStack) : Bool :=
  actual.length == expected.length &&
    (actual.zip expected).all fun (actual, expected) => actual.refines expected

def stackEquivalent (left right : OperandStack) : Bool :=
  stackMatches left right && stackMatches right left

def popKinds (function : Name) (stack expected : OperandStack) :
    Except SymbolicError OperandStack := do
  if stack.length < expected.length then
    throw (.stackUnderflow function expected)
  let remaining := stack.take (stack.length - expected.length)
  let actual := stack.drop (stack.length - expected.length)
  unless stackMatches actual expected do
    throw (.stackMismatch function expected actual)
  return remaining

structure LabelTarget where
  fvarId : FVarId
  stack? : Option OperandStack

structure CheckContext where
  module : Module
  function : Function
  locals : LocalKinds
  labels : List LabelTarget := []

def CheckContext.findLabel? (context : CheckContext) (fvarId : FVarId) :
    Option LabelTarget :=
  context.labels.find? (·.fvarId.name == fvarId.name)

structure Flow where
  fallthrough : Option OperandStack
  branches : List FVarId := []

def mergeFallthrough (function : Name) (left right : Option OperandStack) :
    Except SymbolicError (Option OperandStack) := do
  match left, right with
  | none, none => return none
  | some stack, none | none, some stack => return some stack
  | some left, some right =>
      unless stackEquivalent left right do
        throw (.branchMergeMismatch function left right)
      return some left

mutual

partial def collectLabelsInstruction : Instruction → List FVarId
  | .block label body => label :: collectLabels body
  | .ifElse thenBody elseBody => collectLabels thenBody ++ collectLabels elseBody
  | _ => []

partial def collectLabels (instructions : List Instruction) : List FVarId :=
  instructions.flatMap collectLabelsInstruction

end

mutual

partial def checkInstruction (context : CheckContext) (stack? : Option OperandStack) :
    Instruction → Except SymbolicError Flow
  | .i32Const kind _ => do
      unless kind.valueType == .i32 do
        throw (.invalidConstant context.function.name kind .i32)
      return { fallthrough := stack?.map (· ++ [kind]) }
  | .i64Const kind _ => do
      unless kind.valueType == .i64 do
        throw (.invalidConstant context.function.name kind .i64)
      return { fallthrough := stack?.map (· ++ [kind]) }
  | .localGet fvarId => do
      let some kind := findLocalKind? context.locals fvarId |
        throw (.unknownLocal context.function.name fvarId)
      return { fallthrough := stack?.map (· ++ [kind]) }
  | .localGetObject fvarId => do
      let some kind := findLocalKind? context.locals fvarId |
        throw (.unknownLocal context.function.name fvarId)
      unless kind == .tobject do
        throw (.invalidLocalRefinement context.function.name fvarId kind)
      return { fallthrough := stack?.map (· ++ [.object]) }
  | .localSet fvarId => do
      let some kind := findLocalKind? context.locals fvarId |
        throw (.unknownLocal context.function.name fvarId)
      let stack? ← stack?.mapM fun stack => popKinds context.function.name stack [kind]
      return { fallthrough := stack? }
  | .globalGet index kind => do
      let some expected := context.module.globalKinds[index]? |
        throw (.unknownGlobal context.function.name index)
      unless kind == expected do
        throw (.invalidGlobalKind context.function.name index)
      return { fallthrough := stack?.map (· ++ [kind]) }
  | .globalSet index kind => do
      let some expected := context.module.globalKinds[index]? |
        throw (.unknownGlobal context.function.name index)
      unless kind == expected do
        throw (.invalidGlobalKind context.function.name index)
      let stack? ← stack?.mapM fun stack => popKinds context.function.name stack [kind]
      return { fallthrough := stack? }
  | .call target => do
      let some signature := context.module.callSignature? target |
        throw (.unknownCallTarget context.function.name)
      let stack? ← stack?.mapM fun stack => do
        let stack ← popKinds context.function.name stack signature.params.toList
        return stack ++ signature.results.toList
      return { fallthrough := stack? }
  | .i32Eq => do
      let stack? ← stack?.mapM fun stack => do
        if stack.length < 2 then
          throw (.stackUnderflow context.function.name [.uint32, .uint32])
        let remaining := stack.take (stack.length - 2)
        let operands := stack.drop (stack.length - 2)
        let some left := operands[0]? |
          throw (.stackUnderflow context.function.name [.uint32, .uint32])
        let some right := operands[1]? |
          throw (.stackUnderflow context.function.name [.uint32, .uint32])
        unless left.valueType == .i32 && right.valueType == .i32 &&
            left.refines right && right.refines left do
          throw (.stackMismatch context.function.name [right, right] operands)
        return remaining ++ [.uint32]
      return { fallthrough := stack? }
  | .i32And | .i32ShrU | .i32Add | .i32Sub | .i32LtU => do
      let stack? ← stack?.mapM fun stack => do
        if stack.length < 2 then
          throw (.stackUnderflow context.function.name [.uint32, .uint32])
        let remaining := stack.take (stack.length - 2)
        let operands := stack.drop (stack.length - 2)
        unless operands.all (·.valueType == .i32) do
          throw (.stackMismatch context.function.name [.uint32, .uint32] operands)
        return remaining ++ [.uint32]
      return { fallthrough := stack? }
  | .i32Store8 value _
  | .i32Store16 value _
  | .i32Store value _ => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      unless value.valueType == .i32 do
        throw (.invalidConstant context.function.name value .i32)
      let stack? ← stack?.mapM fun stack =>
        popKinds context.function.name stack [.uint32, value]
      return { fallthrough := stack? }
  | .i64Store value _ => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      unless value.valueType == .i64 do
        throw (.invalidConstant context.function.name value .i64)
      let stack? ← stack?.mapM fun stack =>
        popKinds context.function.name stack [.uint32, value]
      return { fallthrough := stack? }
  | .memorySize => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      return { fallthrough := stack?.map (· ++ [.uint32]) }
  | .memoryGrow => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      let stack? ← stack?.mapM fun stack => do
        let stack ← popKinds context.function.name stack [.uint32]
        return stack ++ [.uint32]
      return { fallthrough := stack? }
  | .i32Load result _ => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      unless result.valueType == .i32 do
        throw (.invalidConstant context.function.name result .i32)
      let stack? ← stack?.mapM fun stack => do
        if stack.isEmpty then
          throw (.stackUnderflow context.function.name [.uint32])
        let remaining := stack.take (stack.length - 1)
        let some address := stack.getLast? |
          throw (.stackUnderflow context.function.name [.uint32])
        unless address.valueType == .i32 do
          throw (.stackMismatch context.function.name [.uint32] [address])
        return remaining ++ [result]
      return { fallthrough := stack? }
  | .i32Load8U result _
  | .i32Load16U result _ => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      unless result.valueType == .i32 do
        throw (.invalidConstant context.function.name result .i32)
      let stack? ← stack?.mapM fun stack => do
        if stack.isEmpty then
          throw (.stackUnderflow context.function.name [.uint32])
        let remaining := stack.take (stack.length - 1)
        let some address := stack.getLast? |
          throw (.stackUnderflow context.function.name [.uint32])
        unless address.valueType == .i32 do
          throw (.stackMismatch context.function.name [.uint32] [address])
        return remaining ++ [result]
      return { fallthrough := stack? }
  | .i64Load result _ => do
      unless context.module.memory.isSome do
        throw (.memoryInstructionWithoutMemory context.function.name)
      unless result.valueType == .i64 do
        throw (.invalidConstant context.function.name result .i64)
      let stack? ← stack?.mapM fun stack => do
        if stack.isEmpty then
          throw (.stackUnderflow context.function.name [.uint32])
        let remaining := stack.take (stack.length - 1)
        let some address := stack.getLast? |
          throw (.stackUnderflow context.function.name [.uint32])
        unless address.valueType == .i32 do
          throw (.stackMismatch context.function.name [.uint32] [address])
        return remaining ++ [result]
      return { fallthrough := stack? }
  | .i32WrapI64 result => do
      unless result.valueType == .i32 do
        throw (.invalidConstant context.function.name result .i32)
      let stack? ← stack?.mapM fun stack => do
        if stack.isEmpty then
          throw (.stackUnderflow context.function.name [.uint64])
        let remaining := stack.take (stack.length - 1)
        let some operand := stack.getLast? |
          throw (.stackUnderflow context.function.name [.uint64])
        unless operand.valueType == .i64 do
          throw (.stackMismatch context.function.name [.uint64] [operand])
        return remaining ++ [result]
      return { fallthrough := stack? }
  | .block label body => do
      let nested := { context with labels := { fvarId := label, stack? } :: context.labels }
      let flow ← checkInstructions nested stack? body
      let caught := flow.branches.any (·.name == label.name)
      let branches := flow.branches.filter (·.name != label.name)
      let normal ←
        match stack?, flow.fallthrough with
        | some expected, some actual =>
            if stackEquivalent actual expected then pure true
            else throw (.stackMismatch context.function.name expected actual)
        | none, some actual => throw (.stackMismatch context.function.name [] actual)
        | _, none => pure false
      let fallthrough := if normal || caught then stack? else none
      return { fallthrough, branches }
  | .ifElse thenBody elseBody => do
      let branchInput ← stack?.mapM fun stack => do
        popKinds context.function.name stack [.uint32]
      let thenFlow ← checkInstructions context branchInput thenBody
      let elseFlow ← checkInstructions context branchInput elseBody
      let fallthrough ← mergeFallthrough context.function.name
        thenFlow.fallthrough elseFlow.fallthrough
      match branchInput, fallthrough with
      | some expected, some actual =>
          unless stackEquivalent actual expected do
            throw (.stackMismatch context.function.name expected actual)
      | none, some actual =>
          throw (.stackMismatch context.function.name [] actual)
      | _, none => pure ()
      return {
        fallthrough
        branches := thenFlow.branches ++ elseFlow.branches }
  | .br label => do
      let some target := context.findLabel? label |
        throw (.unknownLabel context.function.name label)
      match stack?, target.stack? with
      | some actual, some expected =>
          unless stackEquivalent actual expected do
            throw (.branchStackMismatch context.function.name label expected actual)
      | some actual, none =>
          throw (.branchStackMismatch context.function.name label [] actual)
      | none, _ => pure ()
      return { fallthrough := none, branches := if stack?.isSome then [label] else [] }
  | .ret => do
      if let some actual := stack? then
        let expected := context.function.results.toList
        unless stackMatches actual expected do
          throw (.stackMismatch context.function.name expected actual)
      return { fallthrough := none }
  | .unreachable => return { fallthrough := none }

partial def checkInstructions (context : CheckContext) (stack? : Option OperandStack) :
    List Instruction → Except SymbolicError Flow
  | [] => return { fallthrough := stack? }
  | instruction :: rest => do
      let first ← checkInstruction context stack? instruction
      let tail ← checkInstructions context first.fallthrough rest
      return { fallthrough := tail.fallthrough, branches := first.branches ++ tail.branches }

end

def validateFunction (module : Module) (function : Function) : Except SymbolicError Unit := do
  let fvarIds := (function.params ++ function.locals).toList.map (·.fst)
  if let some duplicate := firstDuplicateFVar? fvarIds then
    throw (.duplicateLocal function.name duplicate)
  let labels := collectLabels function.body
  if let some duplicate := firstDuplicateFVar? labels then
    throw (.duplicateLabel function.name duplicate)
  let context : CheckContext := {
    module
    function
    locals := (function.params ++ function.locals).toList }
  let flow ← checkInstructions context (some []) function.body
  if let some label := flow.branches.head? then
    throw (.escapingBranch function.name label)
  if let some actual := flow.fallthrough then
    let expected := function.results.toList
    unless stackMatches actual expected do
      throw (.stackMismatch function.name expected actual)

/-- Validate all module identities and every function's semantic operand stack. -/
def validateModule (module : Module) : Except SymbolicError Unit := do
  validateModuleShape module
  module.functions.forM (validateFunction module)

end Fir.Wasm
