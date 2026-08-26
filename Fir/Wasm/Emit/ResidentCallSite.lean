import Fir.Wasm.Validate

namespace Fir.Wasm.Emit.ResidentCallSite

open Fir.Wasm
open Lean

/-!
# Resident call-site rewrites

Some operations in Lean's C runtime are `static inline` wrappers around a
cold out-of-line helper. Resident Wasm helpers retain the cold implementation,
while these rules describe the caller-local state needed to reproduce the
inline wrapper at a symbolic call site.
-/

/-- A compiler result-local refinement justified by the kinds of the original
call operands.

`argumentKinds` follows the target signature. `none` accepts any compiler
local, while `some kind` requires an immediately preceding `localGet` whose
declared kind is exactly `kind`. A matching call must be followed immediately
by the compiler's `localSet` for its result, and that local must have no other
definition in the function.

The provider remains responsible for the semantic transfer rule. The generic
machinery checks only that the operand conditions and result refinement agree
with the target signature. -/
structure ConditionalResultRefinement where
  argumentKinds : Array (Option AbiKind)
  kind : AbiKind
  deriving Inhabited, BEq

/-- One typed call replacement and the fresh locals it requires.

`signature` is deliberately semantic rather than merely physical: a rewrite
for an `object`/`tobject`/`tagged` operation must not be accepted just because
all three happen to occupy an `i32` Wasm lane.  `validateRewrites` checks this
contract against the source module before any caller body is changed. -/
structure Rewrite where
  target : CallTarget
  signature : Signature
  body : List Instruction
  locals : Array (FVarId × AbiKind) := #[]
  conditionalResultRefinement? : Option ConditionalResultRefinement := none
  deriving Inhabited, BEq

inductive Error where
  | duplicateTarget (rewriteIndex previousIndex : Nat)
  | missingTarget (rewriteIndex : Nat)
  | incompatibleSignature (rewriteIndex : Nat)
  | invalidConditionalRefinement (rewriteIndex : Nat)
  | reservedLocal (function : Name) (localId : FVarId)
  | conflictingRequirement (localId : FVarId)
  deriving Inhabited, Repr

/-- Check the semantic declaration contract of every registered rewrite.

This is separate from the ordinary symbolic module validator: the registry
check prevents a stale or duplicate primitive specification, while final
module validation checks the replacement instruction body at every concrete
caller stack boundary. -/
def validateRewrites (rewrites : Array Rewrite) (module : Module) :
    Except Error Unit := do
  let mut seen : Std.HashMap CallTarget Nat :=
    Std.HashMap.emptyWithCapacity rewrites.size
  for (rewrite, index) in rewrites.zipIdx do
    if let some previousIndex := seen.get? rewrite.target then
      throw (.duplicateTarget index previousIndex)
    seen := seen.insert rewrite.target index
    let some signature := module.callSignature? rewrite.target |
      throw (.missingTarget index)
    unless signature == rewrite.signature do
      throw (.incompatibleSignature index)
    if let some refinement := rewrite.conditionalResultRefinement? then
      unless refinement.argumentKinds.size == signature.params.size do
        throw (.invalidConditionalRefinement index)
      let some ordinary := signature.results[0]? |
        throw (.invalidConditionalRefinement index)
      unless signature.results.size == 1 && refinement.kind.refines ordinary do
        throw (.invalidConditionalRefinement index)
      for pair in refinement.argumentKinds.zip signature.params do
        if let some actual := pair.1 then
          unless actual.refines pair.2 do
            throw (.invalidConditionalRefinement index)

private partial def instructionCalls (target : CallTarget) : Instruction → Bool
  | .call actual => actual == target
  | .block _ body | .loop _ body => body.any (instructionCalls target)
  | .ifElse thenBody elseBody =>
      thenBody.any (instructionCalls target) ||
        elseBody.any (instructionCalls target)
  | _ => false

private def callArgumentsMatch (locals : LocalKinds)
    (conditions : Array (Option AbiKind)) (instructions : Array Instruction)
    (callIndex : Nat) : Bool :=
  if callIndex < conditions.size then false
  else
    let arguments := instructions.extract (callIndex - conditions.size) callIndex
    arguments.size == conditions.size &&
      (arguments.zip conditions).all fun pair =>
        match pair.1, pair.2 with
        | .localGet localId, some expected =>
            findLocalKind? locals localId == some expected
        | .localGet _, none => true
        | _, _ => false

private partial def refinedResultLocals (target : CallTarget)
    (locals : LocalKinds) (conditions : Array (Option AbiKind))
    (instructions : List Instruction) : Array FVarId :=
  let instructions := instructions.toArray
  instructions.zipIdx.foldl (init := #[]) fun results pair =>
    match pair.1 with
    | .call actual =>
        if actual == target &&
            callArgumentsMatch locals conditions instructions pair.2 then
          match instructions[pair.2 + 1]? with
          | some (.localSet result) => results.push result
          | _ => results
        else results
    | .block _ body | .loop _ body =>
        results ++ refinedResultLocals target locals conditions body
    | .ifElse thenBody elseBody =>
        results ++ refinedResultLocals target locals conditions thenBody ++
          refinedResultLocals target locals conditions elseBody
    | _ => results

private partial def assignedLocals : List Instruction → Array FVarId
  | instructions => instructions.foldl (init := #[]) fun results instruction =>
      match instruction with
      | .localSet result => results.push result
      | .block _ body | .loop _ body => results ++ assignedLocals body
      | .ifElse thenBody elseBody =>
          results ++ assignedLocals thenBody ++ assignedLocals elseBody
      | _ => results

private def occurrenceCount (values : Array FVarId) (target : FVarId) : Nat :=
  (values.filter fun value => value.name == target.name).size

private def refineFunctionLocalsOnce (rewrites : Array Rewrite)
    (function : Function) : Function :=
  let localKinds := function.params.toList ++ function.locals.toList
  let assignments := assignedLocals function.body
  let candidates := rewrites.filterMap fun rewrite =>
    rewrite.conditionalResultRefinement?.map fun refinement =>
      (refinement,
        refinedResultLocals rewrite.target localKinds
          refinement.argumentKinds function.body)
  let locals := function.locals.map fun entry =>
    let applicable := candidates.filterMap fun candidate =>
      let count := occurrenceCount candidate.2 entry.1
      if count > 0 && count == occurrenceCount assignments entry.1 &&
          candidate.1.kind.refines entry.2 then
        some candidate.1.kind
      else none
    match applicable[0]? with
    | some kind =>
        if applicable.all (· == kind) then (entry.1, kind) else entry
    | none => entry
  { function with locals }

/-- Propagate reviewed representation/range facts from primitive operands to
the compiler's single-assignment result locals. Iterate to a fixed point so a
chain of eligible primitive calls retains the fact without a declaration- or
application-specific allowlist. -/
def refineFunctionLocals (rewrites : Array Rewrite)
    (function : Function) : Function :=
  let rec loop : Nat → Function → Function
    | 0, function => function
    | fuel + 1, function =>
        let refined := refineFunctionLocalsOnce rewrites function
        if refined.locals == function.locals then refined
        else loop fuel refined
  loop function.locals.size function

/-- Add only the rule locals needed by calls actually present in `function`. -/
def reserveLocals (rewrites : Array Rewrite) (function : Function) :
    Except Error Function := do
  let mut required : Array (FVarId × AbiKind) := #[]
  for rewrite in rewrites do
    if function.body.any (instructionCalls rewrite.target) then
      for requirement in rewrite.locals do
        if function.params.any (·.1 == requirement.1) ||
            function.locals.any (·.1 == requirement.1) then
          throw (.reservedLocal function.name requirement.1)
        if let some previous := required.find? (·.1 == requirement.1) then
          unless previous.2 == requirement.2 do
            throw (.conflictingRequirement requirement.1)
        else
          required := required.push requirement
  return { function with locals := function.locals ++ required }

mutual
  private partial def rewriteInstructions (rewrites : Array Rewrite) :
      List Instruction → List Instruction
    | instructions => instructions.flatMap (rewriteInstruction rewrites)

  private partial def rewriteInstruction (rewrites : Array Rewrite) :
      Instruction → List Instruction
    | .call target =>
        match rewrites.find? (·.target == target) with
        | some rewrite => rewrite.body
        | none => [.call target]
    | .block label body =>
        [.block label (rewriteInstructions rewrites body)]
    | .loop label body =>
        [.loop label (rewriteInstructions rewrites body)]
    | .ifElse thenBody elseBody =>
        [.ifElse (rewriteInstructions rewrites thenBody)
          (rewriteInstructions rewrites elseBody)]
    | instruction => [instruction]
end

/-- Apply checked caller-local reservation followed by call replacement. -/
private def rewriteFunction (rewrites : Array Rewrite) (function : Function) :
    Except Error Function := do
  let function := refineFunctionLocals rewrites function
  let function ← reserveLocals rewrites function
  return { function with body := rewriteInstructions rewrites function.body }

/-- Validate one typed rewrite registry and apply it to every module function. -/
def rewriteModuleFunctions (rewrites : Array Rewrite) (module : Module) :
    Except Error (Array Function) := do
  validateRewrites rewrites module
  module.functions.mapM (rewriteFunction rewrites)

private def exampleValue : FVarId := ⟨`exampleValue⟩
private def exampleResult : FVarId := ⟨`exampleResult⟩
private def exampleResult2 : FVarId := ⟨`exampleResult2⟩
private def exampleScratch : FVarId := ⟨`exampleScratch⟩
private def exampleTarget : CallTarget := .declaration `Example.inline

private def exampleRewrite : Rewrite := {
  target := exampleTarget
  signature := { params := #[.uint32], results := #[.uint32] }
  locals := #[(exampleResult, .uint32)]
  body := [.localSet exampleResult, .localGet exampleResult] }

private def exampleFunction : Function := {
  name := `Example.caller
  params := #[(exampleValue, .uint32)]
  results := #[.uint32]
  locals := #[]
  body := [.localGet exampleValue, .call exampleTarget, .ret] }

#guard match rewriteFunction #[exampleRewrite] exampleFunction with
  | .ok function =>
      function.locals == #[(exampleResult, .uint32)] &&
        function.body == [.localGet exampleValue, .localSet exampleResult,
          .localGet exampleResult, .ret]
  | .error _ => false

#guard match rewriteFunction #[{
    exampleRewrite with locals := #[(exampleValue, .uint32)]
  }] exampleFunction with
  | .error (.reservedLocal function localId) =>
      function == exampleFunction.name && localId == exampleValue
  | _ => false

private def exampleObjectTarget : CallTarget :=
  .declaration `Example.objectInline

private def exampleObjectRewrite : Rewrite := {
  target := exampleObjectTarget
  signature := { params := #[.tobject], results := #[.tobject] }
  locals := #[(exampleScratch, .tobject)]
  conditionalResultRefinement? := some {
    argumentKinds := #[some .tagged]
    kind := .tagged }
  body := [.localSet exampleScratch, .localGet exampleScratch] }

private def exampleObjectFunction (argumentKind : AbiKind) : Function := {
  name := `Example.objectCaller
  params := #[(exampleValue, argumentKind)]
  results := #[.tobject]
  locals := #[(exampleResult, .tobject)]
  body := [
    .localGet exampleValue,
    .call exampleObjectTarget,
    .localSet exampleResult,
    .localGet exampleResult,
    .ret] }

#guard (refineFunctionLocals #[exampleObjectRewrite]
    (exampleObjectFunction .tagged)).locals == #[(exampleResult, .tagged)]

#guard (refineFunctionLocals #[exampleObjectRewrite]
    (exampleObjectFunction .tobject)).locals == #[(exampleResult, .tobject)]

private def exampleObjectChainFunction : Function := {
  name := `Example.objectChainCaller
  params := #[(exampleValue, .tagged)]
  results := #[.tobject]
  locals := #[(exampleResult, .tobject), (exampleResult2, .tobject)]
  body := [
    .localGet exampleValue,
    .call exampleObjectTarget,
    .localSet exampleResult,
    .localGet exampleResult,
    .call exampleObjectTarget,
    .localSet exampleResult2,
    .localGet exampleResult2,
    .ret] }

#guard (refineFunctionLocals #[exampleObjectRewrite]
    exampleObjectChainFunction).locals ==
  #[(exampleResult, .tagged), (exampleResult2, .tagged)]

private def exampleMultiplyAssignedFunction : Function := {
  exampleObjectFunction .tagged with
  body := [
    .localGet exampleValue,
    .call exampleObjectTarget,
    .localSet exampleResult,
    .i32Const .tagged 1,
    .localSet exampleResult,
    .localGet exampleResult,
    .ret] }

#guard (refineFunctionLocals #[exampleObjectRewrite]
    exampleMultiplyAssignedFunction).locals == #[(exampleResult, .tobject)]

private def exampleModule : Module := {
  functions := #[exampleFunction]
  imports := #[{
    key := .external `Example.inline
    moduleName := "example"
    itemName := "inline"
    signature := exampleRewrite.signature }]
  exports := #[]
  initializers := #[]
  runtimeOperations := #[] }

#guard (validateRewrites #[exampleRewrite] exampleModule).isOk

private def exampleObjectModule : Module := {
  functions := #[exampleObjectFunction .tagged]
  imports := #[{
    key := .external `Example.objectInline
    moduleName := "example"
    itemName := "objectInline"
    signature := exampleObjectRewrite.signature }]
  exports := #[]
  initializers := #[]
  runtimeOperations := #[] }

#guard (validateRewrites #[exampleObjectRewrite] exampleObjectModule).isOk

#guard match validateRewrites #[{
    exampleObjectRewrite with
    conditionalResultRefinement? := some {
      argumentKinds := #[some .uint32]
      kind := .tagged }
  }] exampleObjectModule with
  | .error (.invalidConditionalRefinement 0) => true
  | _ => false

#guard match validateRewrites #[{
    exampleRewrite with
    signature := { params := #[.tobject], results := #[.tobject] }
  }] exampleModule with
  | .error (.incompatibleSignature 0) => true
  | _ => false

#guard match validateRewrites #[{
    exampleRewrite with target := .declaration `Example.missing
  }] exampleModule with
  | .error (.missingTarget 0) => true
  | _ => false

#guard match validateRewrites #[exampleRewrite, exampleRewrite] exampleModule with
  | .error (.duplicateTarget 1 0) => true
  | _ => false

end Fir.Wasm.Emit.ResidentCallSite
