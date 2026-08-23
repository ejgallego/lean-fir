import Fir.Wasm.Validate

namespace Fir.Wasm.Emit.ClosureDispatch

open Fir.Wasm
open Lean
open Lean.Compiler

mutual

/--
Collect the declaration targets allocated by `pap` nodes in one final-LCNF
code tree, in first-use order.
-/
partial def collectPartialApplicationTargetsCode (targets : Array Name) :
    LCNF.Code .impure → Array Name
  | .let decl continuation =>
      let targets := match decl.value with
        | .pap name _ => addUniqueName targets name
        | _ => targets
      collectPartialApplicationTargetsCode targets continuation
  | .fun _ _ h => nomatch h
  | .jp decl continuation =>
      collectPartialApplicationTargetsCode
        (collectPartialApplicationTargetsCode targets decl.value) continuation
  | .cases cases =>
      cases.alts.foldl collectPartialApplicationTargetsAlt targets
  | .oset _ _ _ continuation
  | .uset _ _ _ continuation
  | .sset _ _ _ _ _ continuation
  | .setTag _ _ continuation
  | .inc _ _ _ _ continuation
  | .dec _ _ _ _ _ continuation
  | .del _ continuation =>
      collectPartialApplicationTargetsCode targets continuation
  | .jmp .. | .return .. | .unreach .. => targets

partial def collectPartialApplicationTargetsAlt (targets : Array Name) :
    LCNF.Alt .impure → Array Name
  | .ctorAlt _ code | .default code =>
      collectPartialApplicationTargetsCode targets code
  | .alt _ _ _ h => nomatch h

end

def partialApplicationTargets (program : Fir.LeanIR.ImpureProgram) : Array Name :=
  program.decls.foldl (init := #[]) fun targets decl =>
    match decl.value with
    | .code code => collectPartialApplicationTargetsCode targets code
    | .extern _ => targets

structure PruneStats where
  sourceTargets : Array Name
  retainedCandidates : Nat
  removedCandidates : Nat
  deriving Inhabited, Repr

private structure InstructionPruneResult where
  instructions : List Instruction := []
  retainedCandidates : Nat := 0
  removedCandidates : Nat := 0
  deriving Inhabited

private def InstructionPruneResult.add
    (left right : InstructionPruneResult) : InstructionPruneResult := {
  instructions := left.instructions ++ right.instructions
  retainedCandidates := left.retainedCandidates + right.retainedCandidates
  removedCandidates := left.removedCandidates + right.removedCandidates }

/--
Remove compiler-generated closure-dispatch branches whose static target is not
allocated by the closed source program. The recognizable three-instruction
prefix is emitted only by `compileClosureCandidateChain`: preserving that
boundary avoids rewriting ordinary `if` expressions.

When a candidate is removed its body is unreachable for this source boundary,
so only the fallthrough chain is retained. Nested structured code in retained
bodies is processed recursively.
-/
private partial def pruneInstructions (targets : Array Name) :
    List Instruction → InstructionPruneResult
  | [] => {}
  | .localGet closureId ::
      .call (.runtime (.closureMatches target arity fixed)) ::
      .ifElse thenBody elseBody :: rest =>
      if targets.contains target then
        let thenResult := pruneInstructions targets thenBody
        let elseResult := pruneInstructions targets elseBody
        let restResult := pruneInstructions targets rest
        let branch : Instruction := .ifElse thenResult.instructions elseResult.instructions
        {
          instructions := .localGet closureId ::
            .call (.runtime (.closureMatches target arity fixed)) ::
              branch :: restResult.instructions
          retainedCandidates := thenResult.retainedCandidates +
            elseResult.retainedCandidates + restResult.retainedCandidates + 1
          removedCandidates := thenResult.removedCandidates +
            elseResult.removedCandidates + restResult.removedCandidates }
      else
        let result := pruneInstructions targets (elseBody ++ rest)
        { result with removedCandidates := result.removedCandidates + 1 }
  | .block label body :: rest =>
      let bodyResult := pruneInstructions targets body
      let restResult := pruneInstructions targets rest
      ({ bodyResult with instructions := [.block label bodyResult.instructions] }).add
        restResult
  | .loop label body :: rest =>
      let bodyResult := pruneInstructions targets body
      let restResult := pruneInstructions targets rest
      ({ bodyResult with instructions := [.loop label bodyResult.instructions] }).add
        restResult
  | .ifElse thenBody elseBody :: rest =>
      let thenResult := pruneInstructions targets thenBody
      let elseResult := pruneInstructions targets elseBody
      let restResult := pruneInstructions targets rest
      {
        instructions :=
          .ifElse thenResult.instructions elseResult.instructions ::
            restResult.instructions
        retainedCandidates := thenResult.retainedCandidates +
          elseResult.retainedCandidates + restResult.retainedCandidates
        removedCandidates := thenResult.removedCandidates +
          elseResult.removedCandidates + restResult.removedCandidates }
  | instruction :: rest =>
      let result := pruneInstructions targets rest
      { result with instructions := instruction :: result.instructions }

private def pruneFunction (targets : Array Name) (function : Function) :
    Function × Nat × Nat :=
  let result := pruneInstructions targets function.body
  ({ function with body := result.instructions }, result.retainedCandidates,
    result.removedCandidates)

inductive PruneError where
  | invalidInput (error : SymbolicError)
  | unexpectedTarget (name : Name)
  | invalidOutput (error : SymbolicError)
  deriving Inhabited, Repr

/--
Prune all-target closure dispatch after ordinary lowering and before resident
linking. This function is valid only for a source boundary at which every
closure value eventually applied by generated code was allocated by a `pap`
node in `program`; in particular, application JavaScript must not transfer a
pre-existing closure object.

The stable closure target/descriptor tables are intentionally retained. They
are semantic ABI metadata consumed by W6 and may contain unused rows after
this generation-only optimization. Runtime imports are rebuilt from the
rewritten functions, while external declaration imports preserve their
existing order and signatures.
-/
def pruneClosedProgram (program : Fir.LeanIR.ImpureProgram) (module : Module)
    (validate : Bool := true) : Except PruneError (Module × PruneStats) := do
  if validate then
    match Fir.Wasm.validateModule module with
    | .ok () => pure ()
    | .error error => throw (.invalidInput error)
  let targets := partialApplicationTargets program
  let rows := module.functions.map (pruneFunction targets)
  let functions := rows.map (fun row => row.1)
  let retainedCandidates := rows.foldl (init := 0) fun total row =>
    total + row.2.1
  let removedCandidates := rows.foldl (init := 0) fun total row =>
    total + row.2.2
  let runtimeOperations := Fir.Wasm.collectRuntimeOps functions
  let retainedTargets := runtimeOperations.filterMap RuntimeOp.closureTarget?
  if let some unexpected := retainedTargets.find? fun target => !targets.contains target then
    throw (.unexpectedTarget unexpected)
  let externalImports := module.imports.filter (fun import_ => import_.operation?.isNone)
  let result : Module := {
    module with
    imports := runtimeOperations.mapIdx Fir.Wasm.runtimeImport ++ externalImports
    functions
    runtimeOperations }
  if validate then
    match Fir.Wasm.validateModule result with
    | .ok () => pure ()
    | .error error => throw (.invalidOutput error)
  return (result, {
    sourceTargets := targets
    retainedCandidates
    removedCandidates })

private def keptTarget : Name := `closureDispatchKept
private def removedTarget : Name := `closureDispatchRemoved
private def closureId : FVarId := ⟨`closure⟩

private def pruneExampleModule : Module := {
  imports := #[
    runtimeImport 0 (.closureMatches removedTarget 2 1),
    runtimeImport 1 (.closureMatches keptTarget 2 1)]
  functions := #[{
    name := `closureDispatchPruneExample
    params := #[(closureId, .object)]
    results := #[.object]
    locals := #[]
    body := [
      .localGet closureId,
      .call (.runtime (.closureMatches removedTarget 2 1)),
      .ifElse [.unreachable] [
        .localGet closureId,
        .call (.runtime (.closureMatches keptTarget 2 1)),
        .ifElse [.localGet closureId, .ret] [.unreachable]]]}]
  exports := #[`closureDispatchPruneExample]
  initializers := #[]
  runtimeOperations := #[
    .closureMatches removedTarget 2 1,
    .closureMatches keptTarget 2 1]
  closureDispatch := #[removedTarget, keptTarget] }

private def pruneExampleResult :=
  let rows := pruneExampleModule.functions.map (pruneFunction #[keptTarget])
  (rows[0]?.map (fun row => row.1.body), rows[0]?.map (fun row => (row.2.1, row.2.2)))

#guard pruneExampleResult ==
  (some [
    .localGet closureId,
    .call (.runtime (.closureMatches keptTarget 2 1)),
    .ifElse [.localGet closureId, .ret] [.unreachable]],
   some (1, 1))

end Fir.Wasm.Emit.ClosureDispatch
