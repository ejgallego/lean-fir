import Fir.LeanIR.Passes.SimpCase
import Fir.LeanIR.Passes.AlphaEqvBind
import Fir.LeanIR.Passes.AlphaEqvLocal
import Fir.LeanIR.Passes.QSortPerm

namespace Fir.LeanIR.Passes.AlphaEqv

open Lean
open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.Passes.SimpCase

/-- The terminal fragment of the proof-facing impure-code relation. -/
inductive TerminalCodeRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId) :
    LCNF.Code .impure → LCNF.Code .impure → Prop where
  | ret (related : ScopedFVarRelated rho leftScope rightScope leftId rightId) :
      TerminalCodeRelated rho leftScope rightScope (.return leftId) (.return rightId)
  | unreachable :
      TerminalCodeRelated rho leftScope rightScope (.unreach leftType) (.unreach rightType)

/-- A jump target is in both active join scopes and follows the current renaming. -/
abbrev ScopedJoinRelated (rho : FVarIdMap FVarId)
    (leftJoins rightJoins : List FVarId) (left right : FVarId) : Prop :=
  ScopedFVarRelated rho leftJoins rightJoins left right

/-- A join binder is globally fresh with respect to the currently visible names. -/
structure FreshJoinBinder (fvarId : FVarId)
    (variables joins : List FVarId) : Prop where
  variables : FreshForScope fvarId variables
  joins : FreshForScope fvarId joins

set_option linter.unusedVariables false in
mutual

/--
The proof-facing code relation, covering terminal code, value bindings,
join-point control flow, and the sequential impure heap/ownership instructions.
Recursive binders record the same scope and renaming extensions performed by
Lean's alpha-equivalence checker.
-/
inductive CodeRelated :
    FVarIdMap FVarId → List FVarId → List FVarId →
      {leftJoins rightJoins : List FVarId} →
      LCNF.Code .impure → LCNF.Code .impure → Prop where
  | terminal
      (related : TerminalCodeRelated rho leftScope rightScope left right) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope left right
  | letE
      (declaration : LetDeclValueRelated rho leftScope rightScope leftDecl rightDecl)
      (leftFresh : FreshForScope leftDecl.fvarId leftScope)
      (rightFresh : FreshForScope rightDecl.fvarId rightScope)
      (leftJoinFresh : FreshForScope leftDecl.fvarId leftJoins)
      (rightJoinFresh : FreshForScope rightDecl.fvarId rightJoins)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          (rho.insert rightDecl.fvarId leftDecl.fvarId)
          (leftDecl.fvarId :: leftScope) (rightDecl.fvarId :: rightScope)
          leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.let leftDecl leftContinuation) (.let rightDecl rightContinuation)
  | jp
      (leftFresh : FreshJoinBinder leftDecl.fvarId leftScope leftJoins)
      (rightFresh : FreshJoinBinder rightDecl.fvarId rightScope rightJoins)
      (body :
        ParamBodyRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope
          leftDecl.params.toList rightDecl.params.toList
          leftDecl.value rightDecl.value)
      (continuation :
        CodeRelated
          (leftJoins := leftDecl.fvarId :: leftJoins)
          (rightJoins := rightDecl.fvarId :: rightJoins)
          (rho.insert rightDecl.fvarId leftDecl.fvarId)
          leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.jp leftDecl leftContinuation) (.jp rightDecl rightContinuation)
  | jmp
      (target : ScopedJoinRelated rho leftJoins rightJoins leftTarget rightTarget)
      (args : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.jmp leftTarget leftArgs) (.jmp rightTarget rightArgs)
  | cases
      (discr : ScopedFVarRelated rho leftScope rightScope
        leftCases.discr rightCases.discr)
      (selected : ∀ tag,
        CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope
          (chooseAlt tag leftCases.alts.toList)
          (chooseAlt tag rightCases.alts.toList)) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.cases leftCases) (.cases rightCases)
  | oset
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (field : ArgRelated rho leftScope rightScope leftField rightField)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.oset leftObject index leftField leftContinuation)
        (.oset rightObject index rightField rightContinuation)
  | uset
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (field : ScopedFVarRelated rho leftScope rightScope leftField rightField)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.uset leftObject index leftField leftContinuation)
        (.uset rightObject index rightField rightContinuation)
  | sset
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (field : ScopedFVarRelated rho leftScope rightScope leftField rightField)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.sset leftObject width offset leftField leftType leftContinuation)
        (.sset rightObject width offset rightField rightType rightContinuation)
  | setTag
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.setTag leftObject tag leftContinuation)
        (.setTag rightObject tag rightContinuation)
  | inc
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.inc leftObject amount check persistent leftContinuation)
        (.inc rightObject amount check persistent rightContinuation)
  | dec
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.dec leftObject amount check persistent objects leftContinuation)
        (.dec rightObject amount check persistent objects rightContinuation)
  | del
      (object : ScopedFVarRelated rho leftScope rightScope leftObject rightObject)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          rho leftScope rightScope leftContinuation rightContinuation) :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.del leftObject leftContinuation) (.del rightObject rightContinuation)

/--
Related join/function bodies under their pointwise alpha-renamed parameters.
The join binder itself is deliberately absent: Lean checks the body before it
extends the renaming for the continuation.
-/
inductive ParamBodyRelated :
    FVarIdMap FVarId → List FVarId → List FVarId →
      {leftJoins rightJoins : List FVarId} →
      List (LCNF.Param .impure) → List (LCNF.Param .impure) →
      LCNF.Code .impure → LCNF.Code .impure → Prop where
  | nil
      (body : CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftCode rightCode) :
      ParamBodyRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope [] [] leftCode rightCode
  | cons
      (leftFresh : FreshForScope leftParam.fvarId leftScope)
      (rightFresh : FreshForScope rightParam.fvarId rightScope)
      (leftJoinFresh : FreshForScope leftParam.fvarId leftJoins)
      (rightJoinFresh : FreshForScope rightParam.fvarId rightJoins)
      (rest : ParamBodyRelated
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        (rho.insert rightParam.fvarId leftParam.fvarId)
        (leftParam.fvarId :: leftScope) (rightParam.fvarId :: rightScope)
        leftRest rightRest leftCode rightCode) :
      ParamBodyRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (leftParam :: leftRest) (rightParam :: rightRest) leftCode rightCode

/-- A case-table lookup either fails on both sides or selects related code. -/
inductive CaseSelectionRelated :
    FVarIdMap FVarId → List FVarId → List FVarId →
      {leftJoins rightJoins : List FVarId} →
      Option (LCNF.Code .impure) → Option (LCNF.Code .impure) → Prop where
  | none : CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope none none
  | some
      (code : CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftCode rightCode) :
      CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (some leftCode) (some rightCode)

end

/--
Semantic relation for the runtime join-point stacks. `empty` intentionally
permits arbitrary dormant runtime entries when no join is visible through the
proof index. `join` records the declaration body at installation time, `bind`
transports the same stack across a fresh ordinary binder, and `ignored` retains
dormant runtime prefixes while exposing a declaration's historical scope.
Together they keep the variable and join namespaces distinct in the shared
renaming map.
-/
inductive JoinEnvsRelated :
    FVarIdMap FVarId → List FVarId → List FVarId →
      List FVarId → List FVarId → JoinEnv → JoinEnv → Prop where
  | empty : JoinEnvsRelated rho leftScope rightScope [] [] left right
  | join
      (prior : JoinEnvsRelated rho leftScope rightScope
        leftJoins rightJoins leftTail rightTail)
      (renamingScoped : RenamingScoped rho leftScope rightScope)
      (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
      (leftFresh : FreshJoinBinder leftDecl.fvarId leftScope leftJoins)
      (rightFresh : FreshJoinBinder rightDecl.fvarId rightScope rightJoins)
      (body : ParamBodyRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        leftDecl.params.toList rightDecl.params.toList
        leftDecl.value rightDecl.value) :
      JoinEnvsRelated (rho.insert rightDecl.fvarId leftDecl.fvarId)
        leftScope rightScope
        (leftDecl.fvarId :: leftJoins) (rightDecl.fvarId :: rightJoins)
        ((leftDecl.fvarId, leftDecl) :: leftTail)
        ((rightDecl.fvarId, rightDecl) :: rightTail)
  | bind
      (prior : JoinEnvsRelated rho leftScope rightScope
        leftJoins rightJoins left right)
      (renamingScoped : RenamingScoped rho leftScope rightScope)
      (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
      (leftFresh : FreshForScope leftId leftScope)
      (rightFresh : FreshForScope rightId rightScope)
      (leftJoinFresh : FreshForScope leftId leftJoins)
      (rightJoinFresh : FreshForScope rightId rightJoins) :
      JoinEnvsRelated (rho.insert rightId leftId)
        (leftId :: leftScope) (rightId :: rightScope)
        leftJoins rightJoins left right
  | ignored
      (leftFresh : FreshForScope leftId leftJoins)
      (rightFresh : FreshForScope rightId rightJoins)
      (prior : JoinEnvsRelated rho leftScope rightScope
        leftJoins rightJoins leftTail rightTail) :
      JoinEnvsRelated rho leftScope rightScope leftJoins rightJoins
        ((leftId, leftDecl) :: leftTail) ((rightId, rightDecl) :: rightTail)

/-- Every identifier visible in the smaller scope remains visible in the larger one. -/
def ScopeSubset (smaller larger : List FVarId) : Prop :=
  ∀ fvarId, smaller.contains fvarId = true → larger.contains fvarId = true

theorem scopeSubset_cons_right : ScopeSubset scope (fvarId :: scope) := by
  unfold ScopeSubset
  intro candidate member
  simp [member]

theorem scopeSubset_trans
    (first : ScopeSubset small middle) (second : ScopeSubset middle large) :
    ScopeSubset small large := by
  unfold ScopeSubset at *
  intro candidate member
  exact second candidate (first candidate member)

theorem freshForScope_of_subset
    (fresh : FreshForScope fvarId large) (subset : ScopeSubset small large) :
    FreshForScope fvarId small := by
  intro old oldScoped
  exact fresh old (subset old oldScoped)

/-- Recover agreement before a fresh renaming insertion on unchanged scopes. -/
theorem envsAgree_before_fresh_insert
    (agree : EnvsAgree (rho.insert rightId leftId)
      leftScope rightScope leftEnv rightEnv)
    (rightFresh : FreshForScope rightId rightScope) :
    EnvsAgree rho leftScope rightScope leftEnv rightEnv := by
  intro candidateLeft candidateLeftScoped candidateRight candidateRightScoped related
  have different := rightFresh candidateRight candidateRightScoped
  exact agree candidateLeft candidateLeftScoped candidateRight candidateRightScoped
    ((fVarRelated_insert_of_name_ne
      rho leftId rightId candidateLeft candidateRight different).mpr related)

/-- Recover old-scope agreement after binding a fresh ordinary variable. -/
theorem envsAgree_before_variable_insert
    (agree : EnvsAgree (rho.insert rightId leftId)
      (leftId :: leftScope) (rightId :: rightScope) leftEnv rightEnv)
    (rightFresh : FreshForScope rightId rightScope) :
    EnvsAgree rho leftScope rightScope leftEnv rightEnv := by
  intro candidateLeft candidateLeftScoped candidateRight candidateRightScoped related
  have different := rightFresh candidateRight candidateRightScoped
  apply agree candidateLeft (by simp [candidateLeftScoped])
    candidateRight (by simp [candidateRightScoped])
  exact (fVarRelated_insert_of_name_ne
    rho leftId rightId candidateLeft candidateRight different).mpr related

/-- Bind a list of parameter declarations to an equally long list of values. -/
def bindParamValues (env : Env) (params : List (LCNF.Param .impure))
    (values : List Value) : Env :=
  (params.zip values).foldl
    (fun current pair => bind current pair.fst.fvarId pair.snd) env

private theorem listMapM_length_of_ok
    {input output error : Type} (items : List input)
    (action : input → Except error output) (results : List output)
    (found : items.mapM action = Except.ok results) :
    results.length = items.length := by
  induction items generalizing results with
  | nil =>
      change Except.ok [] = Except.ok results at found
      have resultsEq : ([] : List output) = results := Except.ok.inj found
      subst results
      rfl
  | cons item items ih =>
      rw [List.mapM_cons] at found
      cases itemResult : action item with
      | error fault =>
          rw [itemResult] at found
          change Except.error fault = Except.ok results at found
          contradiction
      | ok value =>
          rw [itemResult] at found
          cases restResult : items.mapM action with
          | error fault =>
              rw [restResult] at found
              change Except.error fault = Except.ok results at found
              contradiction
          | ok rest =>
              rw [restResult] at found
              change Except.ok (value :: rest) = Except.ok results at found
              have resultsEq : value :: rest = results := Except.ok.inj found
              subst results
              simp [ih rest restResult]

/-- Successful argument evaluation preserves the source array length. -/
theorem evalArgs_size_of_ok
    (found : evalArgs env args = .ok values) : values.size = args.size := by
  unfold evalArgs at found
  rw [Array.mapM_eq_mapM_toList] at found
  cases listResult : args.toList.mapM (evalArg env) with
  | error fault =>
      rw [listResult] at found
      change Except.error fault = Except.ok values at found
      contradiction
  | ok results =>
      rw [listResult] at found
      change Except.ok results.toArray = Except.ok values at found
      have valuesEq : results.toArray = values := Except.ok.inj found
      subst values
      simpa using listMapM_length_of_ok args.toList (evalArg env) results listResult

/-- Pointwise-related argument arrays have the same length. -/
private theorem listRel_length_eq_code
    (related : ListRel relation left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem ArgsRelated.size_eq
    (related : ArgsRelated rho leftScope rightScope leftArgs rightArgs) :
    leftArgs.size = rightArgs.size := by
  simpa using listRel_length_eq_code related

/-- Related parameter bodies introduce equally many parameters. -/
theorem ParamBodyRelated.length_eq
    (related : ParamBodyRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope leftParams rightParams leftCode rightCode) :
    leftParams.length = rightParams.length := by
  induction leftParams generalizing rho leftScope rightScope rightParams with
  | nil =>
      cases related
      rfl
  | cons leftParam leftRest ih =>
      cases related with
      | cons _ _ _ _ rest => simpa using ih rest

/-- A declaration body is reflexively related under its parameter binders. -/
def DeclBodyRelated (decl : LCNF.Decl .impure) : Prop :=
  match decl.value with
  | .code code =>
      ParamBodyRelated (leftJoins := []) (rightJoins := [])
        ({} : FVarIdMap FVarId) [] []
        decl.params.toList decl.params.toList code code
  | .extern _ => True

/-- Every declaration reachable by name exposes a proof-facing body relation. -/
def ProgramBodiesRelated (program : ImpureProgram) : Prop :=
  ∀ name decl, program.findDecl? name = some decl → DeclBodyRelated decl

/-- Two looked-up code declarations expose alpha-related parameter bodies.
External declarations retain the ABI observed by the interpreter. -/
inductive ProgramDeclRelated :
    LCNF.Decl .impure → LCNF.Decl .impure → Prop where
  | code
      (left right : LCNF.Decl .impure)
      (leftCode rightCode : LCNF.Code .impure)
      (body : ParamBodyRelated (leftJoins := []) (rightJoins := [])
        ({} : FVarIdMap FVarId) [] []
        left.params.toList right.params.toList leftCode rightCode) :
      ProgramDeclRelated
        { left with value := .code leftCode }
        { right with value := .code rightCode }
  | extern
      (left right : LCNF.Decl .impure)
      (leftMetadata rightMetadata : ExternAttrData)
      (arity_eq : left.params.size = right.params.size)
      (paramTypes_eq : left.params.map (·.type) = right.params.map (·.type))
      (resultType_eq : left.type = right.type) :
      ProgramDeclRelated
        { left with value := .extern leftMetadata }
        { right with value := .extern rightMetadata }

/-- Named lookup succeeds or fails on both sides and returns related ABIs. -/
inductive OptionalProgramDeclRelated :
    Option (LCNF.Decl .impure) → Option (LCNF.Decl .impure) → Prop where
  | none : OptionalProgramDeclRelated none none
  | some (related : ProgramDeclRelated left right) :
      OptionalProgramDeclRelated (some left) (some right)

/-- Cross-program alpha boundary used when execution enters a global body. -/
def ProgramsRelated (left right : ImpureProgram) : Prop :=
  ∀ name, OptionalProgramDeclRelated
    (left.findDecl? name) (right.findDecl? name)

theorem ProgramDeclRelated.arity_eq
    (related : ProgramDeclRelated left right) :
    left.params.size = right.params.size := by
  cases related with
  | code _ _ _ _ body => simpa using body.length_eq
  | extern _ _ _ _ arity _ _ => exact arity

/-- The previous one-program body invariant constructs the reflexive instance
of the new cross-program relation. -/
theorem programsRelated_refl
    (bodies : ProgramBodiesRelated program) : ProgramsRelated program program := by
  intro name
  generalize found : program.findDecl? name = declaration
  cases declaration with
  | none => exact .none
  | some declaration =>
      have body := bodies name declaration found
      rcases declaration with ⟨signature, value, recursive, inlineAttr⟩
      cases value with
      | code code =>
          exact OptionalProgramDeclRelated.some
            (ProgramDeclRelated.code
              { toSignature := signature, value := .code code,
                recursive := recursive, inlineAttr? := inlineAttr }
              { toSignature := signature, value := .code code,
                recursive := recursive, inlineAttr? := inlineAttr }
              code code body)
      | extern metadata =>
          exact OptionalProgramDeclRelated.some
            (ProgramDeclRelated.extern
              { toSignature := signature, value := .extern metadata,
                recursive := recursive, inlineAttr? := inlineAttr }
              { toSignature := signature, value := .extern metadata,
                recursive := recursive, inlineAttr? := inlineAttr }
              metadata metadata rfl rfl rfl)

/-- Successful top-level parameter binding exposes its fold and arity facts. -/
theorem bindParams_data_of_ok
    (found : bindParams params values = .ok env) :
    bindParamValues [] params.toList values.toList = env ∧
      values.toList.length = params.toList.length := by
  by_cases sizes : params.size = values.size
  · have foldResult :
        (Except.ok ((params.toList.zip values.toList).foldl
          (fun env pair => bind env pair.fst.fvarId pair.snd) []) :
            Except RuntimeFault Env) = Except.ok env := by
      simpa [bindParams, sizes] using found
    have foldEq := Except.ok.inj foldResult
    exact ⟨by simpa [bindParamValues] using foldEq, by simpa using sizes.symm⟩
  · simp [bindParams, sizes] at found

/-- Parameter binding failures depend only on the two array sizes, not on the
parameter binder identities. -/
theorem bindParams_error_of_size_eq
    (sameSize : leftParams.size = rightParams.size)
    (found : bindParams leftParams values = .error fault) :
    bindParams rightParams values = .error fault := by
  by_cases sizes : leftParams.size = values.size
  · simp [bindParams, sizes] at found
  · have rightMismatch : rightParams.size ≠ values.size := by
      simpa only [sameSize] using sizes
    simpa [bindParams, sizes, rightMismatch, sameSize] using found

/--
Binding equal values to related parameter lists produces related environments
and exposes the declaration bodies under the final accumulated renaming.
-/
theorem paramBody_bind_values_related
    (body : ParamBodyRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope leftParams rightParams leftCode rightCode)
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftRuntime rightRuntime)
    (valuesLength : values.length = leftParams.length) :
    ∃ finalRho finalLeftScope finalRightScope leftBound rightBound,
      bindParamValues leftEnv leftParams values = leftBound ∧
      bindParamValues rightEnv rightParams values = rightBound ∧
      EnvsAgree finalRho finalLeftScope finalRightScope leftBound rightBound ∧
      RenamingScoped finalRho finalLeftScope finalRightScope ∧
      RenamingScoped finalRho leftJoins rightJoins ∧
      JoinEnvsRelated finalRho finalLeftScope finalRightScope
        leftJoins rightJoins leftRuntime rightRuntime ∧
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        finalRho finalLeftScope finalRightScope leftCode rightCode := by
  cases body with
  | nil code =>
      have valuesNil : values = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using valuesLength)
      subst values
      exact ⟨rho, leftScope, rightScope, leftEnv, rightEnv,
        rfl, rfl, agree, renamingScoped, joinRenamingScoped, joinEnvs, code⟩
  | cons leftFresh rightFresh leftJoinFresh rightJoinFresh rest =>
      rename_i leftRest rightRest leftParam rightParam
      cases values with
      | nil => simp at valuesLength
      | cons value values =>
          have restLength : values.length = leftRest.length := by
            simpa using valuesLength
          rcases paramBody_bind_values_related
              (leftEnv := bind leftEnv leftParam.fvarId value)
              (rightEnv := bind rightEnv rightParam.fvarId value)
              (values := values) rest
              (envsAgree_bind agree renamingScoped leftFresh rightFresh)
              (renamingScoped_insert renamingScoped rightFresh)
              (renamingScoped_insert_preserve joinRenamingScoped rightJoinFresh)
              (.bind joinEnvs renamingScoped joinRenamingScoped
                leftFresh rightFresh leftJoinFresh rightJoinFresh)
              restLength with
            ⟨finalRho, finalLeftScope, finalRightScope, leftBound, rightBound,
              leftFold, rightFold, finalAgree, finalRenaming,
              finalJoinRenaming, finalJoins, finalCode⟩
          exact ⟨finalRho, finalLeftScope, finalRightScope, leftBound, rightBound,
            by simpa [bindParamValues] using leftFold,
            by simpa [bindParamValues] using rightFold,
            finalAgree, finalRenaming, finalJoinRenaming, finalJoins, finalCode⟩
termination_by leftParams.length

/--
The semantic payload recovered by looking up a related active join target.
The existential base context is the one in which the declaration body was
checked, and `joins` relates the complete current runtime stacks while exposing
only the joins that were active in that body.
-/
inductive JoinLookupRelated
    (currentLeftJoins currentRightJoins : List FVarId)
    (leftTarget rightTarget : FVarId)
    (leftRuntime rightRuntime : JoinEnv)
    (leftEnv rightEnv : Env) : Prop where
  | intro
      (baseRho : FVarIdMap FVarId)
      (baseLeftScope baseRightScope : List FVarId)
      (baseLeftJoins baseRightJoins : List FVarId)
      (leftDecl rightDecl : LCNF.FunDecl .impure)
      (leftFound : findJoinPoint? leftRuntime leftTarget = some leftDecl)
      (rightFound : findJoinPoint? rightRuntime rightTarget = some rightDecl)
      (body : ParamBodyRelated
        (leftJoins := baseLeftJoins) (rightJoins := baseRightJoins)
        baseRho baseLeftScope baseRightScope
        leftDecl.params.toList rightDecl.params.toList
        leftDecl.value rightDecl.value)
      (joins : JoinEnvsRelated baseRho baseLeftScope baseRightScope
        baseLeftJoins baseRightJoins leftRuntime rightRuntime)
      (envs : EnvsAgree baseRho baseLeftScope baseRightScope leftEnv rightEnv)
      (renamingScoped : RenamingScoped baseRho baseLeftScope baseRightScope)
      (joinRenamingScoped : RenamingScoped baseRho baseLeftJoins baseRightJoins)
      (leftSubset : ScopeSubset baseLeftJoins currentLeftJoins)
      (rightSubset : ScopeSubset baseRightJoins currentRightJoins) :
      JoinLookupRelated currentLeftJoins currentRightJoins
        leftTarget rightTarget leftRuntime rightRuntime leftEnv rightEnv

/-- Related active targets resolve to declarations with related bodies. -/
theorem JoinEnvsRelated.lookup
    (related : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftRuntime rightRuntime)
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (target : ScopedJoinRelated rho leftJoins rightJoins leftTarget rightTarget) :
    JoinLookupRelated leftJoins rightJoins leftTarget rightTarget
      leftRuntime rightRuntime leftEnv rightEnv := by
  induction related with
  | empty => simp [ScopedJoinRelated, ScopedFVarRelated] at target
  | @join rho leftScope rightScope leftJoins rightJoins leftTail rightTail
      leftDecl rightDecl prior oldRenaming oldJoinRenaming leftFresh rightFresh
      body ih =>
      have oldAgree := envsAgree_before_fresh_insert agree rightFresh.variables
      rcases fVarRelated_insert_classify oldJoinRenaming rightFresh.joins
          target.2.1 target.2.2 with newTarget | oldTarget
      · rcases newTarget with ⟨rfl, rfl⟩
        exact .intro rho leftScope rightScope leftJoins rightJoins
          leftDecl rightDecl
          (by simp [findJoinPoint?]) (by simp [findJoinPoint?]) body
          (.ignored leftFresh.joins rightFresh.joins prior)
          oldAgree oldRenaming oldJoinRenaming
          scopeSubset_cons_right scopeSubset_cons_right
      · rcases oldTarget with ⟨leftScoped, rightScoped, oldRelated⟩
        rcases ih oldAgree ⟨leftScoped, rightScoped, oldRelated⟩ with
          ⟨baseRho, baseLeftScope, baseRightScope, baseLeftJoins,
            baseRightJoins, foundLeftDecl, foundRightDecl, leftFound,
            rightFound, foundBody, foundJoins, foundEnvs, foundRenaming,
            foundJoinRenaming, leftSubset, rightSubset⟩
        have leftDifferent := leftFresh.joins leftTarget leftScoped
        have rightDifferent := rightFresh.joins rightTarget rightScoped
        exact .intro baseRho baseLeftScope baseRightScope
          baseLeftJoins baseRightJoins foundLeftDecl foundRightDecl
          (by simpa [findJoinPoint?, leftDifferent] using leftFound)
          (by simpa [findJoinPoint?, rightDifferent] using rightFound)
          foundBody
          (.ignored
            (freshForScope_of_subset leftFresh.joins leftSubset)
            (freshForScope_of_subset rightFresh.joins rightSubset)
            foundJoins)
          foundEnvs foundRenaming foundJoinRenaming
          (scopeSubset_trans leftSubset scopeSubset_cons_right)
          (scopeSubset_trans rightSubset scopeSubset_cons_right)
  | @bind rho leftScope rightScope leftJoins rightJoins leftRuntime rightRuntime
      leftId rightId prior oldRenaming oldJoinRenaming leftFresh rightFresh
      leftJoinFresh rightJoinFresh ih =>
      have oldAgree := envsAgree_before_variable_insert agree rightFresh
      have different := rightJoinFresh rightTarget target.2.1
      have oldTarget : ScopedJoinRelated rho leftJoins rightJoins
          leftTarget rightTarget := ⟨target.1, target.2.1,
        (fVarRelated_insert_of_name_ne
          rho leftId rightId leftTarget rightTarget different).mp target.2.2⟩
      exact ih oldAgree oldTarget
  | @ignored rho leftScope rightScope leftJoins rightJoins leftTail rightTail
      leftId rightId leftDecl rightDecl leftFresh rightFresh prior ih =>
      rcases ih agree target with
        ⟨baseRho, baseLeftScope, baseRightScope, baseLeftJoins,
          baseRightJoins, foundLeftDecl, foundRightDecl, leftFound,
          rightFound, foundBody, foundJoins, foundEnvs, foundRenaming,
          foundJoinRenaming, leftSubset, rightSubset⟩
      have leftDifferent := leftFresh leftTarget target.1
      have rightDifferent := rightFresh rightTarget target.2.1
      exact .intro baseRho baseLeftScope baseRightScope
        baseLeftJoins baseRightJoins foundLeftDecl foundRightDecl
        (by simpa [findJoinPoint?, leftDifferent] using leftFound)
        (by simpa [findJoinPoint?, rightDifferent] using rightFound)
        foundBody
        (.ignored
          (freshForScope_of_subset leftFresh leftSubset)
          (freshForScope_of_subset rightFresh rightSubset)
          foundJoins)
        foundEnvs foundRenaming foundJoinRenaming leftSubset rightSubset

/-- Impure alternatives agree on their selector and have related bodies. -/
inductive AltRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    {leftJoins rightJoins : List FVarId} :
    LCNF.Alt .impure → LCNF.Alt .impure → Prop where
  | ctor
      (code : CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftCode rightCode) :
      AltRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.ctorAlt info leftCode) (.ctorAlt info rightCode)
  | default
      (code : CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftCode rightCode) :
      AltRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.default leftCode) (.default rightCode)

abbrev AltsRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    {leftJoins rightJoins : List FVarId}
    (left right : List (LCNF.Alt .impure)) : Prop :=
  ListRel (AltRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
    rho leftScope rightScope) left right

/-- A table contains a constructor alternative selecting `code` for `tag`. -/
def HasCtorAlt (tag : Nat) (code : LCNF.Code .impure)
    (alts : List (LCNF.Alt .impure)) : Prop :=
  ∃ info, .ctorAlt info code ∈ alts ∧ info.cidx == tag

/-- A table contains `code` as a default alternative. -/
def HasDefaultAlt (code : LCNF.Code .impure)
    (alts : List (LCNF.Alt .impure)) : Prop :=
  .default code ∈ alts

/--
Every selector in a case table determines at most one branch body. Duplicate
alternatives are permitted when they select the same code.
-/
structure CaseTableDeterministic (alts : List (LCNF.Alt .impure)) : Prop where
  ctor : ∀ tag left right,
    HasCtorAlt tag left alts → HasCtorAlt tag right alts → left = right
  default : ∀ left right,
    HasDefaultAlt left alts → HasDefaultAlt right alts → left = right

/--
The exact phase invariant needed to move between interpreter order and Lean's
alpha-equivalence normalization. Quicksort's permutation property is now
proved generically, so callers provide only selector determinism.
-/
structure CaseTableNormalizationInvariant
    (alts : Array (LCNF.Alt .impure)) : Prop where
  deterministic : CaseTableDeterministic alts.toList

/-- Lean's alternative normalization is a permutation of the original table. -/
theorem sortAlts_perm (alts : Array (LCNF.Alt pu)) :
    alts.toList.Perm (LCNF.AlphaEqv.sortAlts alts).toList := by
  unfold LCNF.AlphaEqv.sortAlts
  exact (QSortPerm.qsort_perm alts _).symm.toList

/--
Saved continuations are related when they remember agreeing environments and
resume with related code under the binders they introduce. Apply and cache
frames carry no alpha-sensitive syntax yet and therefore agree literally.
-/
inductive FrameRelated : Frame → Frame → Prop where
  | bind
      {leftJoins rightJoins : List FVarId}
      (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
      (renamingScoped : RenamingScoped rho leftScope rightScope)
      (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
      (joinEnvs : JoinEnvsRelated rho leftScope rightScope
        leftJoins rightJoins leftJoinEnv rightJoinEnv)
      (leftFresh : FreshForScope leftId leftScope)
      (rightFresh : FreshForScope rightId rightScope)
      (leftJoinFresh : FreshForScope leftId leftJoins)
      (rightJoinFresh : FreshForScope rightId rightJoins)
      (continuation :
        CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
          (rho.insert rightId leftId)
          (leftId :: leftScope) (rightId :: rightScope)
          leftContinuation rightContinuation) :
      FrameRelated
        (.bind leftId leftContinuation leftEnv leftJoinEnv)
        (.bind rightId rightContinuation rightEnv rightJoinEnv)
  | apply (args : Array Value) :
      FrameRelated (.apply args) (.apply args)
  | cache (name : Name) :
      FrameRelated (.cache name) (.cache name)

abbrev FramesRelated (left right : List Frame) : Prop :=
  ListRel FrameRelated left right

/-- Applying the interpreter's extra-argument and nullary-cache frame policy
to related stacks preserves their relation. -/
theorem framesRelated_prepare_call
    (name : Name) (params : Array (LCNF.Param .impure))
    (args extraArgs : Array Value)
    (related : FramesRelated leftFrames rightFrames) :
    FramesRelated
      (let frames :=
        if extraArgs.isEmpty then leftFrames else .apply extraArgs :: leftFrames
       if params.isEmpty && args.isEmpty then .cache name :: frames else frames)
      (let frames :=
        if extraArgs.isEmpty then rightFrames else .apply extraArgs :: rightFrames
       if params.isEmpty && args.isEmpty then .cache name :: frames else frames) := by
  by_cases extraEmpty : extraArgs.isEmpty
  · by_cases cache : params.isEmpty && args.isEmpty
    · simpa [extraEmpty, cache] using
        ListRel.cons (FrameRelated.cache name) related
    · simpa [extraEmpty, cache] using related
  · by_cases cache : params.isEmpty && args.isEmpty
    · simpa [extraEmpty, cache] using
        ListRel.cons (FrameRelated.cache name)
          (ListRel.cons (FrameRelated.apply extraArgs) related)
    · simpa [extraEmpty, cache] using
        ListRel.cons (FrameRelated.apply extraArgs) related

/-- Call-frame preparation depends on a declaration's parameter array only
through its arity and emptiness. -/
theorem framesRelated_prepare_related_call
    (name : Name)
    (leftParams rightParams : Array (LCNF.Param .impure))
    (args extraArgs : Array Value)
    (sameSize : leftParams.size = rightParams.size)
    (related : FramesRelated leftFrames rightFrames) :
    FramesRelated
      (let frames :=
        if extraArgs.isEmpty then leftFrames else .apply extraArgs :: leftFrames
       if leftParams.isEmpty && args.isEmpty then .cache name :: frames else frames)
      (let frames :=
        if extraArgs.isEmpty then rightFrames else .apply extraArgs :: rightFrames
       if rightParams.isEmpty && args.isEmpty then .cache name :: frames else frames) := by
  have sameEmpty : leftParams.isEmpty = rightParams.isEmpty := by
    simp only [Array.isEmpty]
    rw [sameSize]
  simpa only [sameEmpty] using
    framesRelated_prepare_call name leftParams args extraArgs related

/-- Machine controls that carry equal runtime data or related residual code. -/
inductive ControlRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    {leftJoins rightJoins : List FVarId} : Control → Control → Prop where
  | code (related : CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right) :
      ControlRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope (.code left) (.code right)
  | yielded (value : Value) :
      ControlRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope (.yielded value) (.yielded value)
  | invokeName (name : Name) (args : Array Value) :
      ControlRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.invokeName name args) (.invokeName name args)
  | invokeValue (function : Value) (args : Array Value) :
      ControlRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope
        (.invokeValue function args) (.invokeValue function args)

/--
The state invariant used by the declarative simulation. Programs agree at
every named declaration boundary and runtime state is shared literally;
variable environments, join-point environments, frames, and code are related
structurally.
-/
structure MachineStateRelated (rho : FVarIdMap FVarId)
    (leftScope rightScope : List FVarId)
    {leftJoins rightJoins : List FVarId}
    (left right : MachineState) : Prop where
  programs : ProgramsRelated left.program right.program
  runtime_eq : left.runtime = right.runtime
  joins : JoinEnvsRelated rho leftScope rightScope
    leftJoins rightJoins left.joins right.joins
  frames : FramesRelated left.frames right.frames
  envs : EnvsAgree rho leftScope rightScope left.env right.env
  renaming_scoped : RenamingScoped rho leftScope rightScope
  join_renaming_scoped : RenamingScoped rho leftJoins rightJoins
  control : ControlRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
    rho leftScope rightScope left.control right.control

/-- Core-step results related by the machine invariant. -/
inductive CoreResultRelated : CoreResult → CoreResult → Prop where
  | next
      {leftJoins rightJoins : List FVarId}
      (related : MachineStateRelated
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope left right) :
      CoreResultRelated (.next left) (.next right)
  | external (request : ExternalRequest)
      {leftJoins rightJoins : List FVarId}
      (related : MachineStateRelated
        (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope left right) :
      CoreResultRelated (.external request left) (.external request right)
  | done (observation : Observation) :
      CoreResultRelated (.done observation) (.done observation)

theorem CoreResultRelated.done_right
    (related : CoreResultRelated (.done observation) rightResult) :
    rightResult = .done observation := by
  cases related
  rfl

/-- Successful constructor lookup identifies a matching table member. -/
theorem hasCtorAlt_of_findCtorAlt_eq_some
    (found : findCtorAlt tag alts = some code) : HasCtorAlt tag code alts := by
  induction alts with
  | nil => simp [findCtorAlt] at found
  | cons alt rest ih =>
      cases alt with
      | alt =>
          rename_i ctorName params head purity
          contradiction
      | ctorAlt =>
          rename_i ctorInfo head purity
          by_cases tagEq : ctorInfo.cidx = tag
          · simp [findCtorAlt, tagEq] at found
            subst code
            exact ⟨ctorInfo, by simp, by simpa using tagEq⟩
          · have tailFound : findCtorAlt tag rest = some code := by
              simpa [findCtorAlt, tagEq] using found
            rcases ih tailFound with ⟨selected, member, selectedTagEq⟩
            exact ⟨selected, by simp [member], selectedTagEq⟩
      | default =>
          rename_i head
          have tailFound : findCtorAlt tag rest = some code := by
            simpa [findCtorAlt] using found
          rcases ih tailFound with ⟨selected, member, selectedTagEq⟩
          exact ⟨selected, by simp [member], selectedTagEq⟩

/-- Failed constructor lookup excludes every matching table member. -/
theorem not_hasCtorAlt_of_findCtorAlt_eq_none
    (notFound : findCtorAlt tag alts = none) : ¬ HasCtorAlt tag code alts := by
  intro has
  induction alts with
  | nil => simp [HasCtorAlt] at has
  | cons alt rest ih =>
      cases alt with
      | alt =>
          rename_i ctorName params head purity
          contradiction
      | ctorAlt =>
          rename_i headInfo headCode purity
          by_cases headTag : headInfo.cidx = tag
          · simp [findCtorAlt, headTag] at notFound
          · have tailNotFound : findCtorAlt tag rest = none := by
              simpa [findCtorAlt, headTag] using notFound
            rcases has with ⟨selectedInfo, member, selectedTag⟩
            simp only [List.mem_cons] at member
            rcases member with member | member
            · have infoEq : selectedInfo = headInfo := by
                injection member
              subst selectedInfo
              exact headTag (by simpa using selectedTag)
            · exact ih tailNotFound ⟨selectedInfo, member, selectedTag⟩
      | default =>
          rename_i headCode
          have tailNotFound : findCtorAlt tag rest = none := by
            simpa [findCtorAlt] using notFound
          rcases has with ⟨selectedInfo, member, selectedTag⟩
          simp only [List.mem_cons] at member
          rcases member with member | member
          · contradiction
          · exact ih tailNotFound ⟨selectedInfo, member, selectedTag⟩

/-- Successful default lookup identifies a matching table member. -/
theorem hasDefaultAlt_of_findDefaultAlt_eq_some
    (found : findDefaultAlt alts = some code) : HasDefaultAlt code alts := by
  induction alts with
  | nil => simp [findDefaultAlt] at found
  | cons alt rest ih =>
      cases alt with
      | alt =>
          rename_i ctorName params head purity
          contradiction
      | ctorAlt =>
          have tailFound : findDefaultAlt rest = some code := by
            simpa [findDefaultAlt] using found
          exact by simpa [HasDefaultAlt] using ih tailFound
      | default =>
          rename_i head
          simp [findDefaultAlt] at found
          subst code
          simp [HasDefaultAlt]

/-- Failed default lookup excludes every default table member. -/
theorem not_hasDefaultAlt_of_findDefaultAlt_eq_none
    (notFound : findDefaultAlt alts = none) : ¬ HasDefaultAlt code alts := by
  intro has
  induction alts with
  | nil => simp [HasDefaultAlt] at has
  | cons alt rest ih =>
      cases alt with
      | alt =>
          rename_i ctorName params head purity
          contradiction
      | ctorAlt =>
          have tailNotFound : findDefaultAlt rest = none := by
            simpa [findDefaultAlt] using notFound
          have tailHas : HasDefaultAlt code rest := by
            simpa [HasDefaultAlt] using has
          exact ih tailNotFound tailHas
      | default => simp [findDefaultAlt] at notFound

/-- Constructor membership is invariant under table permutations. -/
theorem hasCtorAlt_iff_of_perm (permutation : left.Perm right) :
    HasCtorAlt tag code left ↔ HasCtorAlt tag code right := by
  constructor
  · rintro ⟨info, member, tagEq⟩
    exact ⟨info, permutation.mem_iff.mp member, tagEq⟩
  · rintro ⟨info, member, tagEq⟩
    exact ⟨info, permutation.mem_iff.mpr member, tagEq⟩

/-- Default membership is invariant under table permutations. -/
theorem hasDefaultAlt_iff_of_perm (permutation : left.Perm right) :
    HasDefaultAlt code left ↔ HasDefaultAlt code right := by
  exact permutation.mem_iff

/-- Constructor lookup is order-insensitive for deterministic case tables. -/
theorem findCtorAlt_eq_of_perm
    (deterministic : CaseTableDeterministic left)
    (permutation : left.Perm right) :
    findCtorAlt tag left = findCtorAlt tag right := by
  cases leftFound : findCtorAlt tag left with
  | none =>
      cases rightFound : findCtorAlt tag right with
      | none => rfl
      | some rightCode =>
          have rightHas := hasCtorAlt_of_findCtorAlt_eq_some rightFound
          have leftHas := (hasCtorAlt_iff_of_perm permutation).mpr rightHas
          exact (not_hasCtorAlt_of_findCtorAlt_eq_none leftFound leftHas).elim
  | some leftCode =>
      have leftHas := hasCtorAlt_of_findCtorAlt_eq_some leftFound
      cases rightFound : findCtorAlt tag right with
      | none =>
          have rightHas := (hasCtorAlt_iff_of_perm permutation).mp leftHas
          exact (not_hasCtorAlt_of_findCtorAlt_eq_none rightFound rightHas).elim
      | some rightCode =>
          have rightHas := hasCtorAlt_of_findCtorAlt_eq_some rightFound
          have rightHasLeft := (hasCtorAlt_iff_of_perm permutation).mpr rightHas
          rw [deterministic.ctor tag leftCode rightCode leftHas rightHasLeft]

/-- Default lookup is order-insensitive for deterministic case tables. -/
theorem findDefaultAlt_eq_of_perm
    (deterministic : CaseTableDeterministic left)
    (permutation : left.Perm right) :
    findDefaultAlt left = findDefaultAlt right := by
  cases leftFound : findDefaultAlt left with
  | none =>
      cases rightFound : findDefaultAlt right with
      | none => rfl
      | some rightCode =>
          have rightHas := hasDefaultAlt_of_findDefaultAlt_eq_some rightFound
          have leftHas := (hasDefaultAlt_iff_of_perm permutation).mpr rightHas
          exact (not_hasDefaultAlt_of_findDefaultAlt_eq_none leftFound leftHas).elim
  | some leftCode =>
      have leftHas := hasDefaultAlt_of_findDefaultAlt_eq_some leftFound
      cases rightFound : findDefaultAlt right with
      | none =>
          have rightHas := (hasDefaultAlt_iff_of_perm permutation).mp leftHas
          exact (not_hasDefaultAlt_of_findDefaultAlt_eq_none rightFound rightHas).elim
      | some rightCode =>
          have rightHas := hasDefaultAlt_of_findDefaultAlt_eq_some rightFound
          have rightHasLeft := (hasDefaultAlt_iff_of_perm permutation).mpr rightHas
          rw [deterministic.default leftCode rightCode leftHas rightHasLeft]

/-- Full case selection is invariant under deterministic table permutations. -/
theorem chooseAlt_eq_of_perm
    (deterministic : CaseTableDeterministic left)
    (permutation : left.Perm right) :
    chooseAlt tag left = chooseAlt tag right := by
  unfold chooseAlt
  rw [findCtorAlt_eq_of_perm deterministic permutation]
  rw [findDefaultAlt_eq_of_perm deterministic permutation]

/-- Lean's alternative normalization preserves interpreter selection. -/
theorem chooseAlt_sortAlts_eq
    (invariant : CaseTableNormalizationInvariant alts) :
    chooseAlt tag alts.toList =
      chooseAlt tag (LCNF.AlphaEqv.sortAlts alts).toList :=
  chooseAlt_eq_of_perm invariant.deterministic (sortAlts_perm alts)

/-- Optional selected branches agree structurally. -/
theorem findCtorAlt_related
    {leftJoins rightJoins : List FVarId}
    (related : AltsRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right) :
    CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (findCtorAlt tag left) (findCtorAlt tag right) := by
  induction related with
  | nil => exact .none
  | cons head tail tail_ih =>
      cases head with
      | ctor code =>
          rename_i leftCode rightCode info
          by_cases selected : info.cidx == tag
          · simpa [findCtorAlt, selected] using CaseSelectionRelated.some code
          · simpa [findCtorAlt, selected] using tail_ih
      | default code => simpa [findCtorAlt] using tail_ih

theorem findDefaultAlt_related
    {leftJoins rightJoins : List FVarId}
    (related : AltsRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right) :
    CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (findDefaultAlt left) (findDefaultAlt right) := by
  induction related with
  | nil => exact .none
  | cons head tail tail_ih =>
      cases head with
      | ctor code => simpa [findDefaultAlt] using tail_ih
      | default code =>
          simpa [findDefaultAlt] using CaseSelectionRelated.some code

/-- Related optional results remain related when the same fallback is used. -/
theorem caseSelectionRelated_orElse
    {left right leftFallback rightFallback : Option (LCNF.Code .impure)}
    {leftJoins rightJoins : List FVarId}
    (primary : CaseSelectionRelated
      (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right)
    (fallback :
      CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftFallback rightFallback) :
    CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (left.orElse fun _ => leftFallback)
      (right.orElse fun _ => rightFallback) := by
  cases primary with
  | none => exact fallback
  | some code => exact .some code

theorem chooseAlt_related
    {leftJoins rightJoins : List FVarId}
    (related : AltsRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right) :
    CaseSelectionRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (chooseAlt tag left) (chooseAlt tag right) := by
  unfold chooseAlt
  exact caseSelectionRelated_orElse
    (findCtorAlt_related (tag := tag) related)
    (findDefaultAlt_related related)

/-- `evalLetValue` observes only a state's program, runtime, and environment. -/
theorem evalLetValue_eq_of_state_fields
    (programs : ProgramsRelated left.program right.program)
    (runtimeEq : left.runtime = right.runtime)
    (envEq : left.env = right.env) :
    evalLetValue left declaration = evalLetValue right declaration := by
  rcases declaration with ⟨fvarId, binderName, type, value⟩
  cases value <;> simp only [evalLetValue, runtimeEq, envEq]
  case pap name args purity =>
    generalize leftFound : left.program.findDecl? name = leftDecl
    generalize rightFound : right.program.findDecl? name = rightDecl
    have lookup := programs name
    rw [leftFound, rightFound] at lookup
    cases leftDecl with
    | none =>
        cases rightDecl with
        | none => rfl
        | some rightDecl => cases lookup
    | some leftDecl =>
        cases rightDecl with
        | none => cases lookup
        | some rightDecl =>
            cases lookup with
            | some related =>
                simp only
                rw [related.arity_eq]

/-- Evaluate related declarations in two states satisfying the machine fields. -/
theorem evalLetValue_eq_of_related_states
    (programs : ProgramsRelated left.program right.program)
    (runtimeEq : left.runtime = right.runtime)
    (agree : EnvsAgree rho leftScope rightScope left.env right.env)
    (related : LetDeclValueRelated rho leftScope rightScope leftDecl rightDecl) :
    evalLetValue left leftDecl = evalLetValue right rightDecl := by
  calc
    evalLetValue left leftDecl =
        evalLetValue ({ left with env := right.env }) rightDecl := by
      simpa using evalLetValue_eq_of_related left agree related
    _ = evalLetValue right rightDecl := by
      exact evalLetValue_eq_of_state_fields
        (left := { left with env := right.env }) (right := right)
        programs runtimeEq rfl

theorem observe_eq_of_runtime_eq
    (runtimeEq : left.runtime = right.runtime) (outcome : Outcome) :
    observe left outcome = observe right outcome := by
  cases left
  cases right
  simp_all [observe]

/-- Continue with related code without changing either runtime. -/
theorem continuationResult_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftState.joins rightState.joins)
    (framesRelated : FramesRelated leftState.frames rightState.frames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
    (continuation :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftContinuation rightContinuation) :
    CoreResultRelated
      (.next { leftState with control := .code leftContinuation })
      (.next { rightState with control := .code rightContinuation }) :=
  .next {
    programs := programEq
    runtime_eq := runtimeEq
    joins := joinEnvs
    frames := framesRelated
    envs := agree
    renaming_scoped := renamingScoped
    join_renaming_scoped := joinRenamingScoped
    control := .code continuation
  }

/-- Lift one common runtime effect through related continuation states. -/
theorem runtimeEffectResult_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftState.joins rightState.joins)
    (framesRelated : FramesRelated leftState.frames rightState.frames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
    (continuation :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        rho leftScope rightScope leftContinuation rightContinuation)
    (effect : Except RuntimeFault RuntimeState) :
    CoreResultRelated
      (match effect with
      | .error fault => .done (observe leftState (.fault fault))
      | .ok nextRuntime =>
          .next { leftState with
            runtime := nextRuntime, control := .code leftContinuation })
      (match effect with
      | .error fault => .done (observe rightState (.fault fault))
      | .ok nextRuntime =>
          .next { rightState with
            runtime := nextRuntime, control := .code rightContinuation }) := by
  cases effect with
  | error fault =>
      simp only
      rw [observe_eq_of_runtime_eq
        (left := leftState) (right := rightState) runtimeEq (.fault fault)]
      exact .done _
  | ok nextRuntime =>
      simp only
      exact .next {
        programs := programEq
        runtime_eq := rfl
        joins := joinEnvs
        frames := framesRelated
        envs := agree
        renaming_scoped := renamingScoped
        join_renaming_scoped := joinRenamingScoped
        control := .code continuation
      }

/-- Every code head represented by `CodeRelated` has a one-step simulation. -/
def CoreStepSupported (_ _ : LCNF.Code .impure) : Prop := True

/--
One interpreter step preserves the declarative machine relation for every
code head, including join installation and invocation. The three successful let actions
either extend the current environments immediately or save the same extension
invariant in a pair of bind frames. Heap and ownership instructions run the
same runtime effect on both sides before entering related continuations.
-/
theorem coreStep_code_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftState.joins rightState.joins)
    (framesRelated : FramesRelated leftState.frames rightState.frames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
    (related : CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope leftCode rightCode)
    (supported : CoreStepSupported leftCode rightCode) :
    CoreResultRelated
      (coreStep { leftState with control := .code leftCode })
      (coreStep { rightState with control := .code rightCode }) := by
  cases related with
  | terminal terminal =>
      cases terminal with
      | ret fvarRelated =>
          obtain ⟨value, leftFound, rightFound⟩ :=
            agree _ fvarRelated.1 _ fvarRelated.2.1 fvarRelated.2.2
          have nextRelated :
              MachineStateRelated
                (leftJoins := leftJoins) (rightJoins := rightJoins)
                rho leftScope rightScope
                { leftState with control := .yielded value }
                { rightState with control := .yielded value } := {
            programs := programEq
            runtime_eq := runtimeEq
            joins := joinEnvs
            frames := framesRelated
            envs := agree
            renaming_scoped := renamingScoped
            join_renaming_scoped := joinRenamingScoped
            control := .yielded value
          }
          simpa [coreStep, lookupValue, leftFound, rightFound] using
            CoreResultRelated.next nextRelated
      | unreachable =>
          have observed := observe_eq_of_runtime_eq
            (left := leftState) (right := rightState) runtimeEq
            (.fault .unreachable)
          simp only [coreStep, fail]
          change CoreResultRelated
            (.done (observe leftState (.fault .unreachable)))
            (.done (observe rightState (.fault .unreachable)))
          rw [observed]
          exact .done _
  | letE declaration leftFresh rightFresh leftJoinFresh rightJoinFresh continuation =>
      rename_i leftDecl rightDecl leftContinuation rightContinuation
      have evaluated :
          evalLetValue
              { leftState with
                control := .code (.let leftDecl leftContinuation) }
              leftDecl =
            evalLetValue
              { rightState with
                control := .code (.let rightDecl rightContinuation) }
              rightDecl :=
        evalLetValue_eq_of_related_states programEq runtimeEq agree declaration
      simp only [coreStep]
      rw [evaluated]
      generalize rightEvaluation :
        evalLetValue
            { rightState with
              control := .code (.let rightDecl rightContinuation) }
            rightDecl = result
      cases result with
      | error fault =>
          have observed := observe_eq_of_runtime_eq
            (left := leftState) (right := rightState) runtimeEq (.fault fault)
          simp only [fail]
          change CoreResultRelated
            (.done (observe leftState (.fault fault)))
            (.done (observe rightState (.fault fault)))
          rw [observed]
          exact .done _
      | ok evaluated =>
          rcases evaluated with ⟨nextRuntime, action⟩
          cases action with
          | value value =>
              have nextRelated :
                  MachineStateRelated
                    (rho.insert rightDecl.fvarId leftDecl.fvarId)
                    (leftDecl.fvarId :: leftScope) (rightDecl.fvarId :: rightScope)
                    { leftState with
                      runtime := nextRuntime
                      env := bind leftState.env leftDecl.fvarId value
                      control := .code leftContinuation }
                    { rightState with
                      runtime := nextRuntime
                      env := bind rightState.env rightDecl.fvarId value
                      control := .code rightContinuation } := {
                programs := programEq
                runtime_eq := rfl
                joins := .bind joinEnvs renamingScoped joinRenamingScoped
                  leftFresh rightFresh leftJoinFresh rightJoinFresh
                frames := framesRelated
                envs := envsAgree_bind agree renamingScoped leftFresh rightFresh
                renaming_scoped := renamingScoped_insert renamingScoped rightFresh
                join_renaming_scoped :=
                  renamingScoped_insert_preserve joinRenamingScoped rightJoinFresh
                control := .code continuation
              }
              exact CoreResultRelated.next nextRelated
          | invokeName name args =>
              have bindFrameRelated :
                  FrameRelated
                    (.bind leftDecl.fvarId leftContinuation
                      leftState.env leftState.joins)
                    (.bind rightDecl.fvarId rightContinuation
                      rightState.env rightState.joins) :=
                .bind agree renamingScoped joinRenamingScoped joinEnvs
                  leftFresh rightFresh leftJoinFresh rightJoinFresh continuation
              have nextRelated :
                  MachineStateRelated
                    (leftJoins := leftJoins) (rightJoins := rightJoins)
                    rho leftScope rightScope
                    { leftState with
                      runtime := nextRuntime
                      frames := .bind leftDecl.fvarId leftContinuation
                        leftState.env leftState.joins :: leftState.frames
                      control := .invokeName name args }
                    { rightState with
                      runtime := nextRuntime
                      frames := .bind rightDecl.fvarId rightContinuation
                        rightState.env rightState.joins :: rightState.frames
                      control := .invokeName name args } := {
                programs := programEq
                runtime_eq := rfl
                joins := joinEnvs
                frames := .cons bindFrameRelated framesRelated
                envs := agree
                renaming_scoped := renamingScoped
                join_renaming_scoped := joinRenamingScoped
                control := .invokeName name args
              }
              simpa [pushBindFrame] using CoreResultRelated.next nextRelated
          | invokeValue function args =>
              have bindFrameRelated :
                  FrameRelated
                    (.bind leftDecl.fvarId leftContinuation
                      leftState.env leftState.joins)
                    (.bind rightDecl.fvarId rightContinuation
                      rightState.env rightState.joins) :=
                .bind agree renamingScoped joinRenamingScoped joinEnvs
                  leftFresh rightFresh leftJoinFresh rightJoinFresh continuation
              have nextRelated :
                  MachineStateRelated
                    (leftJoins := leftJoins) (rightJoins := rightJoins)
                    rho leftScope rightScope
                    { leftState with
                      runtime := nextRuntime
                      frames := .bind leftDecl.fvarId leftContinuation
                        leftState.env leftState.joins :: leftState.frames
                      control := .invokeValue function args }
                    { rightState with
                      runtime := nextRuntime
                      frames := .bind rightDecl.fvarId rightContinuation
                        rightState.env rightState.joins :: rightState.frames
                      control := .invokeValue function args } := {
                programs := programEq
                runtime_eq := rfl
                joins := joinEnvs
                frames := .cons bindFrameRelated framesRelated
                envs := agree
                renaming_scoped := renamingScoped
                join_renaming_scoped := joinRenamingScoped
                control := .invokeValue function args
              }
              simpa [pushBindFrame] using CoreResultRelated.next nextRelated
  | jp leftFresh rightFresh body continuation =>
      rename_i leftContinuation rightContinuation leftDecl rightDecl
      have nextRelated :
          MachineStateRelated
            (rho.insert rightDecl.fvarId leftDecl.fvarId)
            leftScope rightScope
            { leftState with
              joins := (leftDecl.fvarId, leftDecl) :: leftState.joins
              control := .code leftContinuation }
            { rightState with
              joins := (rightDecl.fvarId, rightDecl) :: rightState.joins
              control := .code rightContinuation } := {
        programs := programEq
        runtime_eq := runtimeEq
        joins := .join joinEnvs renamingScoped joinRenamingScoped
          leftFresh rightFresh body
        frames := framesRelated
        envs := envsAgree_insert_preserve agree rightFresh.variables
        renaming_scoped :=
          renamingScoped_insert_preserve renamingScoped rightFresh.variables
        join_renaming_scoped :=
          renamingScoped_insert joinRenamingScoped rightFresh.joins
        control := .code continuation
      }
      simpa [coreStep] using CoreResultRelated.next nextRelated
  | jmp target args =>
      rename_i leftTarget rightTarget leftArgs rightArgs
      rcases joinEnvs.lookup agree target with
        ⟨baseRho, baseLeftScope, baseRightScope, baseLeftJoins,
          baseRightJoins, leftDecl, rightDecl, leftFound, rightFound,
          body, historicalJoins, historicalAgree, historicalRenaming,
          historicalJoinRenaming, leftSubset, rightSubset⟩
      have evaluations := evalArgs_eq_of_related agree args
      have paramSizes : leftDecl.params.size = rightDecl.params.size := by
        simpa using body.length_eq
      simp only [coreStep]
      rw [leftFound, rightFound, evaluations]
      generalize rightEvaluation :
        evalArgs rightState.env rightArgs = argumentResult
      cases argumentResult with
      | error fault =>
          simp only [fail]
          rw [observe_eq_of_runtime_eq
            (left :=
              { leftState with control := .code (.jmp leftTarget leftArgs) })
            (right :=
              { rightState with control := .code (.jmp rightTarget rightArgs) })
            runtimeEq (.fault fault)]
          exact .done _
      | ok values =>
          simp only
          by_cases leftArity : leftDecl.params.size = values.size
          · have rightArity : rightDecl.params.size = values.size := by
              rw [← paramSizes]
              exact leftArity
            have valuesLength :
                values.toList.length = leftDecl.params.toList.length := by
              simpa using leftArity.symm
            rcases paramBody_bind_values_related body historicalAgree
                historicalRenaming historicalJoinRenaming historicalJoins
                valuesLength with
              ⟨finalRho, finalLeftScope, finalRightScope, leftBound,
                rightBound, leftFold, rightFold, finalAgree, finalRenaming,
                finalJoinRenaming, finalJoins, finalCode⟩
            have leftBind :
                bindParamsOver leftState.env leftDecl.params values =
                  .ok leftBound := by
              simp [bindParamsOver, leftArity]
              simpa only [bindParamValues] using leftFold
            have rightBind :
                bindParamsOver rightState.env rightDecl.params values =
                  .ok rightBound := by
              simp [bindParamsOver, rightArity]
              simpa only [bindParamValues] using rightFold
            rw [leftBind, rightBind]
            exact .next {
              programs := programEq
              runtime_eq := runtimeEq
              joins := finalJoins
              frames := framesRelated
              envs := finalAgree
              renaming_scoped := finalRenaming
              join_renaming_scoped := finalJoinRenaming
              control := .code finalCode
            }
          · have rightArity : rightDecl.params.size ≠ values.size := by
              intro rightArity
              exact leftArity (paramSizes.trans rightArity)
            have leftBind :
                bindParamsOver leftState.env leftDecl.params values =
                  .error (.arityMismatch leftDecl.params.size values.size) := by
              simp [bindParamsOver, leftArity]
            have rightBind :
                bindParamsOver rightState.env rightDecl.params values =
                  .error (.arityMismatch leftDecl.params.size values.size) := by
              simp [bindParamsOver, rightArity, paramSizes]
            rw [leftBind, rightBind]
            simp only [fail]
            rw [observe_eq_of_runtime_eq
              (left :=
                { leftState with control := .code (.jmp leftTarget leftArgs) })
              (right :=
                { rightState with control := .code (.jmp rightTarget rightArgs) })
              runtimeEq
              (.fault (.arityMismatch leftDecl.params.size values.size))]
            exact .done _
  | cases discr alternatives =>
      rename_i leftCases rightCases
      have discrEq := lookupValue_eq_of_scoped_related agree discr
      simp only [coreStep]
      rw [discrEq]
      generalize discrLookup : lookupValue rightState.env rightCases.discr = discrResult
      cases discrResult with
      | error fault =>
          simp only [fail]
          rw [observe_eq_of_runtime_eq
            (left := { leftState with control := .code (.cases leftCases) })
            (right := { rightState with control := .code (.cases rightCases) })
            runtimeEq (.fault fault)]
          exact .done _
      | ok discrValue =>
          simp only
          have tagEq :
              getTag leftState.runtime discrValue =
                getTag rightState.runtime discrValue := by
            rw [runtimeEq]
          rw [tagEq]
          generalize tagRead : getTag rightState.runtime discrValue = tagResult
          cases tagResult with
          | error fault =>
              simp only [fail]
              rw [observe_eq_of_runtime_eq
                (left := { leftState with control := .code (.cases leftCases) })
                (right := { rightState with control := .code (.cases rightCases) })
                runtimeEq (.fault fault)]
              exact .done _
          | ok tag =>
              simp only
              have selected := alternatives tag
              cases leftChoice : chooseAlt tag leftCases.alts.toList with
              | none =>
                  cases rightChoice : chooseAlt tag rightCases.alts.toList with
                  | none =>
                      simp only [fail]
                      rw [observe_eq_of_runtime_eq
                        (left :=
                          { leftState with control := .code (.cases leftCases) })
                        (right :=
                          { rightState with control := .code (.cases rightCases) })
                        runtimeEq (.fault .invalidCases)]
                      exact .done _
                  | some rightCode =>
                      have impossible :
                          CaseSelectionRelated
                            (leftJoins := leftJoins) (rightJoins := rightJoins)
                            rho leftScope rightScope
                            none (some rightCode) := by
                        simpa [leftChoice, rightChoice] using selected
                      cases impossible
              | some leftCode =>
                  cases rightChoice : chooseAlt tag rightCases.alts.toList with
                  | none =>
                      have impossible :
                          CaseSelectionRelated
                            (leftJoins := leftJoins) (rightJoins := rightJoins)
                            rho leftScope rightScope
                            (some leftCode) none := by
                        simpa [leftChoice, rightChoice] using selected
                      cases impossible
                  | some rightCode =>
                      have branches :
                          CaseSelectionRelated
                            (leftJoins := leftJoins) (rightJoins := rightJoins)
                            rho leftScope rightScope
                            (some leftCode) (some rightCode) := by
                        simpa [leftChoice, rightChoice] using selected
                      cases branches with
                      | some branch =>
                          simpa only [leftChoice, rightChoice] using
                            continuationResult_related leftState rightState
                              programEq runtimeEq joinEnvs framesRelated agree
                              renamingScoped joinRenamingScoped branch
  | oset object field continuation =>
      rename_i leftObject rightObject leftField rightField
        leftContinuation rightContinuation index
      have objectEq := lookupValue_eq_of_scoped_related agree object
      have fieldEq := evalArg_eq_of_related agree field
      simp only [coreStep]
      rw [objectEq, fieldEq, runtimeEq]
      generalize objectLookup : lookupValue rightState.env _ = objectResult
      generalize fieldLookup : evalArg rightState.env _ = fieldResult
      cases objectResult with
      | error fault =>
          simp only
          simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation (.error fault)
      | ok objectValue =>
          cases fieldResult with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok fieldValue =>
              simp
              generalize effectEq :
                setObjectField rightState.runtime objectValue index fieldValue = effect
              cases effect with
              | error fault =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.error fault)
              | ok nextRuntime =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.ok nextRuntime)
  | uset object field continuation =>
      rename_i leftObject rightObject leftField rightField
        leftContinuation rightContinuation index
      have objectEq := lookupValue_eq_of_scoped_related agree object
      have fieldEq := lookupValue_eq_of_scoped_related agree field
      simp only [coreStep]
      rw [objectEq, fieldEq, runtimeEq]
      generalize objectLookup : lookupValue rightState.env _ = objectResult
      generalize fieldLookup : lookupValue rightState.env _ = fieldResult
      cases objectResult with
      | error fault =>
          simp only
          simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation (.error fault)
      | ok objectValue =>
          cases fieldResult with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok fieldValue =>
              simp
              generalize effectEq :
                setUSizeSlot rightState.runtime objectValue index fieldValue = effect
              cases effect with
              | error fault =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.error fault)
              | ok nextRuntime =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.ok nextRuntime)
  | sset object field continuation =>
      rename_i leftObject rightObject leftField rightField
        leftContinuation rightContinuation width offset leftType rightType
      have objectEq := lookupValue_eq_of_scoped_related agree object
      have fieldEq := lookupValue_eq_of_scoped_related agree field
      simp only [coreStep]
      rw [objectEq, fieldEq, runtimeEq]
      generalize objectLookup : lookupValue rightState.env _ = objectResult
      generalize fieldLookup : lookupValue rightState.env _ = fieldResult
      cases objectResult with
      | error fault =>
          simp only
          simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation (.error fault)
      | ok objectValue =>
          cases fieldResult with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok fieldValue =>
              simp
              generalize effectEq :
                setScalarField rightState.runtime objectValue width offset fieldValue = effect
              cases effect with
              | error fault =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.error fault)
              | ok nextRuntime =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.ok nextRuntime)
  | setTag object continuation =>
      rename_i leftObject rightObject leftContinuation rightContinuation tag
      have objectEq := lookupValue_eq_of_scoped_related agree object
      simp only [coreStep]
      rw [objectEq, runtimeEq]
      generalize objectLookup : lookupValue rightState.env _ = objectResult
      cases objectResult with
      | error fault =>
          simp only
          simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation (.error fault)
      | ok objectValue =>
          simp
          generalize effectEq : setTag rightState.runtime objectValue tag = effect
          cases effect with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok nextRuntime =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.ok nextRuntime)
  | inc object continuation =>
      rename_i leftObject rightObject leftContinuation rightContinuation
        amount check persistent
      cases persistent with
      | false =>
          have objectEq := lookupValue_eq_of_scoped_related agree object
          simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
          rw [objectEq, runtimeEq]
          generalize objectLookup : lookupValue rightState.env _ = objectResult
          cases objectResult with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok objectValue =>
              simp
              generalize effectEq :
                incValue rightState.runtime objectValue amount check = effect
              cases effect with
              | error fault =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.error fault)
              | ok nextRuntime =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.ok nextRuntime)
      | true =>
          simpa [coreStep] using continuationResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation
  | dec object continuation =>
      rename_i leftObject rightObject leftContinuation rightContinuation
        amount check persistent objects
      cases persistent with
      | false =>
          have objectEq := lookupValue_eq_of_scoped_related agree object
          simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
          rw [objectEq, runtimeEq]
          generalize objectLookup : lookupValue rightState.env _ = objectResult
          cases objectResult with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok objectValue =>
              simp
              generalize effectEq :
                decValue rightState.runtime objectValue amount check = effect
              cases effect with
              | error fault =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.error fault)
              | ok nextRuntime =>
                  simp only
                  simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                    leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                    renamingScoped joinRenamingScoped continuation (.ok nextRuntime)
      | true =>
          simpa [coreStep] using continuationResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation
  | del object continuation =>
      rename_i leftObject rightObject leftContinuation rightContinuation
      have objectEq := lookupValue_eq_of_scoped_related agree object
      simp only [coreStep]
      rw [objectEq, runtimeEq]
      generalize objectLookup : lookupValue rightState.env _ = objectResult
      cases objectResult with
      | error fault =>
          simp only
          simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
            leftState rightState programEq runtimeEq joinEnvs framesRelated agree
            renamingScoped joinRenamingScoped continuation (.error fault)
      | ok objectValue =>
          simp
          generalize effectEq : deleteValue rightState.runtime objectValue = effect
          cases effect with
          | error fault =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.error fault)
          | ok nextRuntime =>
              simp only
              simpa [fail, observe, runtimeEq] using runtimeEffectResult_related
                leftState rightState programEq runtimeEq joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped continuation (.ok nextRuntime)

/-- A related pair of saved bind continuations resumes under the new binders. -/
theorem coreStep_yielded_bind_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (restFrames : FramesRelated leftFrames rightFrames)
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftJoinEnv rightJoinEnv)
    (leftFresh : FreshForScope leftId leftScope)
    (rightFresh : FreshForScope rightId rightScope)
    (leftJoinFresh : FreshForScope leftId leftJoins)
    (rightJoinFresh : FreshForScope rightId rightJoins)
    (continuation :
      CodeRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        (rho.insert rightId leftId)
        (leftId :: leftScope) (rightId :: rightScope)
        leftContinuation rightContinuation) :
    CoreResultRelated
      (coreStep
        { leftState with
          control := .yielded value
          frames := .bind leftId leftContinuation leftEnv leftJoinEnv :: leftFrames })
      (coreStep
        { rightState with
          control := .yielded value
          frames := .bind rightId rightContinuation rightEnv rightJoinEnv :: rightFrames }) := by
  have nextRelated :
      MachineStateRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
        (rho.insert rightId leftId)
        (leftId :: leftScope) (rightId :: rightScope)
        { leftState with
          control := .code leftContinuation
          env := bind leftEnv leftId value
          joins := leftJoinEnv
          frames := leftFrames }
        { rightState with
          control := .code rightContinuation
          env := bind rightEnv rightId value
          joins := rightJoinEnv
          frames := rightFrames } := {
    programs := programEq
    runtime_eq := runtimeEq
    joins := .bind joinEnvs renamingScoped joinRenamingScoped
      leftFresh rightFresh leftJoinFresh rightJoinFresh
    frames := restFrames
    envs := envsAgree_bind agree renamingScoped leftFresh rightFresh
    renaming_scoped := renamingScoped_insert renamingScoped rightFresh
    join_renaming_scoped :=
      renamingScoped_insert_preserve joinRenamingScoped rightJoinFresh
    control := .code continuation
  }
  simpa [coreStep] using CoreResultRelated.next nextRelated

/-- Yielded values pop every kind of related continuation frame in lockstep. -/
theorem coreStep_yielded_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftState.joins rightState.joins)
    (framesRelated : FramesRelated leftFrames rightFrames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins) :
    CoreResultRelated
      (coreStep { leftState with control := .yielded value, frames := leftFrames })
      (coreStep { rightState with control := .yielded value, frames := rightFrames }) := by
  cases framesRelated with
  | nil =>
      simp only [coreStep]
      rw [observe_eq_of_runtime_eq
        (left := { leftState with control := .yielded value, frames := [] })
        (right := { rightState with control := .yielded value, frames := [] })
        runtimeEq (.returned value)]
      exact .done _
  | cons frame rest =>
      cases frame with
      | bind savedAgree savedRenaming savedJoinRenaming savedJoins
          leftFresh rightFresh leftJoinFresh rightJoinFresh continuation =>
          exact coreStep_yielded_bind_related leftState rightState
            programEq runtimeEq rest savedAgree savedRenaming savedJoinRenaming
            savedJoins leftFresh rightFresh leftJoinFresh rightJoinFresh continuation
      | apply args =>
          have nextRelated :
              MachineStateRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
                rho leftScope rightScope
                { leftState with
                  control := .invokeValue value args, frames := _ }
                { rightState with
                  control := .invokeValue value args, frames := _ } := {
            programs := programEq
            runtime_eq := runtimeEq
            joins := joinEnvs
            frames := rest
            envs := agree
            renaming_scoped := renamingScoped
            join_renaming_scoped := joinRenamingScoped
            control := .invokeValue value args
          }
          simpa [coreStep] using CoreResultRelated.next nextRelated
      | cache name =>
          have nextRelated :
              MachineStateRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
                rho leftScope rightScope
                { leftState with
                  runtime := leftState.runtime.setGlobal name value
                  control := .yielded value, frames := _ }
                { rightState with
                  runtime := rightState.runtime.setGlobal name value
                  control := .yielded value, frames := _ } := {
            programs := programEq
            runtime_eq := congrArg (fun runtime => runtime.setGlobal name value) runtimeEq
            joins := joinEnvs
            frames := rest
            envs := agree
            renaming_scoped := renamingScoped
            join_renaming_scoped := joinRenamingScoped
            control := .yielded value
          }
          simpa [coreStep] using CoreResultRelated.next nextRelated

/-- Empty lexical scopes agree for arbitrary environments. -/
theorem envsAgree_empty_scopes (rho : FVarIdMap FVarId)
    (left right : Env) : EnvsAgree rho [] [] left right := by
  intro leftId leftScoped
  simp at leftScoped

/--
Invoking the same named declaration from related states produces related
partial applications, body entries, external requests, and faults. The body
premise is the explicit phase bridge needed when control enters a declaration
that was not traversed by the current local alpha check.
-/
theorem invokeDecl_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftState.joins rightState.joins)
    (framesRelated : FramesRelated leftState.frames rightState.frames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins)
    (waitingControl : ControlRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) [] [] leftState.control rightState.control) :
    CoreResultRelated
      (invokeDecl leftState name args) (invokeDecl rightState name args) := by
  unfold invokeDecl
  generalize leftFound : leftState.program.findDecl? name = leftDeclaration
  generalize rightFound : rightState.program.findDecl? name = rightDeclaration
  have lookup := programEq name
  rw [leftFound, rightFound] at lookup
  cases leftDeclaration with
  | none =>
      cases rightDeclaration with
      | none =>
          simp only [fail]
          rw [observe_eq_of_runtime_eq (left := leftState) (right := rightState)
            runtimeEq (.fault (.unknownDecl name))]
          exact .done _
      | some rightDeclaration => cases lookup
  | some leftDeclaration =>
      cases rightDeclaration with
      | none => cases lookup
      | some rightDeclaration =>
          cases lookup with
          | some declarations =>
              simp only
              have sameSize := declarations.arity_eq
              by_cases tooFew : args.size < leftDeclaration.params.size
              · have rightTooFew : args.size < rightDeclaration.params.size := by
                  simpa only [sameSize] using tooFew
                rw [if_pos tooFew, if_pos rightTooFew, runtimeEq, ← sameSize]
                generalize allocation :
                  alloc rightState.runtime
                    (.closure name leftDeclaration.params.size args) = allocated
                rcases allocated with ⟨nextRuntime, reference⟩
                exact .next {
                  programs := programEq
                  runtime_eq := rfl
                  joins := joinEnvs
                  frames := framesRelated
                  envs := agree
                  renaming_scoped := renamingScoped
                  join_renaming_scoped := joinRenamingScoped
                  control := .yielded (.object reference)
                }
              · have rightNotTooFew : ¬ args.size < rightDeclaration.params.size := by
                  simpa only [sameSize] using tooFew
                rw [if_neg tooFew, if_neg rightNotTooFew]
                let callArgs := args.extract 0 leftDeclaration.params.size
                let extraArgs := args.extract leftDeclaration.params.size args.size
                let leftPreparedFrames :=
                  let frames := if extraArgs.isEmpty then leftState.frames
                    else .apply extraArgs :: leftState.frames
                  if leftDeclaration.params.isEmpty && args.isEmpty then
                    .cache name :: frames else frames
                let rightPreparedFrames :=
                  let frames := if extraArgs.isEmpty then rightState.frames
                    else .apply extraArgs :: rightState.frames
                  if rightDeclaration.params.isEmpty && args.isEmpty then
                    .cache name :: frames else frames
                have preparedFrames :
                    FramesRelated leftPreparedFrames rightPreparedFrames := by
                  exact framesRelated_prepare_related_call name
                    leftDeclaration.params rightDeclaration.params args extraArgs
                    sameSize framesRelated
                generalize leftBinding :
                  bindParams leftDeclaration.params callArgs = bound
                cases bound with
                | error fault =>
                    have rightBinding :
                        bindParams rightDeclaration.params callArgs = .error fault :=
                      bindParams_error_of_size_eq sameSize leftBinding
                    have rightBindingActual :
                        bindParams rightDeclaration.params
                          (args.extract 0 rightDeclaration.params.size) =
                            .error fault := by
                      simpa [callArgs, sameSize] using rightBinding
                    simp only [rightBindingActual, fail]
                    rw [observe_eq_of_runtime_eq
                      (left := leftState) (right := rightState)
                      runtimeEq (.fault fault)]
                    exact .done _
                | ok leftEnv =>
                    have boundData := bindParams_data_of_ok leftBinding
                    cases declarations with
                    | code leftDecl rightDecl leftCode rightCode body =>
                        rcases paramBody_bind_values_related body
                            (envsAgree_empty_scopes
                              ({} : FVarIdMap FVarId) [] [])
                            (renamingScoped_empty []) (renamingScoped_empty [])
                            (JoinEnvsRelated.empty (left := []) (right := []))
                            boundData.2 with
                          ⟨finalRho, finalLeftScope, finalRightScope, leftBound,
                            rightBound, leftFold, rightFold, finalAgree,
                            finalRenaming, finalJoinRenaming, finalJoins, finalCode⟩
                        have leftBoundEq : leftBound = leftEnv :=
                          leftFold.symm.trans boundData.1
                        subst leftBound
                        have rightSize : rightDecl.params.size = callArgs.size := by
                          have rightLength := body.length_eq.symm.trans
                            boundData.2.symm
                          simpa using rightLength
                        have rightBinding :
                            bindParams rightDecl.params callArgs = .ok rightBound := by
                          have foldOk :
                              (Except.ok (bindParamValues [] rightDecl.params.toList
                                callArgs.toList) : Except RuntimeFault Env) =
                                .ok rightBound :=
                            congrArg
                              (fun env => (Except.ok env : Except RuntimeFault Env))
                              rightFold
                          simpa [bindParams, rightSize, bindParamValues] using foldOk
                        have rightBindingActual :
                            bindParams rightDecl.params
                              (args.extract 0 rightDecl.params.size) =
                                .ok rightBound := by
                          simpa [callArgs, sameSize] using rightBinding
                        have finalAgreeEnv :
                            EnvsAgree finalRho finalLeftScope finalRightScope
                              leftEnv rightBound := by
                          simpa only [boundData.1] using finalAgree
                        have nextRelated :
                            MachineStateRelated
                              (leftJoins := []) (rightJoins := [])
                              finalRho finalLeftScope finalRightScope
                              { leftState with
                                env := leftEnv
                                joins := []
                                frames := leftPreparedFrames
                                control := .code leftCode }
                              { rightState with
                                env := rightBound
                                joins := []
                                frames := rightPreparedFrames
                                control := .code rightCode } := {
                          programs := programEq
                          runtime_eq := runtimeEq
                          joins := finalJoins
                          frames := preparedFrames
                          envs := finalAgreeEnv
                          renaming_scoped := finalRenaming
                          join_renaming_scoped := finalJoinRenaming
                          control := .code finalCode
                        }
                        simpa [callArgs, extraArgs, leftPreparedFrames,
                          rightPreparedFrames, sameSize, leftBinding,
                          rightBindingActual] using CoreResultRelated.next nextRelated
                    | extern leftDecl rightDecl leftMetadata rightMetadata
                        arityEq paramTypesEq resultTypeEq =>
                        let rightEnv := bindParamValues []
                          rightDecl.params.toList callArgs.toList
                        have rightSize : rightDecl.params.size = callArgs.size := by
                          have leftLength :
                              callArgs.toList.length = leftDecl.params.toList.length :=
                            boundData.2
                          simpa [arityEq] using leftLength.symm
                        have rightBinding :
                            bindParams rightDecl.params callArgs = .ok rightEnv := by
                          simp [rightEnv, bindParams, rightSize, bindParamValues]
                        have rightBindingActual :
                            bindParams rightDecl.params
                              (args.extract 0 rightDecl.params.size) =
                                .ok rightEnv := by
                          simpa [callArgs, sameSize] using rightBinding
                        have nextRelated :
                            MachineStateRelated (leftJoins := []) (rightJoins := [])
                              ({} : FVarIdMap FVarId) [] []
                              { leftState with
                                env := leftEnv
                                joins := []
                                frames := leftPreparedFrames }
                              { rightState with
                                env := rightEnv
                                joins := []
                                frames := rightPreparedFrames } := {
                          programs := programEq
                          runtime_eq := runtimeEq
                          joins := .empty
                          frames := preparedFrames
                          envs := envsAgree_empty_scopes
                            ({} : FVarIdMap FVarId) leftEnv rightEnv
                          renaming_scoped := renamingScoped_empty []
                          join_renaming_scoped := renamingScoped_empty []
                          control := waitingControl
                        }
                        simpa [callArgs, extraArgs, leftPreparedFrames,
                          rightPreparedFrames, arityEq, leftBinding, rightBinding,
                          rightBindingActual,
                          paramTypesEq, resultTypeEq] using
                          CoreResultRelated.external
                            (request := {
                              name
                              paramTypes := leftDecl.params.map (·.type)
                              resultType := leftDecl.type
                              args := callArgs }) nextRelated

/-- Closure invocation performs the same ownership transition in equal runtimes
and delegates to the related named-declaration simulation on the returned state. -/
theorem invokeClosure_related
    {leftJoins rightJoins : List FVarId}
    (leftState rightState : MachineState)
    (programEq : ProgramsRelated leftState.program rightState.program)
    (runtimeEq : leftState.runtime = rightState.runtime)
    (joinEnvs : JoinEnvsRelated rho leftScope rightScope
      leftJoins rightJoins leftState.joins rightState.joins)
    (framesRelated : FramesRelated leftState.frames rightState.frames)
    (agree : EnvsAgree rho leftScope rightScope leftState.env rightState.env)
    (renamingScoped : RenamingScoped rho leftScope rightScope)
    (joinRenamingScoped : RenamingScoped rho leftJoins rightJoins) :
    CoreResultRelated
      (invokeClosure
        { leftState with control := .invokeValue function args } function args)
      (invokeClosure
        { rightState with control := .invokeValue function args } function args) := by
  let leftInvoke := { leftState with control := .invokeValue function args }
  let rightInvoke := { rightState with control := .invokeValue function args }
  have failRelated (fault : RuntimeFault) :
      CoreResultRelated (fail leftInvoke fault) (fail rightInvoke fault) := by
    unfold fail
    rw [observe_eq_of_runtime_eq (left := leftInvoke) (right := rightInvoke)
      runtimeEq (.fault fault)]
    exact .done _
  unfold invokeClosure
  cases function with
  | object reference =>
      cases reference with
      | tagged payload =>
          simp only
          exact failRelated .expectedClosure
      | heap location =>
          simp only
          have applicationEq :
              takeClosureApplication leftState.runtime location =
                takeClosureApplication rightState.runtime location :=
            congrArg
              (fun runtime => takeClosureApplication runtime location) runtimeEq
          rw [applicationEq]
          generalize applicationRead :
            takeClosureApplication rightState.runtime location = result
          cases result with
          | error fault =>
              simp only
              exact failRelated fault
          | ok application =>
              rcases application with ⟨runtime, name, arity, fixed⟩
              simp only
              exact invokeDecl_related
                { leftInvoke with runtime }
                { rightInvoke with runtime }
                programEq rfl joinEnvs framesRelated agree
                renamingScoped joinRenamingScoped
                (.invokeValue (.object (.heap location)) args)
  | usize value =>
      simp only
      exact failRelated .expectedClosure
  | scalar value =>
      simp only
      exact failRelated .expectedClosure
  | erased =>
      simp only
      exact failRelated .expectedClosure
  | reuseToken location =>
      simp only
      exact failRelated .expectedClosure

/-- Every interpreter control step preserves the machine relation, assuming
the shared program exposes related declaration bodies at named-call entries. -/
theorem coreStep_machine_related
    {leftJoins rightJoins : List FVarId}
    (related : MachineStateRelated (leftJoins := leftJoins)
      (rightJoins := rightJoins) rho leftScope rightScope leftState rightState) :
    CoreResultRelated (coreStep leftState) (coreStep rightState) := by
  let leftMachine := leftState
  let rightMachine := rightState
  cases leftState
  cases rightState
  rcases related with
    ⟨programEq, runtimeEq, joinEnvs, framesRelated, agree,
      renamingScoped, joinRenamingScoped, control⟩
  cases control with
  | code code =>
      exact coreStep_code_related leftMachine rightMachine programEq runtimeEq
        joinEnvs framesRelated agree renamingScoped joinRenamingScoped code trivial
  | yielded value =>
      exact coreStep_yielded_related leftMachine rightMachine programEq runtimeEq
        joinEnvs framesRelated agree renamingScoped joinRenamingScoped
  | invokeName name args =>
      by_cases argsEmpty : args.isEmpty
      · simp only [coreStep, argsEmpty]
        have globalEq :
            findGlobal? leftMachine.runtime.globals name =
              findGlobal? rightMachine.runtime.globals name :=
          congrArg (fun runtime => findGlobal? runtime.globals name) runtimeEq
        rw [globalEq]
        generalize globalRead :
          findGlobal? rightMachine.runtime.globals name = global
        cases global with
        | none =>
            exact invokeDecl_related leftMachine rightMachine programEq runtimeEq
              joinEnvs framesRelated agree renamingScoped joinRenamingScoped
              (.invokeName name args)
        | some value =>
            exact .next {
              programs := programEq
              runtime_eq := runtimeEq
              joins := joinEnvs
              frames := framesRelated
              envs := agree
              renaming_scoped := renamingScoped
              join_renaming_scoped := joinRenamingScoped
              control := .yielded value
            }
      · simp only [coreStep, argsEmpty]
        exact invokeDecl_related leftMachine rightMachine programEq runtimeEq
          joinEnvs framesRelated agree renamingScoped joinRenamingScoped
          (.invokeName name args)
  | invokeValue function args =>
      simpa only [coreStep] using
        invokeClosure_related leftMachine rightMachine programEq runtimeEq
          joinEnvs framesRelated agree renamingScoped joinRenamingScoped

/-- Existential closure of the indexed machine relation for step-level use. -/
def StatesRelated (left right : MachineState) : Prop :=
  ∃ rho leftScope rightScope leftJoins rightJoins,
    MachineStateRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope left right

theorem StatesRelated.programs (related : StatesRelated left right) :
    ProgramsRelated left.program right.program := by
  rcases related with
    ⟨rho, leftScope, rightScope, leftJoins, rightJoins, indexed⟩
  exact indexed.programs

/-- A proof-facing bisimulation packages simulations in both alpha-renaming
directions; each direction may use its own renaming and scope indices. -/
structure StatesBisimilar (left right : MachineState) : Prop where
  forward : StatesRelated left right
  backward : StatesRelated right left

/-- A core result never changes the program stored in its successor/waiter. -/
def CoreResult.PreservesProgram (program : ImpureProgram) : CoreResult → Prop
  | .next state => state.program = program
  | .external _ waiting => waiting.program = program
  | .done _ => True

theorem invokeDecl_preserves_program (state : MachineState) (name : Name)
    (args : Array Value) :
    CoreResult.PreservesProgram state.program (invokeDecl state name args) := by
  unfold invokeDecl
  generalize found : state.program.findDecl? name = declaration
  cases declaration with
  | none => trivial
  | some decl =>
      by_cases tooFew : args.size < decl.params.size
      · simp only [tooFew, ↓reduceIte]
        rfl
      · simp only [tooFew, ↓reduceIte]
        let callArgs := args.extract 0 decl.params.size
        generalize binding : bindParams decl.params callArgs = bound
        cases bound with
        | error fault => trivial
        | ok env =>
            simp only
            cases decl.value <;> rfl

theorem invokeClosure_preserves_program (state : MachineState)
    (function : Value) (args : Array Value) :
    CoreResult.PreservesProgram state.program
      (invokeClosure state function args) := by
  unfold invokeClosure
  cases function with
  | object reference =>
      cases reference with
      | tagged payload =>
          simp only
          trivial
      | heap location =>
          simp only
          generalize applicationRead :
            takeClosureApplication state.runtime location = result
          cases result with
          | error fault => trivial
          | ok application =>
              rcases application with ⟨runtime, name, arity, fixed⟩
              simp only
              exact invokeDecl_preserves_program
                { state with runtime } name (fixed ++ args)
  | usize value =>
      simp only
      trivial
  | scalar value =>
      simp only
      trivial
  | erased =>
      simp only
      trivial
  | reuseToken location =>
      simp only
      trivial

theorem coreStep_preserves_program (state : MachineState) :
    CoreResult.PreservesProgram state.program (coreStep state) := by
  cases state with
  | mk program control env joins frames runtime =>
      cases control with
      | yielded value =>
          cases frames with
          | nil => trivial
          | cons frame rest =>
              cases frame <;> rfl
      | invokeName name args =>
          by_cases argsEmpty : args.isEmpty
          · simp only [coreStep, argsEmpty, ↓reduceIte]
            generalize globalRead : findGlobal? runtime.globals name = global
            cases global with
            | some value => rfl
            | none =>
                exact invokeDecl_preserves_program
                  { program, control := .invokeName name args, env, joins,
                    frames, runtime } name args
          · simp only [coreStep, argsEmpty]
            exact invokeDecl_preserves_program
              { program, control := .invokeName name args, env, joins,
                frames, runtime } name args
      | invokeValue function args =>
          exact invokeClosure_preserves_program
            { program, control := .invokeValue function args, env, joins,
              frames, runtime } function args
      | code code =>
          cases code with
          | «let» decl continuation =>
              simp only [coreStep]
              generalize evaluation :
                evalLetValue
                  { program, control := .code (.let decl continuation), env,
                    joins, frames, runtime } decl = result
              cases result with
              | error fault => trivial
              | ok evaluated =>
                  rcases evaluated with ⟨nextRuntime, action⟩
                  cases action <;> rfl
          | «fun» decl continuation impossible => contradiction
          | jp decl continuation => rfl
          | jmp target args =>
              simp only [coreStep]
              generalize joinRead : findJoinPoint? joins target = found
              cases found with
              | none => trivial
              | some decl =>
                  simp only
                  generalize evaluation : evalArgs env args = result
                  cases result with
                  | error fault => trivial
                  | ok values =>
                      simp only
                      generalize binding : bindParamsOver env decl.params values = bound
                      cases bound <;> simp only <;> trivial
          | «cases» caseInfo =>
              simp only [coreStep]
              generalize discrRead : lookupValue env caseInfo.discr = discrResult
              cases discrResult with
              | error fault => trivial
              | ok discr =>
                  simp only
                  generalize tagRead : getTag runtime discr = tagResult
                  cases tagResult with
                  | error fault =>
                      simp only
                      trivial
                  | ok tag =>
                      simp only
                      generalize selected : chooseAlt tag caseInfo.alts.toList = branch
                      cases branch <;> simp only <;> trivial
          | «return» result =>
              simp only [coreStep]
              generalize valueRead : lookupValue env result = valueResult
              cases valueResult <;> trivial
          | unreach type => trivial
          | oset object index field continuation =>
              simp only [coreStep]
              generalize objectRead : lookupValue env object = objectResult
              generalize fieldRead : evalArg env field = fieldResult
              cases objectResult <;> cases fieldResult
              all_goals try trivial
              rename_i objectValue fieldValue
              simp only
              generalize effect :
                setObjectField runtime objectValue index fieldValue = effectResult
              cases effectResult <;> simp only <;> trivial
          | uset object index field continuation =>
              simp only [coreStep]
              generalize objectRead : lookupValue env object = objectResult
              generalize fieldRead : lookupValue env field = fieldResult
              cases objectResult <;> cases fieldResult
              all_goals try trivial
              rename_i objectValue fieldValue
              simp only
              generalize effect :
                setUSizeSlot runtime objectValue index fieldValue = effectResult
              cases effectResult <;> simp only <;> trivial
          | sset object width offset field type continuation =>
              simp only [coreStep]
              generalize objectRead : lookupValue env object = objectResult
              generalize fieldRead : lookupValue env field = fieldResult
              cases objectResult <;> cases fieldResult
              all_goals try trivial
              rename_i objectValue fieldValue
              simp only
              generalize effect :
                setScalarField runtime objectValue width offset fieldValue = effectResult
              cases effectResult <;> simp only <;> trivial
          | setTag object tag continuation =>
              simp only [coreStep]
              generalize objectRead : lookupValue env object = objectResult
              cases objectResult with
              | error fault => trivial
              | ok objectValue =>
                  simp only
                  generalize effect : setTag runtime objectValue tag = effectResult
                  cases effectResult <;> simp only <;> trivial
          | inc object amount check persistent continuation =>
              cases persistent with
              | true => rfl
              | false =>
                  simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
                  generalize objectRead : lookupValue env object = objectResult
                  cases objectResult with
                  | error fault => trivial
                  | ok objectValue =>
                      simp only
                      generalize effect :
                        incValue runtime objectValue amount check = effectResult
                      cases effectResult <;> simp only <;> trivial
          | dec object amount check persistent objects continuation =>
              cases persistent with
              | true => rfl
              | false =>
                  simp only [coreStep, Bool.false_eq_true, ↓reduceIte]
                  generalize objectRead : lookupValue env object = objectResult
                  cases objectResult with
                  | error fault => trivial
                  | ok objectValue =>
                      simp only
                      generalize effect :
                        decValue runtime objectValue amount check = effectResult
                      cases effectResult <;> simp only <;> trivial
          | del object continuation =>
              simp only [coreStep]
              generalize objectRead : lookupValue env object = objectResult
              cases objectResult with
              | error fault => trivial
              | ok objectValue =>
                  simp only
                  generalize effect : deleteValue runtime objectValue = effectResult
                  cases effectResult <;> simp only <;> trivial

theorem coreStep_next_program
    (transition : coreStep before = .next after) :
    after.program = before.program := by
  have preserved := coreStep_preserves_program before
  rw [transition] at preserved
  exact preserved

theorem coreStep_external_program
    (transition : coreStep before = .external request waiting) :
    waiting.program = before.program := by
  have preserved := coreStep_preserves_program before
  rw [transition] at preserved
  exact preserved

/-- Semantic steps preserve the immutable program component. -/
theorem step_preserves_program (step : Step externals before after) :
    after.program = before.program := by
  cases step with
  | internal transition => exact coreStep_next_program transition
  | external transition external =>
      simpa [resumeExternal, MachineState.withValue] using
        coreStep_external_program transition

/-- A finite semantic execution preserves the immutable program component. -/
theorem steps_preserve_program (steps : Steps externals count before after) :
    after.program = before.program := by
  induction steps with
  | refl state => rfl
  | step head tail ih => exact ih.trans (step_preserves_program head)

/-- Resuming the same external response preserves a related waiting state. -/
theorem resumeExternal_related
    {leftJoins rightJoins : List FVarId}
    (related : MachineStateRelated (leftJoins := leftJoins)
      (rightJoins := rightJoins) rho leftScope rightScope leftWaiting rightWaiting) :
    MachineStateRelated (leftJoins := leftJoins) (rightJoins := rightJoins)
      rho leftScope rightScope
      (resumeExternal request leftWaiting response)
      (resumeExternal request rightWaiting response) := by
  rcases related with
    ⟨programEq, runtimeEq, joinEnvs, framesRelated, agree,
      renamingScoped, joinRenamingScoped, control⟩
  exact {
    programs := programEq
    runtime_eq := by
      simp [resumeExternal, MachineState.withValue, runtimeEq]
    joins := joinEnvs
    frames := framesRelated
    envs := agree
    renaming_scoped := renamingScoped
    join_renaming_scoped := joinRenamingScoped
    control := .yielded response.value
  }

/-- One left semantic step can be matched by one right semantic step. -/
theorem step_forward
    {leftJoins rightJoins : List FVarId}
    (related : MachineStateRelated (leftJoins := leftJoins)
      (rightJoins := rightJoins) rho leftScope rightScope leftBefore rightBefore)
    (step : Step externals leftBefore leftAfter) :
    ∃ rightAfter, Step externals rightBefore rightAfter ∧
      StatesRelated leftAfter rightAfter := by
  have results := coreStep_machine_related related
  generalize rightTransition : coreStep rightBefore = rightResult at results
  cases step with
  | internal transition =>
      rw [transition] at results
      cases results with
      | next nextRelated =>
          exact ⟨_, .internal rightTransition,
            ⟨_, _, _, _, _, nextRelated⟩⟩
  | external transition external =>
      rw [transition] at results
      cases results with
      | external request waitingRelated =>
          have rightExternal := external
          rw [related.runtime_eq] at rightExternal
          exact ⟨_, .external rightTransition rightExternal,
            ⟨_, _, _, _, _, resumeExternal_related waitingRelated⟩⟩

/-- Every finite left execution has a same-length related right execution. -/
theorem steps_forward
    (related : StatesRelated leftBefore rightBefore)
    (steps : Steps externals count leftBefore leftAfter) :
    ∃ rightAfter, Steps externals count rightBefore rightAfter ∧
      StatesRelated leftAfter rightAfter := by
  induction steps generalizing rightBefore with
  | refl state => exact ⟨rightBefore, .refl rightBefore, related⟩
  | step head tail ih =>
      rcases related with
        ⟨rho, leftScope, rightScope, leftJoins, rightJoins, indexed⟩
      rcases step_forward indexed head with
        ⟨rightSecond, rightHead, secondRelated⟩
      rcases ih secondRelated with
        ⟨rightAfter, rightTail, finalRelated⟩
      exact ⟨rightAfter, .step rightHead rightTail, finalRelated⟩

/-- Terminating observations of a related left state are reproduced on the
right with the same number of semantic steps. -/
theorem evaluatesState_forward
    (related : StatesRelated leftBefore rightBefore) :
    EvaluatesState externals leftBefore observation →
      EvaluatesState externals rightBefore observation := by
  rintro ⟨count, leftFinal, leftSteps, leftDone⟩
  rcases steps_forward related leftSteps with
    ⟨rightFinal, rightSteps, finalRelated⟩
  rcases finalRelated with
    ⟨rho, leftScope, rightScope, leftJoins, rightJoins, indexed⟩
  have finalResults :
      CoreResultRelated (.done observation) (coreStep rightFinal) := by
    simpa only [leftDone] using coreStep_machine_related indexed
  exact ⟨count, rightFinal, rightSteps, finalResults.done_right⟩

/-- Divergence of a related left state is reproduced on the right. -/
theorem diverges_forward
    (related : StatesRelated leftBefore rightBefore)
    (diverges : Diverges externals leftBefore) :
    Diverges externals rightBefore := by
  intro count
  rcases diverges count with ⟨leftAfter, leftSteps⟩
  rcases steps_forward related leftSteps with
    ⟨rightAfter, rightSteps, finalRelated⟩
  exact ⟨rightAfter, rightSteps⟩

/-- A bidirectional state relation gives observational equivalence for every
terminating observation. -/
theorem evaluatesState_iff_of_bisimilar
    (related : StatesBisimilar left right) :
    EvaluatesState externals left observation ↔
      EvaluatesState externals right observation := by
  exact ⟨evaluatesState_forward related.forward,
    evaluatesState_forward related.backward⟩

/-- The same bidirectional relation preserves and reflects divergence. -/
theorem diverges_iff_of_bisimilar
    (related : StatesBisimilar left right) :
    Diverges externals left ↔ Diverges externals right := by
  exact ⟨diverges_forward related.forward,
    diverges_forward related.backward⟩

/-- Pointwise declaration relations in both orientations provide the complete
program boundary needed by the alpha machine bisimulation. -/
structure ProgramsBirelated (left right : ImpureProgram) : Prop where
  forward : ProgramsRelated left right
  backward : ProgramsRelated right left

/-- Bidirectionally alpha-related programs have bisimilar entry machines for
every entry name and argument array. -/
theorem initialStates_bisimilar
    (related : ProgramsBirelated left right) (entry : Name)
    (args : Array Value) :
    StatesBisimilar (initialState left entry args) (initialState right entry args) := by
  have forwardMachine :
      MachineStateRelated (leftJoins := []) (rightJoins := [])
        ({} : FVarIdMap FVarId) [] []
        (initialState left entry args) (initialState right entry args) := {
    programs := related.forward
    runtime_eq := rfl
    joins := .empty
    frames := .nil
    envs := envsAgree_empty_scopes ({} : FVarIdMap FVarId) [] []
    renaming_scoped := renamingScoped_empty []
    join_renaming_scoped := renamingScoped_empty []
    control := .invokeName entry args
  }
  have backwardMachine :
      MachineStateRelated (leftJoins := []) (rightJoins := [])
        ({} : FVarIdMap FVarId) [] []
        (initialState right entry args) (initialState left entry args) := {
    programs := related.backward
    runtime_eq := rfl
    joins := .empty
    frames := .nil
    envs := envsAgree_empty_scopes ({} : FVarIdMap FVarId) [] []
    renaming_scoped := renamingScoped_empty []
    join_renaming_scoped := renamingScoped_empty []
    control := .invokeName entry args
  }
  exact {
    forward := ⟨_, _, _, _, _, forwardMachine⟩
    backward := ⟨_, _, _, _, _, backwardMachine⟩
  }

/-- Whole-program alpha renaming preserves and reflects every terminating
observation at every requested entry. -/
theorem samePhaseCorrect_of_programsBirelated
    (related : ProgramsBirelated before after) :
    SamePhaseCorrect (Impure.semantics externals) before after entries := by
  intro entry member args observation
  exact evaluatesState_iff_of_bisimilar
    (initialStates_bisimilar related entry args)

/-- Two code relations, one for each renaming orientation, induce semantic
equivalence in any runtime context covered by the proof scopes. -/
theorem codeEquivalentAt_of_birelated
    (forward : CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) scope scope left right)
    (backward : CodeRelated (leftJoins := []) (rightJoins := [])
      ({} : FVarIdMap FVarId) scope scope right left)
    (covers : EnvCovers scope state.env)
    (frames : FramesRelated state.frames state.frames)
    (bodies : ProgramBodiesRelated state.program) :
    CodeEquivalentAt externals state left right := by
  let leftState : MachineState := { state with control := .code left }
  let rightState : MachineState := { state with control := .code right }
  have forwardMachine :
      MachineStateRelated
        (leftJoins := []) (rightJoins := [])
        ({} : FVarIdMap FVarId) scope scope leftState rightState := {
    programs := programsRelated_refl bodies
    runtime_eq := rfl
    joins := .empty
    frames := frames
    envs := envsAgree_refl_of_covers covers
    renaming_scoped := renamingScoped_empty scope
    join_renaming_scoped := renamingScoped_empty []
    control := .code forward
  }
  have backwardMachine :
      MachineStateRelated
        (leftJoins := []) (rightJoins := [])
        ({} : FVarIdMap FVarId) scope scope rightState leftState := {
    programs := programsRelated_refl bodies
    runtime_eq := rfl
    joins := .empty
    frames := frames
    envs := envsAgree_refl_of_covers covers
    renaming_scoped := renamingScoped_empty scope
    join_renaming_scoped := renamingScoped_empty []
    control := .code backward
  }
  have bisimilar : StatesBisimilar leftState rightState := {
    forward := ⟨_, _, _, _, _, forwardMachine⟩
    backward := ⟨_, _, _, _, _, backwardMachine⟩
  }
  intro observation
  exact evaluatesState_iff_of_bisimilar bisimilar

/-- The matching immediate outcomes of two related terminal instructions. -/
inductive TerminalResultRelated (leftEnv rightEnv : Env) (state : MachineState) :
    CoreResult → CoreResult → Prop where
  | yielded (value : Value) :
      TerminalResultRelated leftEnv rightEnv state
        (.next { state with env := leftEnv, control := .yielded value })
        (.next { state with env := rightEnv, control := .yielded value })
  | done (observation : Observation) :
      TerminalResultRelated leftEnv rightEnv state (.done observation) (.done observation)

theorem coreStep_terminal_related
    (agree : EnvsAgree rho leftScope rightScope leftEnv rightEnv)
    (related : TerminalCodeRelated rho leftScope rightScope left right) :
    TerminalResultRelated leftEnv rightEnv state
      (coreStep { state with env := leftEnv, control := .code left })
      (coreStep { state with env := rightEnv, control := .code right }) := by
  cases related with
  | ret related =>
      obtain ⟨value, leftFound, rightFound⟩ :=
        agree _ related.1 _ related.2.1 related.2.2
      simpa [coreStep, lookupValue, leftFound, rightFound] using
        TerminalResultRelated.yielded (state := state)
          (leftEnv := leftEnv) (rightEnv := rightEnv) value
  | unreachable =>
      simpa [coreStep, fail, observe] using
        TerminalResultRelated.done (state := state)
          (leftEnv := leftEnv) (rightEnv := rightEnv)
          (observe state (.fault .unreachable))

/-- A machine state whose core step is already done has exactly one observation. -/
theorem evaluatesState_done_iff
    (done : coreStep initial = .done result) :
    EvaluatesState externals initial observation ↔ result = observation := by
  constructor
  · rintro ⟨count, final, execution, finalDone⟩
    cases execution with
    | refl _ => simpa [done] using finalDone
    | step head _ =>
        cases head with
        | internal transition => simp [done] at transition
        | external transition _ => simp [done] at transition
  · rintro rfl
    exact ⟨0, initial, .refl initial, done⟩

theorem unreach_codeEquivalentAt (leftType rightType : Expr) :
    CodeEquivalentAt externals state (.unreach leftType) (.unreach rightType) := by
  intro observation
  have leftDone :
      coreStep { state with control := .code (.unreach leftType) } =
        .done (observe state (.fault .unreachable)) := by
    simp [coreStep, fail, observe]
  have rightDone :
      coreStep { state with control := .code (.unreach rightType) } =
        .done (observe state (.fault .unreachable)) := by
    simp [coreStep, fail, observe]
  rw [evaluatesState_done_iff leftDone, evaluatesState_done_iff rightDone]

theorem terminalCodeRelated_empty_sound
    (related : TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    CodeEquivalentAt externals state left right := by
  cases related with
  | ret related =>
      rename_i leftId rightId
      have ids : leftId = rightId := by
        have fvarRelated := related.2.2
        change (leftId == rightId) = true at fvarRelated
        cases leftId with
        | mk leftName =>
            cases rightId with
            | mk rightName =>
                congr
                exact Name.beq_iff_eq.mp fvarRelated
      subst rightId
      exact codeEquivalentAt_refl
  | unreachable => exact unreach_codeEquivalentAt _ _

/--
The transparent local checker already implies the proof-facing return relation;
only scope membership is an external well-formedness premise. This lemma does
not depend on the trusted upstream-correspondence axiom.
-/
theorem terminalCodeRelated_of_local_return
    (leftScoped : leftScope.contains leftId = true)
    (rightScoped : rightScope.contains rightId = true)
    (accepted : Local.AcceptsAt rho
      ((.return leftId : LCNF.Code .impure)) (.return rightId)) :
    TerminalCodeRelated rho leftScope rightScope
      (.return leftId) (.return rightId) := by
  rcases accepted with ⟨fuel, accepted⟩
  cases fuel with
  | zero => simp [Local.checkAt, Local.eqv] at accepted
  | succ fuel =>
      apply TerminalCodeRelated.ret
      refine ⟨leftScoped, rightScoped, ?_⟩
      change (LCNF.AlphaEqv.eqvFVar leftId rightId).run rho = true
      exact accepted

/--
Reduce executable terminal alpha-soundness to the missing checker-to-relation
bridge. Lean 4.32 exposes `LCNF.AlphaEqv.eqv` as an opaque `partial def`, so
that bridge cannot currently be proved by unfolding the checker.
-/
theorem alphaEqvSoundAt_of_terminal_bridge
    (bridge : left.alphaEqv right = true →
      TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    AlphaEqvSoundAt externals state left right := by
  intro accepted
  exact terminalCodeRelated_empty_sound (bridge accepted)

/--
Keep local-checker soundness separate from correspondence with Lean's opaque
checker. This theorem does not depend on FIR's trusted upstream-correspondence
axiom when the two premises are supplied by the caller.
-/
theorem alphaEqvSoundAt_of_local_terminal_sound
    (upstream : UpstreamBridge)
    (localSound : Local.Accepts left right →
      TerminalCodeRelated ({} : FVarIdMap FVarId) scope scope left right) :
    AlphaEqvSoundAt externals state left right := by
  apply alphaEqvSoundAt_of_terminal_bridge
  intro accepted
  exact localSound (upstream.accepted left right accepted)

end Fir.LeanIR.Passes.AlphaEqv
