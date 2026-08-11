import FirTalos.Correctness.Adapter
import FirTalos.Correctness.StructuredWasmMachine

/-!
# Terminal adequacy for the emitted structured Wasm machine

`StructuredWasmStep` exposes calls and structured control that Talos evaluates
recursively.  To reconnect a completed structured path to `Wasm.run`, this
module records the semantic obligation represented by every live frame.  The
invariant is continuation based: it remembers the exact stack normalization
performed by labels, loops, and calls, while permitting each finite piece of
Talos execution to choose a sufficient fuel witness.

The final theorems construct this invariant from a finite path beginning at
the canonical generated-function entry.  It is internal proof evidence, not
an execution certificate accepted by the public compiler theorem.
-/

namespace FirTalos.Correctness

/-- The three successful control outcomes that the emitted structured machine
can propagate through its explicit frame stack. -/
inductive StructuredWasmOutcome (α : Type) where
  | fallthrough (store : Wasm.Store α) (locals : Wasm.Locals)
  | breaking (level : Nat) (store : Wasm.Store α) (locals : Wasm.Locals)
  | returning (store : Wasm.Store α) (values : List Wasm.Value)

/-- Embed a successful structured outcome into Talos's full continuation
type. -/
def StructuredWasmOutcome.toContinuation :
    StructuredWasmOutcome α → Wasm.Continuation α
  | .fallthrough store locals => .Fallthrough store locals
  | .breaking level store locals => .Break level store locals
  | .returning store values => .Return store values

/-- A residual program has one successful outcome at some finite Talos fuel.
Fuel monotonicity later lets independently obtained witnesses be combined. -/
def StructuredWasmExecutes
    (module : Wasm.Module) (env : Wasm.HostEnv α)
    (store : Wasm.Store α) (locals : Wasm.Locals)
    (program : Wasm.Program) (outcome : StructuredWasmOutcome α) : Prop :=
  ∃ fuel,
    Wasm.exec fuel module store locals program env = outcome.toContinuation

/-- A generated instruction that the structured machine can execute in one
step: either an ordinary emitted atomic instruction or a call resolved by the
module as an import.  Internal calls and structured control are deliberately
excluded because their bodies are exposed by multiple machine steps. -/
inductive StructuredWasmFlatInstruction (module : Wasm.Module) :
    Wasm.Instruction → Prop where
  | atomic {instruction : Wasm.Instruction}
      (shape : IsEmittedAtomicInstruction instruction) :
      StructuredWasmFlatInstruction module instruction
  | importedCall {functionIndex : Nat} {decl : Wasm.ImportDecl}
      (found : module.imports[functionIndex]? = some decl) :
      StructuredWasmFlatInstruction module (.call functionIndex)

/-- Straight-line fragment whose instructions each correspond to exactly one
structured-machine transition. -/
inductive StructuredWasmFlatProgram (module : Wasm.Module) :
    Wasm.Program → Prop where
  | nil : StructuredWasmFlatProgram module []
  | cons {instruction : Wasm.Instruction} {rest : Wasm.Program}
      (head : StructuredWasmFlatInstruction module instruction)
      (tail : StructuredWasmFlatProgram module rest) :
      StructuredWasmFlatProgram module (instruction :: rest)

namespace StructuredWasmFlatInstruction

/-- An exact Talos fallthrough for a flat instruction is the corresponding
single transition of the structured machine. -/
theorem step
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {fuel : Nat} {store nextStore : Wasm.Store α}
    {locals nextLocals : Wasm.Locals}
    {instruction : Wasm.Instruction} {rest : Wasm.Program}
    {frames : List StructuredWasmFrame}
    (flat : StructuredWasmFlatInstruction module instruction)
    (executed :
      Wasm.execOne fuel module store locals instruction env =
        .Fallthrough nextStore nextLocals) :
    StructuredWasmStep module env
      ⟨store, .running locals (instruction :: rest), frames⟩
      ⟨nextStore, .running nextLocals rest, frames⟩ := by
  cases flat with
  | atomic shape => exact .atomic shape executed
  | importedCall found => exact .importedCall found executed

end StructuredWasmFlatInstruction

namespace StructuredWasmFlatProgram

/-- Completeness of the structured machine for a successful straight-line
fragment.  The exact Talos execution is decomposed, not trusted separately:
each instruction contributes one machine transition and the final store and
locals are preserved literally. -/
theorem finitePathWithSuffix_of_exec_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {fuel : Nat} {store nextStore : Wasm.Store α}
    {locals nextLocals : Wasm.Locals} {program : Wasm.Program}
    {suffix : Wasm.Program} {frames : List StructuredWasmFrame}
    (flat : StructuredWasmFlatProgram module program)
    (executed :
      Wasm.exec fuel module store locals program env =
        .Fallthrough nextStore nextLocals) :
    FinitePath (StructuredWasmStep module env) program.length
      ⟨store, .running locals (program ++ suffix), frames⟩
      ⟨nextStore, .running nextLocals suffix, frames⟩ := by
  induction flat generalizing store locals with
  | nil =>
      simp only [Wasm.exec] at executed
      cases executed
      exact .refl _
  | @cons instruction rest head tail ih =>
      cases oneExecuted :
          Wasm.execOne fuel module store locals instruction env with
      | Fallthrough middleStore middleLocals =>
          have restExecuted :
              Wasm.exec fuel module middleStore middleLocals rest env =
                .Fallthrough nextStore nextLocals := by
            simpa only [Wasm.exec, oneExecuted] using executed
          exact .cons (head.step oneExecuted) (ih restExecuted)
      | Break level breakStore breakLocals =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed
      | Return returnStore values =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed
      | Trap trapStore message =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed
      | Invalid message =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed
      | OutOfFuel =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed
      | ReturnCall functionIndex returnStore values =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed
      | Throwing tag args throwStore throwLocals =>
          simp only [Wasm.exec, oneExecuted] at executed
          cases executed

/-- A semantic execution witness for a flat fragment therefore determines an
exact structured path, with path length equal to emitted instruction count. -/
theorem finitePathWithSuffix
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store nextStore : Wasm.Store α}
    {locals nextLocals : Wasm.Locals} {program : Wasm.Program}
    {suffix : Wasm.Program} {frames : List StructuredWasmFrame}
    (flat : StructuredWasmFlatProgram module program)
    (executed : StructuredWasmExecutes module env store locals program
      (.fallthrough nextStore nextLocals)) :
    FinitePath (StructuredWasmStep module env) program.length
      ⟨store, .running locals (program ++ suffix), frames⟩
      ⟨nextStore, .running nextLocals suffix, frames⟩ := by
  obtain ⟨fuel, run⟩ := executed
  exact flat.finitePathWithSuffix_of_exec_fallthrough run

/-- Empty-suffix specialization of `finitePathWithSuffix`. -/
theorem finitePath
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store nextStore : Wasm.Store α}
    {locals nextLocals : Wasm.Locals} {program : Wasm.Program}
    {frames : List StructuredWasmFrame}
    (flat : StructuredWasmFlatProgram module program)
    (executed : StructuredWasmExecutes module env store locals program
      (.fallthrough nextStore nextLocals)) :
    FinitePath (StructuredWasmStep module env) program.length
      ⟨store, .running locals program, frames⟩
      ⟨nextStore, .running nextLocals [], frames⟩ := by
  simpa using flat.finitePathWithSuffix (suffix := []) executed

end StructuredWasmFlatProgram

mutual

/-- Semantic completion of one structured configuration.  For running code it
records an exact Talos outcome and then discharges the explicit frame stack;
the administrative control modes inject that outcome directly. -/
inductive StructuredWasmCompletion
    (module : Wasm.Module) (env : Wasm.HostEnv α) :
    StructuredWasmState α → Wasm.Store α → List Wasm.Value → Prop where
  | running
      {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
      {program : Wasm.Program} {frames : List StructuredWasmFrame}
      {outcome : StructuredWasmOutcome α} {finalValues : List Wasm.Value}
      (executed : StructuredWasmExecutes module env store locals program outcome)
      (continued : StructuredWasmContinuation module env outcome frames
        finalStore finalValues) :
      StructuredWasmCompletion module env
        ⟨store, .running locals program, frames⟩ finalStore finalValues
  | breaking
      {store finalStore : Wasm.Store α} {level : Nat} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
      (continued : StructuredWasmContinuation module env
        (.breaking level store locals) frames finalStore finalValues) :
      StructuredWasmCompletion module env
        ⟨store, .breaking level locals, frames⟩ finalStore finalValues
  | returning
      {store finalStore : Wasm.Store α} {values : List Wasm.Value}
      {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
      (continued : StructuredWasmContinuation module env
        (.returning store values) frames finalStore finalValues) :
      StructuredWasmCompletion module env
        ⟨store, .returning values, frames⟩ finalStore finalValues
  | halted {store : Wasm.Store α} {values : List Wasm.Value} :
      StructuredWasmCompletion module env
        ⟨store, .halted values, []⟩ store values

/-- Exact interpretation of the explicit frame stack.  Each constructor is
the corresponding Talos stack-normalization rule.  In particular, a loop
restart retains its loop frame, and a call accepts exactly the three successful
callee exits recognized by `Wasm.run`. -/
inductive StructuredWasmContinuation
    (module : Wasm.Module) (env : Wasm.HostEnv α) :
    StructuredWasmOutcome α → List StructuredWasmFrame →
      Wasm.Store α → List Wasm.Value → Prop where
  | topFallthrough {store : Wasm.Store α} {locals : Wasm.Locals} :
      StructuredWasmContinuation module env (.fallthrough store locals) []
        store locals.values
  | topBreakZero {store : Wasm.Store α} {locals : Wasm.Locals} :
      StructuredWasmContinuation module env (.breaking 0 store locals) []
        store locals.values
  | topReturn {store : Wasm.Store α} {values : List Wasm.Value} :
      StructuredWasmContinuation module env (.returning store values) []
        store values
  | labelFallthrough
      {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
      {resultArity : Nat} {belowStack : List Wasm.Value}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { locals with
              values := locals.values.take resultArity ++ belowStack }
            rest,
          frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.fallthrough store locals)
        (.label resultArity belowStack rest :: frames) finalStore finalValues
  | labelBreakZero
      {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
      {resultArity : Nat} {belowStack : List Wasm.Value}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { locals with
              values := locals.values.take resultArity ++ belowStack }
            rest,
          frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.breaking 0 store locals)
        (.label resultArity belowStack rest :: frames) finalStore finalValues
  | labelBreakSucc
      {store finalStore : Wasm.Store α} {level resultArity : Nat}
      {locals : Wasm.Locals} {belowStack : List Wasm.Value}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store, .breaking level locals, frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.breaking (level + 1) store locals)
        (.label resultArity belowStack rest :: frames) finalStore finalValues
  | labelReturn
      {store finalStore : Wasm.Store α} {values belowStack : List Wasm.Value}
      {resultArity : Nat} {rest : Wasm.Program}
      {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store, .returning values, frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.returning store values)
        (.label resultArity belowStack rest :: frames) finalStore finalValues
  | loopFallthrough
      {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
      {paramArity resultArity : Nat} {belowStack : List Wasm.Value}
      {body rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { locals with
              values := locals.values.take resultArity ++ belowStack }
            rest,
          frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.fallthrough store locals)
        (.loop paramArity resultArity belowStack body rest :: frames)
        finalStore finalValues
  | loopBreakZero
      {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
      {paramArity resultArity : Nat} {belowStack : List Wasm.Value}
      {body rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (enough : paramArity ≤ locals.values.length)
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { locals with
              values := locals.values.take paramArity ++ belowStack }
            body,
          .loop paramArity resultArity belowStack body rest :: frames⟩
        finalStore finalValues) :
      StructuredWasmContinuation module env (.breaking 0 store locals)
        (.loop paramArity resultArity belowStack body rest :: frames)
        finalStore finalValues
  | loopBreakSucc
      {store finalStore : Wasm.Store α} {level paramArity resultArity : Nat}
      {locals : Wasm.Locals} {belowStack : List Wasm.Value}
      {body rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store, .breaking level locals, frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.breaking (level + 1) store locals)
        (.loop paramArity resultArity belowStack body rest :: frames)
        finalStore finalValues
  | loopReturn
      {store finalStore : Wasm.Store α} {values belowStack : List Wasm.Value}
      {paramArity resultArity : Nat} {body rest : Wasm.Program}
      {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store, .returning values, frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.returning store values)
        (.loop paramArity resultArity belowStack body rest :: frames)
        finalStore finalValues
  | callFallthrough
      {store finalStore : Wasm.Store α} {locals callerLocals : Wasm.Locals}
      {resultArity : Nat} {callerRemainder : List Wasm.Value}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { callerLocals with
              values := locals.values.take resultArity ++ callerRemainder }
            rest,
          frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.fallthrough store locals)
        (.call resultArity callerRemainder callerLocals rest :: frames)
        finalStore finalValues
  | callBreakZero
      {store finalStore : Wasm.Store α} {locals callerLocals : Wasm.Locals}
      {resultArity : Nat} {callerRemainder : List Wasm.Value}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { callerLocals with
              values := locals.values.take resultArity ++ callerRemainder }
            rest,
          frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.breaking 0 store locals)
        (.call resultArity callerRemainder callerLocals rest :: frames)
        finalStore finalValues
  | callReturn
      {store finalStore : Wasm.Store α} {values callerRemainder : List Wasm.Value}
      {callerLocals : Wasm.Locals} {resultArity : Nat}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      {finalValues : List Wasm.Value}
      (next : StructuredWasmCompletion module env
        ⟨store,
          .running
            { callerLocals with
              values := values.take resultArity ++ callerRemainder }
            rest,
          frames⟩ finalStore finalValues) :
      StructuredWasmContinuation module env (.returning store values)
        (.call resultArity callerRemainder callerLocals rest :: frames)
        finalStore finalValues

end

namespace StructuredWasmOutcome

/-- Successful structured outcomes are never Talos's fuel-exhaustion
continuation. -/
theorem toContinuation_ne_outOfFuel (outcome : StructuredWasmOutcome α) :
    outcome.toContinuation ≠ .OutOfFuel := by
  cases outcome <;> intro impossible <;> cases impossible

end StructuredWasmOutcome

namespace StructuredWasmExecutes

/-- The empty residual program falls through without changing its concrete
state. -/
theorem empty
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store : Wasm.Store α} {locals : Wasm.Locals} :
    StructuredWasmExecutes module env store locals []
      (.fallthrough store locals) := by
  exact ⟨0, by simp only [Wasm.exec, StructuredWasmOutcome.toContinuation]⟩

/-- Executing the emitted branch instruction enters the matching structured
unwinding mode. -/
theorem beginBreak
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store : Wasm.Store α} {locals : Wasm.Locals}
    {level : Nat} {rest : Wasm.Program} :
    StructuredWasmExecutes module env store locals (.br level :: rest)
      (.breaking level store locals) := by
  exact ⟨1, by simp only [Wasm.exec, Wasm.execOne.eq_def,
    StructuredWasmOutcome.toContinuation]⟩

/-- Executing the emitted return instruction enters structured return
unwinding with the current operand stack. -/
theorem beginReturn
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store : Wasm.Store α} {locals : Wasm.Locals}
    {rest : Wasm.Program} :
    StructuredWasmExecutes module env store locals (.ret :: rest)
      (.returning store locals.values) := by
  exact ⟨1, by simp only [Wasm.exec, Wasm.execOne.eq_def,
    StructuredWasmOutcome.toContinuation]⟩

/-- One successful finite-fuel execution is stable at every larger fuel. -/
theorem stable
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store : Wasm.Store α} {locals : Wasm.Locals}
    {program : Wasm.Program} {outcome : StructuredWasmOutcome α}
    (executed : StructuredWasmExecutes module env store locals program outcome) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module store locals program env = outcome.toContinuation := by
  obtain ⟨bound, executed⟩ := executed
  refine ⟨bound, ?_⟩
  intro fuel enough
  have notOutOfFuel :
      Wasm.exec bound module store locals program env ≠ .OutOfFuel := by
    rw [executed]
    exact outcome.toContinuation_ne_outOfFuel
  rw [Wasm.exec_fuel_mono enough notOutOfFuel, executed]

/-- Prepend one genuine Talos fallthrough to an eventual residual execution. -/
theorem cons_of_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {stepFuel : Nat} {store nextStore : Wasm.Store α}
    {locals nextLocals : Wasm.Locals}
    {instruction : Wasm.Instruction} {rest : Wasm.Program}
    {outcome : StructuredWasmOutcome α}
    (head :
      Wasm.execOne stepFuel module store locals instruction env =
        .Fallthrough nextStore nextLocals)
    (tail : StructuredWasmExecutes module env nextStore nextLocals rest outcome) :
    StructuredWasmExecutes module env store locals (instruction :: rest) outcome := by
  obtain ⟨tailBound, tailStable⟩ := tail.stable
  let bound := Nat.max stepFuel tailBound
  have stepEnough : stepFuel ≤ bound := Nat.le_max_left _ _
  have tailEnough : tailBound ≤ bound := Nat.le_max_right _ _
  have notOutOfFuel :
      Wasm.execOne stepFuel module store locals instruction env ≠ .OutOfFuel := by
    rw [head]
    intro impossible
    cases impossible
  have headAtBound := Wasm.execOne_fuel_mono stepEnough notOutOfFuel
  rw [head] at headAtBound
  refine ⟨bound, ?_⟩
  simp only [Wasm.exec, headAtBound, tailStable bound tailEnough]

/-- Collapse a normally completed block body and the following residual
program into one eventual outer execution. -/
theorem block_of_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {outcome : StructuredWasmOutcome α}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.fallthrough bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++
          locals.values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store locals
      (.block paramArity resultArity body :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    bodyStable bound bodyEnough, restStable (bound + 1) restEnough]

/-- A depth-zero branch has the same block result normalization as ordinary
body fallthrough. -/
theorem block_of_break_zero
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {outcome : StructuredWasmOutcome α}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.breaking 0 bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++
          locals.values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store locals
      (.block paramArity resultArity body :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    bodyStable bound bodyEnough, restStable (bound + 1) restEnough]

/-- A branch crossing a block decrements its level exactly once. -/
theorem block_of_break_succ
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity level : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.breaking (level + 1) bodyStore bodyLocals)) :
    StructuredWasmExecutes module env store locals
      (.block paramArity resultArity body :: rest)
      (.breaking level bodyStore bodyLocals) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    bodyStable bound (Nat.le_refl bound)]

/-- Returns propagate unchanged through a block. -/
theorem block_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals : Wasm.Locals}
    {values : List Wasm.Value}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.returning bodyStore values)) :
    StructuredWasmExecutes module env store locals
      (.block paramArity resultArity body :: rest)
      (.returning bodyStore values) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    bodyStable bound (Nat.le_refl bound)]

/-- Collapse the selected nonzero conditional body on normal completion. -/
theorem iff_then_of_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {condition : UInt32} {values : List Wasm.Value}
    {outcome : StructuredWasmOutcome α}
    (nonzero : condition ≠ 0)
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } thenBody (.fallthrough bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++ values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 condition :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    if_pos nonzero,
    bodyStable bound bodyEnough, restStable (bound + 1) restEnough]

/-- Collapse the selected zero conditional body on normal completion. -/
theorem iff_else_of_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {values : List Wasm.Value} {outcome : StructuredWasmOutcome α}
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } elseBody (.fallthrough bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++ values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 0 :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    ne_eq, not_true_eq_false, if_false,
    bodyStable bound bodyEnough, restStable (bound + 1) restEnough]

theorem iff_then_of_break_zero
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {condition : UInt32} {values : List Wasm.Value}
    {outcome : StructuredWasmOutcome α}
    (nonzero : condition ≠ 0)
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } thenBody (.breaking 0 bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++ values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 condition :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    if_pos nonzero, bodyStable bound bodyEnough,
    restStable (bound + 1) restEnough]

theorem iff_else_of_break_zero
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {values : List Wasm.Value} {outcome : StructuredWasmOutcome α}
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } elseBody (.breaking 0 bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++ values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 0 :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    ne_eq, not_true_eq_false, if_false, bodyStable bound bodyEnough,
    restStable (bound + 1) restEnough]

theorem iff_then_of_break_succ
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity level : Nat}
    {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {condition : UInt32} {values : List Wasm.Value}
    (nonzero : condition ≠ 0)
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } thenBody
      (.breaking (level + 1) bodyStore bodyLocals)) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 condition :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest)
      (.breaking level bodyStore bodyLocals) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    if_pos nonzero, bodyStable bound (Nat.le_refl bound)]

theorem iff_else_of_break_succ
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity level : Nat}
    {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {values : List Wasm.Value}
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } elseBody
      (.breaking (level + 1) bodyStore bodyLocals)) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 0 :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest)
      (.breaking level bodyStore bodyLocals) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    ne_eq, not_true_eq_false, if_false,
    bodyStable bound (Nat.le_refl bound)]

theorem iff_then_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals : Wasm.Locals}
    {condition : UInt32} {values result : List Wasm.Value}
    (nonzero : condition ≠ 0)
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } thenBody (.returning bodyStore result)) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 condition :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest)
      (.returning bodyStore result) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    if_pos nonzero, bodyStable bound (Nat.le_refl bound)]

theorem iff_else_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals : Wasm.Locals}
    {values result : List Wasm.Value}
    (bodyExecuted : StructuredWasmExecutes module env store
      { locals with values := values } elseBody (.returning bodyStore result)) :
    StructuredWasmExecutes module env store
      { locals with values := .i32 0 :: values }
      (.iff paramArity resultArity thenBody elseBody :: rest)
      (.returning bodyStore result) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, StructuredWasmOutcome.toContinuation,
    ne_eq, not_true_eq_false, if_false,
    bodyStable bound (Nat.le_refl bound)]

/-- Collapse a normally completed loop body and its following residual
program. -/
theorem loop_of_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {outcome : StructuredWasmOutcome α}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.fallthrough bodyStore bodyLocals))
    (restExecuted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take resultArity ++
          locals.values.drop paramArity }
      rest outcome) :
    StructuredWasmExecutes module env store locals
      (.loop paramArity resultArity body :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max bodyBound restBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne_loop_succ,
    StructuredWasmOutcome.toContinuation, bodyStable bound bodyEnough,
    restStable (bound + 1) restEnough]

/-- One completed `br 0` iteration followed by an eventual restarted loop is
an eventual execution of the original loop.  The proof aligns the recursive
`execOne` call with the next larger outer fuel. -/
theorem loop_of_break_zero
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    {outcome : StructuredWasmOutcome α}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.breaking 0 bodyStore bodyLocals))
    (restarted : StructuredWasmExecutes module env bodyStore
      { bodyLocals with
        values := bodyLocals.values.take paramArity ++
          locals.values.drop paramArity }
      (.loop paramArity resultArity body :: rest) outcome) :
    StructuredWasmExecutes module env store locals
      (.loop paramArity resultArity body :: rest) outcome := by
  obtain ⟨bodyBound, bodyStable⟩ := bodyExecuted.stable
  obtain ⟨restartBound, restartStable⟩ := restarted.stable
  let bound := Nat.max bodyBound restartBound
  have bodyEnough : bodyBound ≤ bound := Nat.le_max_left _ _
  have restartEnough : restartBound ≤ bound := Nat.le_max_right _ _
  let restartedLocals : Wasm.Locals :=
    { bodyLocals with
      values := bodyLocals.values.take paramArity ++
        locals.values.drop paramArity }
  have restartedAtBound :
      Wasm.exec bound module bodyStore restartedLocals
          (.loop paramArity resultArity body :: rest) env =
        outcome.toContinuation := by
    simpa [restartedLocals] using restartStable bound restartEnough
  have loopNotOutOfFuel :
      Wasm.execOne bound module bodyStore restartedLocals
          (.loop paramArity resultArity body) env ≠ .OutOfFuel := by
    intro exhausted
    apply outcome.toContinuation_ne_outOfFuel
    rw [← restartedAtBound]
    simp only [Wasm.exec, exhausted]
  have loopAtNext :=
    Wasm.execOne_fuel_mono (Nat.le_succ bound) loopNotOutOfFuel
  have restartedAtNext :
      Wasm.exec (bound + 1) module bodyStore restartedLocals
          (.loop paramArity resultArity body :: rest) env =
        outcome.toContinuation := by
    simpa [restartedLocals] using
      restartStable (bound + 1)
        (Nat.le_trans restartEnough (Nat.le_succ bound))
  refine ⟨bound + 1, ?_⟩
  rw [Wasm.exec, Wasm.execOne_loop_succ,
    bodyStable bound bodyEnough]
  change
    (match Wasm.execOne bound module bodyStore restartedLocals
        (.loop paramArity resultArity body) env with
      | .Fallthrough nextStore nextLocals =>
          Wasm.exec (bound + 1) module nextStore nextLocals rest env
      | other => other) = outcome.toContinuation
  cases result : Wasm.execOne bound module bodyStore restartedLocals
      (.loop paramArity resultArity body) env <;>
    simpa only [result, Wasm.exec, Nat.succ_eq_add_one, loopAtNext] using
      restartedAtNext

/-- A branch crossing a loop decrements its level exactly once. -/
theorem loop_of_break_succ
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity level : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals bodyLocals : Wasm.Locals}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.breaking (level + 1) bodyStore bodyLocals)) :
    StructuredWasmExecutes module env store locals
      (.loop paramArity resultArity body :: rest)
      (.breaking level bodyStore bodyLocals) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne_loop_succ,
    StructuredWasmOutcome.toContinuation,
    bodyStable bound (Nat.le_refl bound)]

/-- Returns propagate unchanged through a loop. -/
theorem loop_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store bodyStore : Wasm.Store α} {locals : Wasm.Locals}
    {values : List Wasm.Value}
    (bodyExecuted : StructuredWasmExecutes module env store locals body
      (.returning bodyStore values)) :
    StructuredWasmExecutes module env store locals
      (.loop paramArity resultArity body :: rest)
      (.returning bodyStore values) := by
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne_loop_succ,
    StructuredWasmOutcome.toContinuation,
    bodyStable bound (Nat.le_refl bound)]

/-- Collapse a normally completed internal callee and the caller's residual
program. -/
theorem internalCall_of_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {store calleeStore : Wasm.Store α}
    {callerLocals calleeLocals : Wasm.Locals} {rest : Wasm.Program}
    {outcome : StructuredWasmOutcome α}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (calleeExecuted : StructuredWasmExecutes module env store
      (function.toLocals
        (callerLocals.values.take function.numParams).reverse)
      function.body (.fallthrough calleeStore calleeLocals))
    (restExecuted : StructuredWasmExecutes module env calleeStore
      { callerLocals with
        values := calleeLocals.values.take function.results.length ++
          callerLocals.values.drop function.numParams }
      rest outcome) :
    StructuredWasmExecutes module env store callerLocals
      (.call functionIndex :: rest) outcome := by
  obtain ⟨calleeBound, calleeStable⟩ := calleeExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max calleeBound restBound
  have calleeEnough : calleeBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, Wasm.run_eq notImport, found,
    StructuredWasmOutcome.toContinuation, calleeStable bound calleeEnough,
    restStable (bound + 1) restEnough]

/-- A depth-zero callee break is a successful function result in Talos and
therefore resumes the caller just like fallthrough. -/
theorem internalCall_of_break_zero
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {store calleeStore : Wasm.Store α}
    {callerLocals calleeLocals : Wasm.Locals} {rest : Wasm.Program}
    {outcome : StructuredWasmOutcome α}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (calleeExecuted : StructuredWasmExecutes module env store
      (function.toLocals
        (callerLocals.values.take function.numParams).reverse)
      function.body (.breaking 0 calleeStore calleeLocals))
    (restExecuted : StructuredWasmExecutes module env calleeStore
      { callerLocals with
        values := calleeLocals.values.take function.results.length ++
          callerLocals.values.drop function.numParams }
      rest outcome) :
    StructuredWasmExecutes module env store callerLocals
      (.call functionIndex :: rest) outcome := by
  obtain ⟨calleeBound, calleeStable⟩ := calleeExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max calleeBound restBound
  have calleeEnough : calleeBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, Wasm.run_eq notImport, found,
    StructuredWasmOutcome.toContinuation, calleeStable bound calleeEnough,
    restStable (bound + 1) restEnough]

/-- Collapse an explicit callee return and resume the caller with the exact
result/remainder convention. -/
theorem internalCall_of_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {store calleeStore : Wasm.Store α} {callerLocals : Wasm.Locals}
    {values : List Wasm.Value} {rest : Wasm.Program}
    {outcome : StructuredWasmOutcome α}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (calleeExecuted : StructuredWasmExecutes module env store
      (function.toLocals
        (callerLocals.values.take function.numParams).reverse)
      function.body (.returning calleeStore values))
    (restExecuted : StructuredWasmExecutes module env calleeStore
      { callerLocals with
        values := values.take function.results.length ++
          callerLocals.values.drop function.numParams }
      rest outcome) :
    StructuredWasmExecutes module env store callerLocals
      (.call functionIndex :: rest) outcome := by
  obtain ⟨calleeBound, calleeStable⟩ := calleeExecuted.stable
  obtain ⟨restBound, restStable⟩ := restExecuted.stable
  let bound := Nat.max calleeBound restBound
  have calleeEnough : calleeBound ≤ bound := Nat.le_max_left _ _
  have restEnough : restBound ≤ bound + 1 :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
  refine ⟨bound + 1, ?_⟩
  simp only [Wasm.exec, Wasm.execOne.eq_def, Wasm.run_eq notImport, found,
    StructuredWasmOutcome.toContinuation, calleeStable bound calleeEnough,
    restStable (bound + 1) restEnough]

end StructuredWasmExecutes

namespace StructuredWasmCompletion

theorem running_inv
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
    {program : Wasm.Program} {frames : List StructuredWasmFrame}
    {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env
      ⟨store, .running locals program, frames⟩ finalStore finalValues) :
    ∃ outcome,
      StructuredWasmExecutes module env store locals program outcome ∧
      StructuredWasmContinuation module env outcome frames
        finalStore finalValues := by
  cases completion with
  | running executed continued => exact ⟨_, executed, continued⟩

theorem breaking_inv
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store finalStore : Wasm.Store α} {level : Nat} {locals : Wasm.Locals}
    {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env
      ⟨store, .breaking level locals, frames⟩ finalStore finalValues) :
    StructuredWasmContinuation module env (.breaking level store locals)
      frames finalStore finalValues := by
  cases completion with
  | breaking continued => exact continued

theorem returning_inv
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {store finalStore : Wasm.Store α} {values : List Wasm.Value}
    {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env
      ⟨store, .returning values, frames⟩ finalStore finalValues) :
    StructuredWasmContinuation module env (.returning store values)
      frames finalStore finalValues := by
  cases completion with
  | returning continued => exact continued

/-- Collapse the semantic label frame introduced by block entry. -/
theorem of_enterBlock
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
    {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env
      ⟨store, .running locals body,
        .label resultArity (locals.values.drop paramArity) rest :: frames⟩
      finalStore finalValues) :
    StructuredWasmCompletion module env
      ⟨store, .running locals (.block paramArity resultArity body :: rest), frames⟩
      finalStore finalValues := by
  obtain ⟨_, bodyExecuted, continued⟩ := completion.running_inv
  cases continued with
  | labelFallthrough next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running (bodyExecuted.block_of_fallthrough restExecuted)
        restContinued
  | labelBreakZero next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running (bodyExecuted.block_of_break_zero restExecuted)
        restContinued
  | labelBreakSucc next =>
      have restContinued := next.breaking_inv
      exact .running bodyExecuted.block_of_break_succ restContinued
  | labelReturn next =>
      have restContinued := next.returning_inv
      exact .running bodyExecuted.block_of_return restContinued

/-- Collapse the semantic label frame introduced by a selected nonzero
conditional. -/
theorem of_enterIffThen
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
    {condition : UInt32} {values : List Wasm.Value}
    {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
    (nonzero : condition ≠ 0)
    (completion : StructuredWasmCompletion module env
      ⟨store, .running { locals with values := values } thenBody,
        .label resultArity (values.drop paramArity) rest :: frames⟩
      finalStore finalValues) :
    StructuredWasmCompletion module env
      ⟨store, .running { locals with values := .i32 condition :: values }
        (.iff paramArity resultArity thenBody elseBody :: rest), frames⟩
      finalStore finalValues := by
  obtain ⟨_, bodyExecuted, continued⟩ := completion.running_inv
  cases continued with
  | labelFallthrough next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running
        (bodyExecuted.iff_then_of_fallthrough nonzero restExecuted)
        restContinued
  | labelBreakZero next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running
        (bodyExecuted.iff_then_of_break_zero nonzero restExecuted)
        restContinued
  | labelBreakSucc next =>
      have restContinued := next.breaking_inv
      exact .running (bodyExecuted.iff_then_of_break_succ nonzero)
        restContinued
  | labelReturn next =>
      have restContinued := next.returning_inv
      exact .running (bodyExecuted.iff_then_of_return nonzero) restContinued

/-- Collapse the semantic label frame introduced by the selected zero
conditional. -/
theorem of_enterIffElse
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
    {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
    {values : List Wasm.Value} {frames : List StructuredWasmFrame}
    {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env
      ⟨store, .running { locals with values := values } elseBody,
        .label resultArity (values.drop paramArity) rest :: frames⟩
      finalStore finalValues) :
    StructuredWasmCompletion module env
      ⟨store, .running { locals with values := .i32 0 :: values }
        (.iff paramArity resultArity thenBody elseBody :: rest), frames⟩
      finalStore finalValues := by
  obtain ⟨_, bodyExecuted, continued⟩ := completion.running_inv
  cases continued with
  | labelFallthrough next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running (bodyExecuted.iff_else_of_fallthrough restExecuted)
        restContinued
  | labelBreakZero next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running (bodyExecuted.iff_else_of_break_zero restExecuted)
        restContinued
  | labelBreakSucc next =>
      have restContinued := next.breaking_inv
      exact .running bodyExecuted.iff_else_of_break_succ restContinued
  | labelReturn next =>
      have restContinued := next.returning_inv
      exact .running bodyExecuted.iff_else_of_return restContinued

/-- Every completion whose current state is inside a head loop frame can
collapse that frame when its stored below-stack agrees with the entry stack. -/
def HeadLoopCollapsible
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {state : StructuredWasmState α} {finalStore : Wasm.Store α}
    {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env state
      finalStore finalValues) : Prop :=
  match state with
  | ⟨store, .running locals program,
      .loop paramArity resultArity belowStack body rest :: frames⟩ =>
      program = body → belowStack = locals.values.drop paramArity →
        StructuredWasmCompletion module env
          ⟨store,
            .running locals (.loop paramArity resultArity body :: rest),
            frames⟩ finalStore finalValues
  | _ => True

/-- Continuation-side motive paired with `HeadLoopCollapsible`. -/
def HeadLoopContinuationCollapsible
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {outcome : StructuredWasmOutcome α} {frames : List StructuredWasmFrame}
    {finalStore : Wasm.Store α} {finalValues : List Wasm.Value}
    (continued : StructuredWasmContinuation module env outcome frames
      finalStore finalValues) : Prop :=
  match frames with
  | .loop paramArity resultArity belowStack body rest :: suffix =>
      ∀ (store : Wasm.Store α) (locals : Wasm.Locals),
        belowStack = locals.values.drop paramArity →
        StructuredWasmExecutes module env store locals body outcome →
        StructuredWasmCompletion module env
          ⟨store,
            .running locals (.loop paramArity resultArity body :: rest),
            suffix⟩ finalStore finalValues
  | _ => True

theorem collapseHeadLoopCompletion
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {state : StructuredWasmState α} {finalStore : Wasm.Store α}
    {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env state
      finalStore finalValues) :
    HeadLoopCollapsible completion := by
  refine StructuredWasmCompletion.rec
    (motive_1 := fun _ _ _ completion => HeadLoopCollapsible completion)
    (motive_2 := fun _ _ _ _ continued =>
      HeadLoopContinuationCollapsible continued)
    (running := ?_)
    (breaking := by intros; trivial)
    (returning := by intros; trivial)
    (halted := by intros; trivial)
    (topFallthrough := by intros; trivial)
    (topBreakZero := by intros; trivial)
    (topReturn := by intros; trivial)
    (labelFallthrough := by intros; trivial)
    (labelBreakZero := by intros; trivial)
    (labelBreakSucc := by intros; trivial)
    (labelReturn := by intros; trivial)
    (loopFallthrough := ?_)
    (loopBreakZero := ?_)
    (loopBreakSucc := ?_)
    (loopReturn := ?_)
    (callFallthrough := by intros; trivial)
    (callBreakZero := by intros; trivial)
    (callReturn := by intros; trivial)
    completion
  · intro store finalStore locals program frames outcome finalValues
      executed continued continuedIH
    unfold HeadLoopCollapsible
    cases frames with
    | nil => trivial
    | cons frame frames =>
        cases frame with
        | label _ _ _ => trivial
        | call _ _ _ _ => trivial
        | loop paramArity resultArity belowStack body rest =>
            intro programEq belowEq
            exact continuedIH _ _ belowEq
              (by simpa only [programEq] using executed)
  · intro bodyStore finalStore locals paramArity resultArity belowStack body
      rest frames finalValues next _nextIH
    unfold HeadLoopContinuationCollapsible
    intro initialStore initialLocals belowEq bodyExecuted
    obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
    have restExecuted' := restExecuted
    rw [belowEq] at restExecuted'
    exact .running (bodyExecuted.loop_of_fallthrough restExecuted')
      restContinued
  · intro bodyStore finalStore branchLocals paramArity resultArity belowStack
      body rest frames finalValues enough next nextIH
    unfold HeadLoopContinuationCollapsible
    intro initialStore initialLocals belowEq bodyExecuted
    let restartedLocals : Wasm.Locals :=
      { branchLocals with
        values := branchLocals.values.take paramArity ++ belowStack }
    have takeLength :
        (branchLocals.values.take paramArity).length = paramArity :=
      List.length_take_of_le enough
    have restartedBelow :
        belowStack = restartedLocals.values.drop paramArity := by
      simp only [restartedLocals]
      calc
        belowStack =
            (branchLocals.values.take paramArity ++ belowStack).drop
              (branchLocals.values.take paramArity).length :=
          List.drop_append_length.symm
        _ = (branchLocals.values.take paramArity ++ belowStack).drop
              paramArity := by rw [takeLength]
    have restartedCompletion := nextIH rfl restartedBelow
    obtain ⟨restartedOutcome, restartedExecuted, restContinued⟩ :=
      restartedCompletion.running_inv
    have restartedExecuted' :
        StructuredWasmExecutes module env bodyStore
          { branchLocals with
            values := branchLocals.values.take paramArity ++
              initialLocals.values.drop paramArity }
          (.loop paramArity resultArity body :: rest) restartedOutcome := by
      simpa only [restartedLocals, belowEq] using restartedExecuted
    exact .running
      (bodyExecuted.loop_of_break_zero restartedExecuted') restContinued
  · intro bodyStore finalStore level paramArity resultArity locals belowStack
      body rest frames finalValues next _nextIH
    unfold HeadLoopContinuationCollapsible
    intro _ _ _ bodyExecuted
    exact .running bodyExecuted.loop_of_break_succ next.breaking_inv
  · intro bodyStore finalStore values belowStack paramArity resultArity body
      rest frames finalValues next _nextIH
    unfold HeadLoopContinuationCollapsible
    intro _ _ _ bodyExecuted
    exact .running bodyExecuted.loop_of_return next.returning_inv

/-- Collapse one live loop frame.  The `belowStack` equality is the frame
shape invariant established at entry and preserved by every arity-correct
restart. -/
theorem of_loopFrame
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
    {belowStack : List Wasm.Value} {frames : List StructuredWasmFrame}
    {finalValues : List Wasm.Value}
    (belowEq : belowStack = locals.values.drop paramArity)
    (completion : StructuredWasmCompletion module env
      ⟨store, .running locals body,
        .loop paramArity resultArity belowStack body rest :: frames⟩
      finalStore finalValues) :
    StructuredWasmCompletion module env
      ⟨store, .running locals (.loop paramArity resultArity body :: rest), frames⟩
      finalStore finalValues :=
  collapseHeadLoopCompletion completion rfl belowEq

/-- Public entry form of `of_loopFrame`: loop entry stores exactly the drop of
the operand stack below its parameter segment. -/
theorem of_enterLoop
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {paramArity resultArity : Nat} {body rest : Wasm.Program}
    {store finalStore : Wasm.Store α} {locals : Wasm.Locals}
    {frames : List StructuredWasmFrame} {finalValues : List Wasm.Value}
    (completion : StructuredWasmCompletion module env
      ⟨store, .running locals body,
        .loop paramArity resultArity (locals.values.drop paramArity)
          body rest :: frames⟩ finalStore finalValues) :
    StructuredWasmCompletion module env
      ⟨store, .running locals (.loop paramArity resultArity body :: rest), frames⟩
      finalStore finalValues :=
  of_loopFrame rfl completion

/-- Collapse the explicit call frame introduced by an internal-function
entry.  The three successful callee exits are exactly the cases accepted by
`Wasm.run`: fallthrough, a depth-zero break, and explicit return. -/
theorem of_enterCall
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {store finalStore : Wasm.Store α} {callerLocals : Wasm.Locals}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    {finalValues : List Wasm.Value}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (completion : StructuredWasmCompletion module env
      ⟨store,
        .running
          (function.toLocals
            (callerLocals.values.take function.numParams).reverse)
          function.body,
        .call function.results.length
            (callerLocals.values.drop function.numParams) callerLocals rest ::
          frames⟩
      finalStore finalValues) :
    StructuredWasmCompletion module env
      ⟨store, .running callerLocals (.call functionIndex :: rest), frames⟩
      finalStore finalValues := by
  obtain ⟨_, calleeExecuted, continued⟩ := completion.running_inv
  cases continued with
  | callFallthrough next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running
        (calleeExecuted.internalCall_of_fallthrough notImport found restExecuted)
        restContinued
  | callBreakZero next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running
        (calleeExecuted.internalCall_of_break_zero notImport found restExecuted)
        restContinued
  | callReturn next =>
      obtain ⟨_, restExecuted, restContinued⟩ := next.running_inv
      exact .running
        (calleeExecuted.internalCall_of_return notImport found restExecuted)
        restContinued

end StructuredWasmCompletion

/-- The only local side condition needed to replay a structured transition in
Talos: a depth-zero loop branch must actually supply the loop parameters that
the machine retains with `take`.  Every other transition is arity-safe by
construction. -/
def StructuredWasmState.AritySafe (state : StructuredWasmState α) : Prop :=
  match state with
  | ⟨_, .breaking 0 locals,
      .loop paramArity _ _ _ _ :: _⟩ =>
      paramArity ≤ locals.values.length
  | _ => True

mutual

/-- Every loop nested in a Talos program has zero parameter arity.  This is
the control shape currently emitted by the FIR adapter. -/
def WasmProgramHasZeroLoopParams : Wasm.Program → Prop
  | [] => True
  | instruction :: rest =>
      WasmInstructionHasZeroLoopParams instruction ∧
        WasmProgramHasZeroLoopParams rest

/-- Instruction-side component of `Wasm.Program.HasZeroLoopParams`. -/
def WasmInstructionHasZeroLoopParams : Wasm.Instruction → Prop
  | .block _ _ body => WasmProgramHasZeroLoopParams body
  | .loop paramArity _ body =>
      paramArity = 0 ∧ WasmProgramHasZeroLoopParams body
  | .iff _ _ thenBody elseBody =>
      WasmProgramHasZeroLoopParams thenBody ∧
        WasmProgramHasZeroLoopParams elseBody
  | _ => True

end

/-- Every internal function available to a structured call has the same
zero-parameter-loop shape. -/
def WasmModuleHasZeroLoopParams (module : Wasm.Module) : Prop :=
  ∀ function ∈ module.funcs, WasmProgramHasZeroLoopParams function.body

/-- A live frame retains only programs whose nested loops have zero parameter
arity; loop frames additionally expose their own zero arity. -/
def StructuredWasmFrame.HasZeroLoopParams : StructuredWasmFrame → Prop
  | .label _ _ rest => WasmProgramHasZeroLoopParams rest
  | .loop paramArity _ _ body rest =>
      paramArity = 0 ∧ WasmProgramHasZeroLoopParams body ∧
        WasmProgramHasZeroLoopParams rest
  | .call _ _ _ rest => WasmProgramHasZeroLoopParams rest

/-- The executable programs retained by a structured state all satisfy the
adapter's zero-loop-parameter invariant. -/
def StructuredWasmState.HasZeroLoopParams : StructuredWasmState α → Prop
  | ⟨_, .running _ program, frames⟩ =>
      WasmProgramHasZeroLoopParams program ∧
        ∀ frame ∈ frames, frame.HasZeroLoopParams
  | ⟨_, _, frames⟩ =>
      ∀ frame ∈ frames, frame.HasZeroLoopParams

mutual

/-- Every successfully adapted FIR instruction contains only zero-parameter
Talos loops. -/
theorem adapterInstruction_hasZeroLoopParams
    (module : Fir.Wasm.Module) (function : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (source : Fir.Wasm.Instruction)
    {target : Wasm.Instruction}
    (adapted : FirTalos.instruction module function labels source =
      .ok target) :
    WasmInstructionHasZeroLoopParams target := by
  cases source
  case block label body =>
      simp only [FirTalos.instruction] at adapted
      cases bodyEq : FirTalos.instructions module function (label :: labels)
          body with
      | error error =>
          simp [bodyEq, Functor.map, Except.map] at adapted
      | ok targetBody =>
          simp [bodyEq, Functor.map, Except.map] at adapted
          subst target
          exact adapterInstructions_hasZeroLoopParams module function
            (label :: labels) body bodyEq
  case loop label body =>
      simp only [FirTalos.instruction] at adapted
      cases bodyEq : FirTalos.instructions module function (label :: labels)
          body with
      | error error =>
          simp [bodyEq, Functor.map, Except.map] at adapted
      | ok targetBody =>
          simp [bodyEq, Functor.map, Except.map] at adapted
          subst target
          exact ⟨rfl, adapterInstructions_hasZeroLoopParams module function
            (label :: labels) body bodyEq⟩
  case ifElse thenBody elseBody =>
      simp only [FirTalos.instruction] at adapted
      cases thenEq : FirTalos.instructions module function labels thenBody with
      | error error =>
          simp [thenEq, Bind.bind, Except.bind] at adapted
      | ok targetThen =>
          cases elseEq : FirTalos.instructions module function labels elseBody with
          | error error =>
              simp [thenEq, elseEq, Bind.bind, Except.bind, Functor.map,
                Except.map] at adapted
          | ok targetElse =>
              simp [thenEq, elseEq, Bind.bind, Except.bind, Functor.map,
                Except.map, Pure.pure, Except.pure] at adapted
              subst target
              exact ⟨adapterInstructions_hasZeroLoopParams module function
                  labels thenBody thenEq,
                adapterInstructions_hasZeroLoopParams module function labels
                  elseBody elseEq⟩
  case localGet fvarId =>
      simp only [FirTalos.instruction] at adapted
      cases found : FirTalos.findFVar?
          (function.params.toList ++ function.locals.toList) fvarId with
      | none => simp [found, Bind.bind, Except.bind] at adapted
      | some index =>
          simp [found, Pure.pure, Except.pure] at adapted
          subst target
          change True
          trivial
  case localGetObject fvarId =>
      simp only [FirTalos.instruction] at adapted
      cases found : FirTalos.findFVar?
          (function.params.toList ++ function.locals.toList) fvarId with
      | none => simp [found, Bind.bind, Except.bind] at adapted
      | some index =>
          simp [found, Pure.pure, Except.pure] at adapted
          subst target
          change True
          trivial
  case localSet fvarId =>
      simp only [FirTalos.instruction] at adapted
      cases found : FirTalos.findFVar?
          (function.params.toList ++ function.locals.toList) fvarId with
      | none => simp [found, Bind.bind, Except.bind] at adapted
      | some index =>
          simp [found, Pure.pure, Except.pure] at adapted
          subst target
          change True
          trivial
  case call callTarget =>
      simp only [FirTalos.instruction] at adapted
      cases found : FirTalos.callIndex? module callTarget with
      | none => simp [found, Bind.bind, Except.bind] at adapted
      | some index =>
          simp [found, Pure.pure, Except.pure] at adapted
          subst target
          change True
          trivial
  case br label =>
      simp only [FirTalos.instruction] at adapted
      cases found : FirTalos.findLabel? labels label with
      | none => simp [found, Bind.bind, Except.bind] at adapted
      | some index =>
          simp [found, Pure.pure, Except.pure] at adapted
          subst target
          change True
          trivial
  all_goals
    simp_all [FirTalos.instruction, Pure.pure, Except.pure, Bind.bind,
      Except.bind, Functor.map, Except.map]
  all_goals
    subst target
    change True
    trivial
termination_by sizeOf source

/-- The instruction-list adapter preserves the zero-parameter-loop shape. -/
theorem adapterInstructions_hasZeroLoopParams
    (module : Fir.Wasm.Module) (function : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (body : List Fir.Wasm.Instruction)
    {target : Wasm.Program}
    (adapted : FirTalos.instructions module function labels body = .ok target) :
    WasmProgramHasZeroLoopParams target := by
  cases body with
  | nil =>
      simp [FirTalos.instructions, Pure.pure, Except.pure] at adapted
      subst target
      trivial
  | cons source rest =>
      simp only [FirTalos.instructions] at adapted
      cases headEq : FirTalos.instruction module function labels source with
      | error error =>
          simp [headEq, Bind.bind, Except.bind] at adapted
      | ok target =>
          cases tailEq :
              FirTalos.instructions module function labels rest with
          | error error =>
              simp [headEq, tailEq, Bind.bind, Except.bind, Functor.map,
                Except.map] at adapted
          | ok targets =>
              simp [headEq, tailEq, Bind.bind, Except.bind, Functor.map,
                Except.map, Pure.pure, Except.pure] at adapted
              subst_vars
              constructor
              · exact adapterInstruction_hasZeroLoopParams module function
                  labels source headEq
              · exact adapterInstructions_hasZeroLoopParams module function
                  labels rest tailEq
termination_by sizeOf body

end

/-- A successfully adapted FIR function has a target body satisfying the
zero-parameter-loop invariant. -/
theorem adapterFunction_hasZeroLoopParams
    (module : Fir.Wasm.Module) (source : Fir.Wasm.Function)
    {target : Wasm.Function}
    (adapted : FirTalos.function module source = .ok target) :
    WasmProgramHasZeroLoopParams target.body := by
  unfold FirTalos.function at adapted
  cases bodyEq : FirTalos.instructions module source [] source.body with
  | error error =>
      simp [bodyEq, Bind.bind, Except.bind] at adapted
  | ok targetBody =>
      simp [bodyEq, Bind.bind, Except.bind, Pure.pure, Except.pure] at adapted
      subst target
      exact adapterInstructions_hasZeroLoopParams module source [] source.body
        bodyEq

/-- Mapping function adaptation over a source list preserves the body
invariant for every successfully produced target function. -/
theorem adapterFunctions_hasZeroLoopParams
    (module : Fir.Wasm.Module) (sources : List Fir.Wasm.Function)
    {targets : List Wasm.Function}
    (adapted : sources.mapM (FirTalos.function module) = .ok targets) :
    ∀ target ∈ targets, WasmProgramHasZeroLoopParams target.body := by
  induction sources generalizing targets with
  | nil =>
      simp [Pure.pure, Except.pure] at adapted
      subst targets
      simp
  | cons source sources ih =>
      simp only [List.mapM_cons] at adapted
      cases headEq : FirTalos.function module source with
      | error error =>
          simp [headEq, Bind.bind, Except.bind] at adapted
      | ok target =>
          cases tailEq : sources.mapM (FirTalos.function module) with
          | error error =>
              simp [headEq, tailEq, Bind.bind, Except.bind, Functor.map,
                Except.map] at adapted
          | ok targets =>
              simp [headEq, tailEq, Bind.bind, Except.bind, Functor.map,
                Except.map, Pure.pure, Except.pure] at adapted
              subst_vars
              intro candidate member
              simp only [List.mem_cons] at member
              cases member with
              | inl equal =>
                  subst candidate
                  exact adapterFunction_hasZeroLoopParams module source headEq
              | inr member =>
                  exact ih tailEq candidate member

/-- Every module produced successfully by the FIR-to-Talos adapter satisfies
the structured-loop shape used by terminal adequacy.  This is derived from
the adapter implementation; it is not an additional compiler assumption. -/
theorem adapterAdapt_hasZeroLoopParams
    {source : Fir.Wasm.Module} {target : FirTalos.AdaptedModule}
    (adapted : FirTalos.adapt source = .ok target) :
    WasmModuleHasZeroLoopParams target.wasmModule := by
  rcases adapt_preserves_module_layout adapted with
    ⟨functions, functionsEq, layout⟩
  rw [layout]
  exact adapterFunctions_hasZeroLoopParams source source.functions.toList
    functionsEq

/-- The zero-parameter-loop shape discharges the local arity obligation at
every possible structured configuration. -/
theorem StructuredWasmState.aritySafe_of_hasZeroLoopParams
    {state : StructuredWasmState α}
    (shape : state.HasZeroLoopParams) : state.AritySafe := by
  rcases state with ⟨store, control, frames⟩
  cases control with
  | running => trivial
  | returning => trivial
  | halted => trivial
  | breaking level locals =>
      cases level with
      | succ => trivial
      | zero =>
          cases frames with
          | nil => trivial
          | cons frame frames =>
              cases frame with
              | label => trivial
              | call => trivial
              | loop paramArity resultArity belowStack body rest =>
                  have frameShape :
                      (StructuredWasmFrame.loop paramArity resultArity
                        belowStack body rest).HasZeroLoopParams :=
                    shape _ (by simp)
                  have paramZero : paramArity = 0 := by
                    simpa [StructuredWasmFrame.HasZeroLoopParams] using
                      frameShape.1
                  simp [StructuredWasmState.AritySafe, paramZero]

/-- The adapter's zero-loop-parameter shape is invariant under every
structured transition, provided internal callees satisfy the same module-wide
shape. -/
theorem StructuredWasmStep.hasZeroLoopParams
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {before after : StructuredWasmState α}
    (moduleShape : WasmModuleHasZeroLoopParams module)
    (transition : StructuredWasmStep module env before after)
    (beforeShape : before.HasZeroLoopParams) :
    after.HasZeroLoopParams := by
  have bodyShapeOfFound :
      ∀ {index : Nat} {function : Wasm.Function},
        module.funcs[index]? = some function →
        WasmProgramHasZeroLoopParams function.body := by
    intro index function found
    have member : function ∈ module.funcs := by
      exact List.mem_iff_getElem?.mpr ⟨index, found⟩
    exact moduleShape function member
  cases transition <;>
    simp_all [bodyShapeOfFound, StructuredWasmState.HasZeroLoopParams,
      StructuredWasmFrame.HasZeroLoopParams,
      WasmModuleHasZeroLoopParams,
      WasmProgramHasZeroLoopParams,
      WasmInstructionHasZeroLoopParams]
  exact bodyShapeOfFound (by assumption)

namespace StructuredWasmCompletion

/-- Backward adequacy of one arity-safe structured-machine transition.  A
semantic completion of the successor can be collapsed to a completion of the
predecessor. -/
theorem of_step
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {before after : StructuredWasmState α}
    {finalStore : Wasm.Store α} {finalValues : List Wasm.Value}
    (transition : StructuredWasmStep module env before after)
    (safe : before.AritySafe)
    (completion : StructuredWasmCompletion module env after
      finalStore finalValues) :
    StructuredWasmCompletion module env before finalStore finalValues := by
  cases transition with
  | atomic atomic executed =>
      obtain ⟨_, restExecuted, continued⟩ := completion.running_inv
      exact .running (restExecuted.cons_of_fallthrough executed) continued
  | importedCall isImport executed =>
      obtain ⟨_, restExecuted, continued⟩ := completion.running_inv
      exact .running (restExecuted.cons_of_fallthrough executed) continued
  | enterCall notImport found =>
      exact of_enterCall notImport found completion
  | enterBlock =>
      exact of_enterBlock completion
  | enterLoop =>
      exact of_enterLoop completion
  | enterIffThen nonzero =>
      exact of_enterIffThen nonzero completion
  | enterIffElse =>
      exact of_enterIffElse completion
  | leaveLabel =>
      exact .running .empty (.labelFallthrough completion)
  | leaveLoop =>
      exact .running .empty (.loopFallthrough completion)
  | leaveCall =>
      exact .running .empty (.callFallthrough completion)
  | beginBreak =>
      exact .running .beginBreak completion.breaking_inv
  | breakLabelZero =>
      exact .breaking (.labelBreakZero completion)
  | breakLabelSucc =>
      exact .breaking (.labelBreakSucc completion)
  | breakLoopZero =>
      exact .breaking (.loopBreakZero
        (by simpa [StructuredWasmState.AritySafe] using safe) completion)
  | breakLoopSucc =>
      exact .breaking (.loopBreakSucc completion)
  | beginReturn =>
      exact .running .beginReturn completion.returning_inv
  | returnLabel =>
      exact .returning (.labelReturn completion)
  | returnLoop =>
      exact .returning (.loopReturn completion)
  | returnCall =>
      exact .returning (.callReturn completion)
  | haltFallthrough =>
      cases completion
      exact .running .empty .topFallthrough
  | haltReturn =>
      cases completion
      exact .returning .topReturn

/-- Every configuration along a finite structured path satisfies the one
reachable-state arity invariant needed by `of_step`.  The final state needs no
premise because it is never used as a transition source. -/
inductive StructuredWasmPathAritySafe
    {module : Wasm.Module} {env : Wasm.HostEnv α} :
    {count : Nat} → {before after : StructuredWasmState α} →
      FinitePath (StructuredWasmStep module env) count before after → Prop
  | refl (state : StructuredWasmState α) :
      StructuredWasmPathAritySafe (.refl state)
  | cons
      {count : Nat} {before middle after : StructuredWasmState α}
      (head : StructuredWasmStep module env before middle)
      (safe : before.AritySafe)
      (tail : FinitePath (StructuredWasmStep module env) count middle after)
      (tailSafe : StructuredWasmPathAritySafe tail) :
      StructuredWasmPathAritySafe (.cons head tail)

/-- A module whose internal bodies use the adapter's zero-parameter loops
makes every finite structured path arity-safe.  This derives the path evidence
from a compiler-output invariant rather than asking a caller to provide it. -/
theorem StructuredWasmPathAritySafe.of_hasZeroLoopParams
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : StructuredWasmState α}
    {path : FinitePath (StructuredWasmStep module env) count before after}
    (moduleShape : WasmModuleHasZeroLoopParams module)
    (beforeShape : before.HasZeroLoopParams) :
    StructuredWasmPathAritySafe path := by
  induction path with
  | refl => exact .refl _
  | cons head tail ih =>
      have headSafe :=
        StructuredWasmState.aritySafe_of_hasZeroLoopParams beforeShape
      have middleShape :=
        StructuredWasmStep.hasZeroLoopParams moduleShape head beforeShape
      exact .cons head headSafe tail (ih middleShape)

/-- Collapse an entire arity-safe finite path from right to left. -/
theorem of_safePath
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : StructuredWasmState α}
    {finalStore : Wasm.Store α} {finalValues : List Wasm.Value}
    {path : FinitePath (StructuredWasmStep module env) count before after}
    (safe : StructuredWasmPathAritySafe path)
    (completion : StructuredWasmCompletion module env after
      finalStore finalValues) :
    StructuredWasmCompletion module env before finalStore finalValues := by
  induction safe with
  | refl => exact completion
  | cons head headSafe tail tailSafe ih =>
      exact (ih completion).of_step head headSafe

/-- Any arity-safe structured path ending in a halted empty-frame state has an
exact semantic completion from its initial state. -/
theorem of_safePath_to_halted
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before : StructuredWasmState α}
    {finalStore : Wasm.Store α} {finalValues : List Wasm.Value}
    {path : FinitePath (StructuredWasmStep module env) count before
      ⟨finalStore, .halted finalValues, []⟩}
    (safe : StructuredWasmPathAritySafe path) :
    StructuredWasmCompletion module env before finalStore finalValues :=
  of_safePath safe .halted

end StructuredWasmCompletion

/-- Terminal adequacy of the structured machine.  Every finite, arity-safe
path from the canonical entry of a non-imported function to a halted
empty-frame state collapses to the exact Talos `Wasm.run` result, uniformly
above one finite fuel bound. -/
theorem StructuredWasmStep.finitePath_run
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial finalStore : Wasm.Store α} {args finalValues : List Wasm.Value}
    {count : Nat}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    {path : FinitePath (StructuredWasmStep module env) count
      (StructuredWasmState.functionEntry function initial args)
      ⟨finalStore, .halted finalValues, []⟩}
    (safe : StructuredWasmCompletion.StructuredWasmPathAritySafe path) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.run fuel module functionIndex initial args env =
        .Success
          (finalValues.take function.results.length ++
            args.drop function.numParams)
          finalStore := by
  have completion :=
    StructuredWasmCompletion.of_safePath_to_halted safe
  change StructuredWasmCompletion module env
    ⟨initial,
      .running
        (function.toLocals (args.take function.numParams).reverse)
        function.body,
      []⟩ finalStore finalValues at completion
  obtain ⟨_, bodyExecuted, continued⟩ := completion.running_inv
  obtain ⟨bound, bodyStable⟩ := bodyExecuted.stable
  refine ⟨bound, ?_⟩
  intro fuel enough
  rw [Wasm.run_eq notImport]
  simp only [found]
  cases continued with
  | topFallthrough =>
      rw [bodyStable fuel enough]
      rfl
  | topBreakZero =>
      rw [bodyStable fuel enough]
      rfl
  | topReturn =>
      rw [bodyStable fuel enough]
      rfl

/-- Compiler-facing terminal adequacy for the current adapter shape.  The
module invariant derives the internal path-arity evidence automatically, so
the theorem exposes only the generated module, its genuine structured path,
and the resulting `Wasm.run` behavior. -/
theorem StructuredWasmStep.finitePath_run_of_hasZeroLoopParams
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial finalStore : Wasm.Store α} {args finalValues : List Wasm.Value}
    {count : Nat}
    (moduleShape : WasmModuleHasZeroLoopParams module)
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (path : FinitePath (StructuredWasmStep module env) count
      (StructuredWasmState.functionEntry function initial args)
      ⟨finalStore, .halted finalValues, []⟩) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.run fuel module functionIndex initial args env =
        .Success
          (finalValues.take function.results.length ++
            args.drop function.numParams)
          finalStore := by
  have functionMember : function ∈ module.funcs :=
    List.mem_iff_getElem?.mpr
      ⟨functionIndex - module.imports.length, found⟩
  have entryShape :
      StructuredWasmState.HasZeroLoopParams
        (StructuredWasmState.functionEntry function initial args) := by
    exact ⟨moduleShape function functionMember, by simp⟩
  have safe :=
    StructuredWasmCompletion.StructuredWasmPathAritySafe.of_hasZeroLoopParams
      (path := path) moduleShape entryShape
  exact StructuredWasmStep.finitePath_run notImport found safe

/-- Terminal adequacy specialized to a module produced by the FIR-to-Talos
adapter.  Successful adaptation discharges the loop-shape invariant, leaving
only genuine execution facts: function lookup and a finite structured path to
the observed terminal state. -/
theorem StructuredWasmStep.finitePath_run_of_adapt
    {source : Fir.Wasm.Module} {target : FirTalos.AdaptedModule}
    {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial finalStore : Wasm.Store α} {args finalValues : List Wasm.Value}
    {count : Nat}
    (adapted : FirTalos.adapt source = .ok target)
    (notImport : target.wasmModule.imports[functionIndex]? = none)
    (found :
      target.wasmModule.funcs[
        functionIndex - target.wasmModule.imports.length]? = some function)
    (path : FinitePath (StructuredWasmStep target.wasmModule env) count
      (StructuredWasmState.functionEntry function initial args)
      ⟨finalStore, .halted finalValues, []⟩) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.run fuel target.wasmModule functionIndex initial args env =
        .Success
          (finalValues.take function.results.length ++
            args.drop function.numParams)
          finalStore := by
  exact StructuredWasmStep.finitePath_run_of_hasZeroLoopParams
    (adapterAdapt_hasZeroLoopParams adapted) notImport found path

end FirTalos.Correctness
