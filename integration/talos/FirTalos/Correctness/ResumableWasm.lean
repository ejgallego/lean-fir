import FirTalos.Correctness.WeakSimulation
import Interpreter.Wasm.Semantics.Lemmas

/-!
# Resumable instruction-boundary Wasm execution

Talos's executable semantics exposes the next store and locals after every
successful `execOne`, but its fuel-bounded `exec` and `run` entry points erase
the in-flight configuration when they return `OutOfFuel`.  This module keeps
exactly the state that Talos actually exposes: a store, locals, and the
remaining outer instruction list.

One transition consumes an instruction only when some finite Talos fuel runs
it to `Fallthrough`.  Structured instructions and calls remain atomic at this
boundary; inventing a resumable state inside them would not be justified by
the current evaluator.  Fuel monotonicity lets a finite path choose one common
bound, yielding an exact adequacy theorem for `exec` and successful `run`.
-/

namespace FirTalos.Correctness

/-- The configuration retained between outer instruction boundaries. -/
structure ResumableWasmState (α : Type) where
  store : Wasm.Store α
  locals : Wasm.Locals
  program : Wasm.Program

/-- A genuine resumable transition: one outer instruction completed normally
and exposed the next store and locals.  The witnessing fuel is proof evidence,
not mutable machine state. -/
inductive ResumableWasmStep (module : Wasm.Module) (env : Wasm.HostEnv α) :
    ResumableWasmState α → ResumableWasmState α → Prop where
  | fallthrough
      {fuel : Nat} {store nextStore : Wasm.Store α}
      {locals nextLocals : Wasm.Locals}
      {instruction : Wasm.Instruction} {rest : Wasm.Program}
      (executed :
        Wasm.execOne fuel module store locals instruction env =
          .Fallthrough nextStore nextLocals) :
      ResumableWasmStep module env
        ⟨store, locals, instruction :: rest⟩
        ⟨nextStore, nextLocals, rest⟩

/-- The instruction-boundary transition system, with the current store as its
observation.  W6 later refines that store observation to world and trace. -/
def resumableWasmSystem (module : Wasm.Module) (env : Wasm.HostEnv α) :
    ObservableTransitionSystem where
  State := ResumableWasmState α
  Observation := Wasm.Store α
  step := ResumableWasmStep module env
  observe := ResumableWasmState.store

namespace ResumableWasmStep

/-- Every finite instruction-boundary path has a single fuel bound above
which running the whole program before the path is exactly the same as
running the residual program after it. -/
theorem finitePath_exec_eq
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : ResumableWasmState α}
    (path : FinitePath (ResumableWasmStep module env) count before after) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module before.store before.locals before.program env =
        Wasm.exec fuel module after.store after.locals after.program env := by
  induction path with
  | refl =>
      exact ⟨0, fun _fuel _enough => rfl⟩
  | @cons before middle after count head tail ih =>
      cases head with
      | @fallthrough stepFuel store nextStore locals nextLocals instruction rest executed =>
          obtain ⟨tailBound, tailStable⟩ := ih
          refine ⟨Nat.max stepFuel tailBound, ?_⟩
          intro fuel enough
          have stepEnough : stepFuel ≤ fuel :=
            Nat.le_trans (Nat.le_max_left stepFuel tailBound) enough
          have tailEnough : tailBound ≤ fuel :=
            Nat.le_trans (Nat.le_max_right stepFuel tailBound) enough
          have notOutOfFuel :
              Wasm.execOne stepFuel module store locals instruction env ≠
                .OutOfFuel := by
            rw [executed]
            intro impossible
            cases impossible
          have stepAtFuel :=
            Wasm.execOne_fuel_mono stepEnough notOutOfFuel
          rw [executed] at stepAtFuel
          simp only [Wasm.exec, stepAtFuel]
          exact tailStable fuel tailEnough

/-- Reaching an empty residual program agrees with a Talos fallthrough for
all sufficiently large fuels. -/
theorem finitePath_exec_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : ResumableWasmState α}
    (path : FinitePath (ResumableWasmStep module env) count before after)
    (completed : after.program = []) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module before.store before.locals before.program env =
        .Fallthrough after.store after.locals := by
  obtain ⟨bound, stable⟩ := finitePath_exec_eq path
  refine ⟨bound, ?_⟩
  intro fuel enough
  rw [stable fuel enough, completed]
  simp only [Wasm.exec]

/-- If the next residual instruction returns, the path plus that terminal
instruction agrees with the corresponding Talos `exec` result above one
common fuel bound.  This is the exit shape emitted for LCNF `.return`. -/
theorem finitePath_exec_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : ResumableWasmState α}
    {exitFuel : Nat} {instruction : Wasm.Instruction} {rest : Wasm.Program}
    {finalStore : Wasm.Store α} {values : List Wasm.Value}
    (path : FinitePath (ResumableWasmStep module env) count before after)
    (atExit : after.program = instruction :: rest)
    (returned :
      Wasm.execOne exitFuel module after.store after.locals instruction env =
        .Return finalStore values) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module before.store before.locals before.program env =
        .Return finalStore values := by
  obtain ⟨prefixBound, prefixStable⟩ := finitePath_exec_eq path
  refine ⟨Nat.max prefixBound exitFuel, ?_⟩
  intro fuel enough
  have prefixEnough : prefixBound ≤ fuel :=
    Nat.le_trans (Nat.le_max_left prefixBound exitFuel) enough
  have exitEnough : exitFuel ≤ fuel :=
    Nat.le_trans (Nat.le_max_right prefixBound exitFuel) enough
  have notOutOfFuel :
      Wasm.execOne exitFuel module after.store after.locals instruction env ≠
        .OutOfFuel := by
    rw [returned]
    intro impossible
    cases impossible
  have exitAtFuel := Wasm.execOne_fuel_mono exitEnough notOutOfFuel
  rw [returned] at exitAtFuel
  rw [prefixStable fuel prefixEnough, atExit]
  simp only [Wasm.exec, exitAtFuel]

/-- Direct emitted-code specialization: a residual `.ret` returns the current
operand stack and store. -/
theorem finitePath_exec_ret
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : ResumableWasmState α}
    {rest : Wasm.Program}
    (path : FinitePath (ResumableWasmStep module env) count before after)
    (atExit : after.program = .ret :: rest) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module before.store before.locals before.program env =
        .Return after.store after.locals.values := by
  apply finitePath_exec_return (exitFuel := 1) path atExit
  simp only [Wasm.execOne.eq_def]

/-- A finite prefix whose next residual instruction branches agrees with the
corresponding Talos break continuation above one common fuel bound. -/
theorem finitePath_exec_break
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : ResumableWasmState α}
    {exitFuel level : Nat} {instruction : Wasm.Instruction}
    {rest : Wasm.Program} {finalStore : Wasm.Store α}
    {finalLocals : Wasm.Locals}
    (path : FinitePath (ResumableWasmStep module env) count before after)
    (atExit : after.program = instruction :: rest)
    (branched :
      Wasm.execOne exitFuel module after.store after.locals instruction env =
        .Break level finalStore finalLocals) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module before.store before.locals before.program env =
        .Break level finalStore finalLocals := by
  obtain ⟨prefixBound, prefixStable⟩ := finitePath_exec_eq path
  refine ⟨Nat.max prefixBound exitFuel, ?_⟩
  intro fuel enough
  have prefixEnough : prefixBound ≤ fuel :=
    Nat.le_trans (Nat.le_max_left prefixBound exitFuel) enough
  have exitEnough : exitFuel ≤ fuel :=
    Nat.le_trans (Nat.le_max_right prefixBound exitFuel) enough
  have notOutOfFuel :
      Wasm.execOne exitFuel module after.store after.locals instruction env ≠
        .OutOfFuel := by
    rw [branched]
    intro impossible
    cases impossible
  have exitAtFuel := Wasm.execOne_fuel_mono exitEnough notOutOfFuel
  rw [branched] at exitAtFuel
  rw [prefixStable fuel prefixEnough, atExit]
  simp only [Wasm.exec, exitAtFuel]

/-- Direct symbolic-compiler specialization for a residual branch. -/
theorem finitePath_exec_br
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {count : Nat} {before after : ResumableWasmState α}
    {level : Nat} {rest : Wasm.Program}
    (path : FinitePath (ResumableWasmStep module env) count before after)
    (atExit : after.program = .br level :: rest) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.exec fuel module before.store before.locals before.program env =
        .Break level after.store after.locals := by
  apply finitePath_exec_break (exitFuel := 1) path atExit
  simp only [Wasm.execOne.eq_def]

end ResumableWasmStep

/-- Canonical resumable entry configuration for a non-imported function. -/
def ResumableWasmState.functionEntry
    (function : Wasm.Function) (initial : Wasm.Store α)
    (args : List Wasm.Value) : ResumableWasmState α :=
  { store := initial
    locals := function.toLocals (args.take function.numParams).reverse
    program := function.body }

/-- A completed instruction-boundary path ending by fallthrough is exactly a
successful Talos function run, uniformly above a finite fuel bound. -/
theorem ResumableWasmStep.finitePath_run_fallthrough
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store α} {args : List Wasm.Value}
    {count : Nat} {after : ResumableWasmState α}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (path : FinitePath (ResumableWasmStep module env) count
      (ResumableWasmState.functionEntry function initial args) after)
    (completed : after.program = []) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.run fuel module functionIndex initial args env =
        .Success
          (after.locals.values.take function.results.length ++
            args.drop function.numParams)
          after.store := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_fallthrough path completed
  refine ⟨bound, ?_⟩
  intro fuel enough
  have bodyRuns' :
      Wasm.exec fuel module initial
          (function.toLocals (args.take function.numParams).reverse)
          function.body env =
        .Fallthrough after.store after.locals := by
    simpa [ResumableWasmState.functionEntry] using bodyRuns fuel enough
  rw [Wasm.run_eq notImport]
  simp only [found]
  rw [bodyRuns']

/-- A finite instruction-boundary path whose next instruction returns is
exactly a successful Talos function run, uniformly above a finite fuel bound.
This is the adequacy theorem used by FIR's generated `.ret` exit. -/
theorem ResumableWasmStep.finitePath_run_return
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store α} {args : List Wasm.Value}
    {count : Nat} {after : ResumableWasmState α}
    {exitFuel : Nat} {instruction : Wasm.Instruction} {rest : Wasm.Program}
    {finalStore : Wasm.Store α} {values : List Wasm.Value}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (path : FinitePath (ResumableWasmStep module env) count
      (ResumableWasmState.functionEntry function initial args) after)
    (atExit : after.program = instruction :: rest)
    (returned :
      Wasm.execOne exitFuel module after.store after.locals instruction env =
        .Return finalStore values) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.run fuel module functionIndex initial args env =
        .Success
          (values.take function.results.length ++ args.drop function.numParams)
          finalStore := by
  obtain ⟨bound, bodyRuns⟩ :=
    ResumableWasmStep.finitePath_exec_return path atExit returned
  refine ⟨bound, ?_⟩
  intro fuel enough
  have bodyRuns' :
      Wasm.exec fuel module initial
          (function.toLocals (args.take function.numParams).reverse)
          function.body env =
        .Return finalStore values := by
    simpa [ResumableWasmState.functionEntry] using bodyRuns fuel enough
  rw [Wasm.run_eq notImport]
  simp only [found]
  rw [bodyRuns']

/-- Direct compiler-exit adequacy: a path to the generated `.ret` is exactly
a successful Talos run with the current stack and store. -/
theorem ResumableWasmStep.finitePath_run_ret
    {module : Wasm.Module} {env : Wasm.HostEnv α}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store α} {args : List Wasm.Value}
    {count : Nat} {after : ResumableWasmState α} {rest : Wasm.Program}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (path : FinitePath (ResumableWasmStep module env) count
      (ResumableWasmState.functionEntry function initial args) after)
    (atExit : after.program = .ret :: rest) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Wasm.run fuel module functionIndex initial args env =
        .Success
          (after.locals.values.take function.results.length ++
            args.drop function.numParams)
          after.store := by
  apply ResumableWasmStep.finitePath_run_return
      notImport found path atExit (exitFuel := 1)
  simp only [Wasm.execOne.eq_def]

end FirTalos.Correctness
