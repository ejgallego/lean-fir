import FirTalos.Correctness.StructuredWasmFrames

/-!
# Emitted-subset structured Wasm machine

This machine exposes progress inside the control instructions emitted by FIR's
adapter.  Its state owns a Talos store, an explicit running/control mode, and a
stack of block, loop, and call frames.  It is intentionally not a second
general Wasm interpreter: ordinary instructions and imported calls still use
Talos `execOne`, while direct in-module calls and structured control are
reified.
-/

namespace FirTalos.Correctness

/-- Continuations needed by the adapted FIR instruction subset. -/
inductive StructuredWasmFrame where
  /-- Block and conditional bodies share the same exit/branch behavior. -/
  | label (resultArity : Nat) (belowStack : List Wasm.Value)
      (rest : Wasm.Program)
  /-- A branch to depth zero restarts this body with `paramArity` values. -/
  | loop (paramArity resultArity : Nat) (belowStack : List Wasm.Value)
      (body rest : Wasm.Program)
  /-- A direct in-module call returns into the caller's locals and residual
  program using Talos's exact result/remainder convention. -/
  | call (resultArity : Nat) (callerRemainder : List Wasm.Value)
      (callerLocals : Wasm.Locals) (rest : Wasm.Program)
  deriving Inhabited

/-- Running code, an outward branch, a function return in flight, or a final
top-level value stack. -/
inductive StructuredWasmControl where
  | running (locals : Wasm.Locals) (program : Wasm.Program)
  | breaking (level : Nat) (locals : Wasm.Locals)
  | returning (values : List Wasm.Value)
  | halted (values : List Wasm.Value)
  deriving Inhabited

/-- Full resumable target configuration for the emitted subset. -/
structure StructuredWasmState (α : Type) where
  store : Wasm.Store α
  control : StructuredWasmControl
  frames : List StructuredWasmFrame := []

/-- Instructions whose internal control is not reified by this machine. -/
def IsEmittedAtomicInstruction : Wasm.Instruction → Prop
  | .block _ _ _ | .loop _ _ _ | .iff _ _ _ _ | .br _ | .call _ | .ret => False
  | _ => True

/-- Small-step execution for the adapter's emitted control subset. -/
inductive StructuredWasmStep (module : Wasm.Module) (env : Wasm.HostEnv α) :
    StructuredWasmState α → StructuredWasmState α → Prop where
  /-- Talos remains authoritative for ordinary instructions. -/
  | atomic
      {fuel : Nat} {store nextStore : Wasm.Store α}
      {locals nextLocals : Wasm.Locals}
      {instruction : Wasm.Instruction} {rest : Wasm.Program}
      {frames : List StructuredWasmFrame}
      (atomic : IsEmittedAtomicInstruction instruction)
      (executed :
        Wasm.execOne fuel module store locals instruction env =
          .Fallthrough nextStore nextLocals) :
      StructuredWasmStep module env
        ⟨store, .running locals (instruction :: rest), frames⟩
        ⟨nextStore, .running nextLocals rest, frames⟩
  /-- Imported functions are terminating host invocations and remain atomic. -/
  | importedCall
      {fuel id : Nat} {imp : Wasm.ImportDecl}
      {store nextStore : Wasm.Store α} {locals nextLocals : Wasm.Locals}
      {rest : Wasm.Program} {frames : List StructuredWasmFrame}
      (isImport : module.imports[id]? = some imp)
      (executed :
        Wasm.execOne fuel module store locals (.call id) env =
          .Fallthrough nextStore nextLocals) :
      StructuredWasmStep module env
        ⟨store, .running locals (.call id :: rest), frames⟩
        ⟨nextStore, .running nextLocals rest, frames⟩
  /-- An in-module call pushes the caller continuation and enters the callee. -/
  | enterCall
      {id : Nat} {function : Wasm.Function} {store : Wasm.Store α}
      {locals : Wasm.Locals} {rest : Wasm.Program}
      {frames : List StructuredWasmFrame}
      (notImport : module.imports[id]? = none)
      (found : module.funcs[id - module.imports.length]? = some function) :
      StructuredWasmStep module env
        ⟨store, .running locals (.call id :: rest), frames⟩
        ⟨store,
          .running
            (function.toLocals
              (locals.values.take function.numParams).reverse)
            function.body,
          .call function.results.length
              (locals.values.drop function.numParams) locals rest :: frames⟩
  /-- Enter a block and remember its stack mark and residual program. -/
  | enterBlock
      {paramArity resultArity : Nat} {body rest : Wasm.Program}
      {store : Wasm.Store α} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store,
          .running locals (.block paramArity resultArity body :: rest), frames⟩
        ⟨store, .running locals body,
          .label resultArity (locals.values.drop paramArity) rest :: frames⟩
  /-- Enter a loop; its frame retains the body for `br 0` restart. -/
  | enterLoop
      {paramArity resultArity : Nat} {body rest : Wasm.Program}
      {store : Wasm.Store α} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store,
          .running locals (.loop paramArity resultArity body :: rest), frames⟩
        ⟨store, .running locals body,
          .loop paramArity resultArity (locals.values.drop paramArity)
            body rest :: frames⟩
  /-- Select and enter the nonzero conditional body after popping the
  condition. -/
  | enterIffThen
      {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
      {store : Wasm.Store α} {locals : Wasm.Locals}
      {condition : UInt32} {values : List Wasm.Value}
      {frames : List StructuredWasmFrame}
      (nonzero : condition ≠ 0) :
      StructuredWasmStep module env
        ⟨store, .running { locals with values := .i32 condition :: values }
          (.iff paramArity resultArity thenBody elseBody :: rest), frames⟩
        ⟨store, .running { locals with values := values } thenBody,
          .label resultArity (values.drop paramArity) rest :: frames⟩
  /-- Select and enter the zero conditional body. -/
  | enterIffElse
      {paramArity resultArity : Nat} {thenBody elseBody rest : Wasm.Program}
      {store : Wasm.Store α} {locals : Wasm.Locals}
      {values : List Wasm.Value} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .running { locals with values := .i32 0 :: values }
          (.iff paramArity resultArity thenBody elseBody :: rest), frames⟩
        ⟨store, .running { locals with values := values } elseBody,
          .label resultArity (values.drop paramArity) rest :: frames⟩
  /-- Normal block/conditional fallthrough restores the saved stack mark. -/
  | leaveLabel
      {resultArity : Nat} {belowStack : List Wasm.Value}
      {rest : Wasm.Program} {store : Wasm.Store α} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .running locals [],
          .label resultArity belowStack rest :: frames⟩
        ⟨store,
          .running
            { locals with
              values := locals.values.take resultArity ++ belowStack }
            rest,
          frames⟩
  /-- Normal loop fallthrough exits rather than restarting the loop. -/
  | leaveLoop
      {paramArity resultArity : Nat} {belowStack : List Wasm.Value}
      {body rest : Wasm.Program} {store : Wasm.Store α}
      {locals : Wasm.Locals} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .running locals [],
          .loop paramArity resultArity belowStack body rest :: frames⟩
        ⟨store,
          .running
            { locals with
              values := locals.values.take resultArity ++ belowStack }
            rest,
          frames⟩
  /-- Function fallthrough returns through the saved call continuation. -/
  | leaveCall
      {resultArity : Nat} {callerRemainder : List Wasm.Value}
      {callerLocals locals : Wasm.Locals} {rest : Wasm.Program}
      {store : Wasm.Store α} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .running locals [],
          .call resultArity callerRemainder callerLocals rest :: frames⟩
        ⟨store,
          .running
            { callerLocals with
              values := locals.values.take resultArity ++ callerRemainder }
            rest,
          frames⟩
  /-- A branch abandons the current residual body and begins frame unwinding. -/
  | beginBreak
      {level : Nat} {rest : Wasm.Program} {store : Wasm.Store α}
      {locals : Wasm.Locals} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .running locals (.br level :: rest), frames⟩
        ⟨store, .breaking level locals, frames⟩
  /-- Depth-zero branch exits a block/conditional. -/
  | breakLabelZero
      {resultArity : Nat} {belowStack : List Wasm.Value}
      {rest : Wasm.Program} {store : Wasm.Store α} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .breaking 0 locals,
          .label resultArity belowStack rest :: frames⟩
        ⟨store,
          .running
            { locals with
              values := locals.values.take resultArity ++ belowStack }
            rest,
          frames⟩
  /-- Crossing a non-target label decrements the branch depth. -/
  | breakLabelSucc
      {level resultArity : Nat} {belowStack : List Wasm.Value}
      {rest : Wasm.Program} {store : Wasm.Store α} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .breaking (level + 1) locals,
          .label resultArity belowStack rest :: frames⟩
        ⟨store, .breaking level locals, frames⟩
  /-- Depth-zero branch to a loop starts its next iteration and retains the
  loop frame. -/
  | breakLoopZero
      {paramArity resultArity : Nat} {belowStack : List Wasm.Value}
      {body rest : Wasm.Program} {store : Wasm.Store α}
      {locals : Wasm.Locals} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .breaking 0 locals,
          .loop paramArity resultArity belowStack body rest :: frames⟩
        ⟨store,
          .running
            { locals with
              values := locals.values.take paramArity ++ belowStack }
            body,
          .loop paramArity resultArity belowStack body rest :: frames⟩
  /-- Crossing a non-target loop decrements the branch depth. -/
  | breakLoopSucc
      {level paramArity resultArity : Nat} {belowStack : List Wasm.Value}
      {body rest : Wasm.Program} {store : Wasm.Store α}
      {locals : Wasm.Locals} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .breaking (level + 1) locals,
          .loop paramArity resultArity belowStack body rest :: frames⟩
        ⟨store, .breaking level locals, frames⟩
  /-- `.ret` abandons the current residual body and begins function-frame
  unwinding. -/
  | beginReturn
      {rest : Wasm.Program} {store : Wasm.Store α} {locals : Wasm.Locals}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .running locals (.ret :: rest), frames⟩
        ⟨store, .returning locals.values, frames⟩
  /-- Returns ignore nested block/conditional frames. -/
  | returnLabel
      {values : List Wasm.Value} {resultArity : Nat}
      {belowStack : List Wasm.Value} {rest : Wasm.Program}
      {store : Wasm.Store α} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .returning values,
          .label resultArity belowStack rest :: frames⟩
        ⟨store, .returning values, frames⟩
  /-- Returns ignore nested loop frames. -/
  | returnLoop
      {values : List Wasm.Value} {paramArity resultArity : Nat}
      {belowStack : List Wasm.Value} {body rest : Wasm.Program}
      {store : Wasm.Store α} {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .returning values,
          .loop paramArity resultArity belowStack body rest :: frames⟩
        ⟨store, .returning values, frames⟩
  /-- A callee return resumes its caller with the exact Wasm result stack. -/
  | returnCall
      {values : List Wasm.Value} {resultArity : Nat}
      {callerRemainder : List Wasm.Value} {callerLocals : Wasm.Locals}
      {rest : Wasm.Program} {store : Wasm.Store α}
      {frames : List StructuredWasmFrame} :
      StructuredWasmStep module env
        ⟨store, .returning values,
          .call resultArity callerRemainder callerLocals rest :: frames⟩
        ⟨store,
          .running
            { callerLocals with
              values := values.take resultArity ++ callerRemainder }
            rest,
          frames⟩
  /-- Top-level fallthrough exposes the final value stack. -/
  | haltFallthrough
      {store : Wasm.Store α} {locals : Wasm.Locals} :
      StructuredWasmStep module env
        ⟨store, .running locals [], []⟩
        ⟨store, .halted locals.values, []⟩
  /-- Top-level explicit return exposes the returned value stack. -/
  | haltReturn
      {store : Wasm.Store α} {values : List Wasm.Value} :
      StructuredWasmStep module env
        ⟨store, .returning values, []⟩
        ⟨store, .halted values, []⟩

/-- The structured target system observes the concrete store at every
administrative and computational configuration. -/
def structuredWasmSystem (module : Wasm.Module) (env : Wasm.HostEnv α) :
    ObservableTransitionSystem where
  State := StructuredWasmState α
  Observation := Wasm.Store α
  step := StructuredWasmStep module env
  observe := StructuredWasmState.store

/-- Canonical top-level function entry before any frame is pushed. -/
def StructuredWasmState.functionEntry
    (function : Wasm.Function) (initial : Wasm.Store α)
    (args : List Wasm.Value) : StructuredWasmState α :=
  { store := initial
    control := .running
      (function.toLocals (args.take function.numParams).reverse)
      function.body }

end FirTalos.Correctness
