import FirTalos.ConcreteTraceSimulation
import FirTalos.Correctness.ResumableWasm
import FirTalos.Correctness.StructuredWasmAdequacy

/-!
# Concrete W6 resumable Wasm machine

This module instantiates the instruction-boundary semantics with the concrete
W6 host.  It is the target machine used by `ConcreteRankedTraceSimulation`;
the generic adequacy theorems in `Correctness.ResumableWasm` then reconnect a
finite completed path to the executable Talos `Wasm.run` result.
-/

namespace FirTalos.Concrete

open FirTalos.Correctness

/-- The actual resumable target for a concrete FIR-generated module. -/
def concreteResumableWasmMachine
    (module : Wasm.Module) (env : Wasm.HostEnv Host) :
    ConcreteResumableMachine where
  State := ResumableWasmState Host
  step := ResumableWasmStep module env
  store := ResumableWasmState.store

@[simp] theorem concreteResumableWasmMachine_store
    (module : Wasm.Module) (env : Wasm.HostEnv Host)
    (state : ResumableWasmState Host) :
    (concreteResumableWasmMachine module env).store state = state.store :=
  rfl

/-- The frame-stack target that exposes progress inside emitted calls and
structured control. -/
def concreteStructuredWasmMachine
    (module : Wasm.Module) (env : Wasm.HostEnv Host) :
    ConcreteResumableMachine where
  State := StructuredWasmState Host
  step := StructuredWasmStep module env
  store := StructuredWasmState.store

@[simp] theorem concreteStructuredWasmMachine_store
    (module : Wasm.Module) (env : Wasm.HostEnv Host)
    (state : StructuredWasmState Host) :
    (concreteStructuredWasmMachine module env).store state = state.store :=
  rfl

/-- The exact compiler proof object now has a concrete instruction-boundary
target.  This abbreviation keeps module and host selection explicit at the
public theorem boundary. -/
def ConcreteGeneratedTraceSimulation
    (externals : Fir.LeanIR.Impure.ExternalImpl) (module : Wasm.Module)
    (env : Wasm.HostEnv Host) : Type :=
  ConcreteRankedTraceSimulation externals
    (concreteStructuredWasmMachine module env)

end FirTalos.Concrete
