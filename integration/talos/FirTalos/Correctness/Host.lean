import FirTalos.Correctness.Adapter
import FirTalos.Runtime

namespace FirTalos.Correctness

/-- The resolver retains one semantic host operation per source import, in order. -/
def HostsMatch (resolved : ResolvedHosts) (source : Fir.Wasm.Module) : Prop :=
  resolved.operations.length = source.imports.size

/--
Import-count preservation packages the concrete host environment as a Talos
`HostEnv.Satisfies` witness for the adapted module.
-/
theorem resolvedHosts_satisfy_adapted
    {source : Fir.Wasm.Module} {target : AdaptedModule} {resolved : ResolvedHosts}
    (adapted : adapt source = .ok target)
    (alignment : HostsMatch resolved source) :
    resolved.env.Satisfies target.wasmModule resolved.spec := by
  apply resolved.satisfies
  calc
    target.wasmModule.imports.length = source.imports.size :=
      adapt_preserves_import_count adapted
    _ = resolved.operations.length := alignment.symm

/-- The concrete host contract is exact, not merely an over-approximation. -/
theorem hostContract_iff (operation : HostOperation) (initial args result) :
    hostContract operation initial args result ↔
      result = hostStep operation initial args := by
  rfl

end FirTalos.Correctness
