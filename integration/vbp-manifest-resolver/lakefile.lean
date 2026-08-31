import Lake

open Lake DSL

package «FirVbpManifestResolver»

/-
The FIR dependency is a package-script-managed clean archive. Keeping it
outside the active W7 checkout prevents Lean 4.34 build products from entering
the worktree's Lean 4.33 `.lake` state.
-/
require Fir from "../../.deps/source-views/fir-vbp-manifest-resolver"

def vbpRoot : String :=
  get_config? vbpRoot |>.getD
    "../../.deps/source-views/vbp-manifest-resolver-1af64db2"

/-- Compile only the portable resolver source and postpone native lowering. -/
lean_lib «VbpManifestResolverSource» where
  srcDir := System.FilePath.mk vbpRoot / "src"
  roots := #[`VersoBlueprintRuntime.ManifestResolver]
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

@[default_target]
lean_lib «FirVbpManifestResolver»
