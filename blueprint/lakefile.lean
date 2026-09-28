import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "19451b009e306e7436b82f4d9093c4d15f8cdfd8"
require FirTalos from "../.deps/talos-434/project"

package FirBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib FirBlueprint
