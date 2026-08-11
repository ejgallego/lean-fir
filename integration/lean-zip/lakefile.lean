import Lake

open Lake DSL

package «LeanZipFir»

require Fir from "../.."

/-- Clean lean-zip source checkout compiled by FIR's pinned Lean toolchain. -/
def leanZipRoot : String :=
  get_config? leanZipRoot |>.getD ".lean-zip"

/-- Clean checkout of lean-zip's pinned `zipCommon` dependency. -/
def zipCommonRoot : String :=
  get_config? zipCommonRoot |>.getD ".zip-common"

lean_lib «ZipForStdSource» where
  srcDir := System.FilePath.mk zipCommonRoot
  globs := #[.submodules `ZipForStd]
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

lean_lib «ZipCommonSource» where
  srcDir := System.FilePath.mk zipCommonRoot
  globs := #[.submodules `ZipCommon]
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

/--
Read-only source view. Build products stay inside this integration project;
FIR never consumes lean-zip's `.lake` products or cross-version final LCNF.
-/
lean_lib «LeanZipSource» where
  srcDir := System.FilePath.mk leanZipRoot
  globs := #[.submodules `Zip]
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

@[default_target]
lean_lib «LeanZipFir»

/-- Binary-safe native oracle compiled from the same real source entry. -/
lean_exe «leanZipFirOracle» where
  root := `Oracle
