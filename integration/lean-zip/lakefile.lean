import Lake

open System Lake DSL

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

/--
Native-oracle support from the exact lean-zip source view. The FIR Wasm path
does not link this object: its fixed-width and ByteArray operations remain
module-resident. The native executable needs the same optimized externs as
lean-zip's own `zip-wasm-oracle`.
-/
input_file leanZipByteArrayWideFFI.c where
  path := System.FilePath.mk leanZipRoot / "c" / "bytearray_wide_ffi.c"
  text := true

target leanZipByteArrayWideFFI.o pkg : FilePath := do
  let source ← leanZipByteArrayWideFFI.c.fetch
  let object := pkg.buildDir / "c" / "bytearray_wide_ffi.o"
  let flags := #["-O2", "-DNDEBUG"] ++
    if Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO object source #[] flags

extern_lib libLeanZipByteArrayWideFFI pkg := do
  let object ← leanZipByteArrayWideFFI.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "lean_zip_bytearray_wide_ffi")
    #[object]

@[default_target]
lean_lib «LeanZipFir»

/-- Binary-safe native oracle compiled from the same real source entry. -/
lean_exe «leanZipFirOracle» where
  root := `Oracle
