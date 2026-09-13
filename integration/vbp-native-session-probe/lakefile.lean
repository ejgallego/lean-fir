import Lake
open Lake DSL

package FirVbpNativeSessionProbe where
  leanOptions := #[⟨`experimental.module, true⟩]

require Fir from "../../.deps/native-session-probe/sources/fir"
require verso from "../../.deps/native-session-probe/sources/verso"
require lean_vir from "../../.deps/native-session-probe/sources/lean_vir"
require «verso-react» from
  "../../.deps/native-session-probe/sources/vbp/packages/verso-react"

lean_lib NativeSessionSource where
  srcDir := "../../.deps/native-session-probe/sources/vbp/src"
  roots := #[`VersoBlueprint, `VersoBlueprintVir]
  requiresModuleSystem := true
  leanOptions := #[⟨`compiler.postponeCompile, true⟩]

@[default_target]
lean_lib Probe
