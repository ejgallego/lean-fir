module

public import Lean.Compiler.LCNF.Specialize
public import Lean.EnvExtension
import all Lean.Compiler.LCNF.Specialize

public section

namespace Fir.Wasm.Emit.CompilerPrivate

open Lean
open Lean.Compiler

/--
Forget imported specialization-name mappings inside an already isolated
compiler environment.  Lean can then rebuild those private helpers from the
source declarations visible to the ordinary LCNF pipeline.
-/
def clearSpecializationCache (env : Environment) : Environment :=
  SimplePersistentEnvExtension.setState LCNF.Specialize.specCacheExt env {}

end Fir.Wasm.Emit.CompilerPrivate
