import Fir.Compiler.LCNF.Checkpoint

/-! Compatibility names for the production olean checkpoint mechanism.
There is one implementation and one persistent extension, owned by the compiler.
Rebuild dependent oleans with Lake after this extraction; checkpoints are
current-toolchain build products, not a cross-version interchange format. -/
namespace LeanZipFir.CaptureCache

export Fir.Compiler.Lcnf.Checkpoint (Entry capturedArtifactExt add getModule?)

namespace Entry
export Fir.Compiler.Lcnf.Checkpoint.Entry (mk key artifact)
end Entry

end LeanZipFir.CaptureCache
