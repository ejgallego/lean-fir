import LeanZipFir.CaptureCache

namespace LeanZipFir.CaptureCacheExamples

open Lean

example : CaptureCache.Entry = Fir.Compiler.Lcnf.Checkpoint.Entry := rfl
example : CaptureCache.Entry.mk = Fir.Compiler.Lcnf.Checkpoint.Entry.mk := rfl
example : CaptureCache.Entry.key = Fir.Compiler.Lcnf.Checkpoint.Entry.key := rfl
example : CaptureCache.Entry.artifact = Fir.Compiler.Lcnf.Checkpoint.Entry.artifact := rfl
example : CaptureCache.capturedArtifactExt = Fir.Compiler.Lcnf.Checkpoint.capturedArtifactExt := rfl
example : CaptureCache.add = Fir.Compiler.Lcnf.Checkpoint.add := rfl
example : CaptureCache.getModule? = Fir.Compiler.Lcnf.Checkpoint.getModule? := rfl

end LeanZipFir.CaptureCacheExamples
