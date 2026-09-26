import RetainedRC2

open Lean Elab Command

run_cmd do
  liftTermElabM <| Fir.Compiler.Lcnf.Reify.defineDeclEquations
    `RetainedRC2.program `Array.mkEmpty `RetainedInitializer.mkEmptyDecl
  liftTermElabM <| Fir.Compiler.Lcnf.Reify.defineDeclEquations
    `RetainedRC2.program `Array.push `RetainedInitializer.pushDecl
