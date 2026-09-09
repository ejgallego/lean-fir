# Production capture

`Fir.Compiler.LCNF` owns the final-impure-LCNF `Artifact`, `compileEntry`,
form-name collection, and textual formatting. It depends on the program
representation and upstream compiler, not the validation corpus or interpreter.
`Fir.Wasm.Emit.Source` supplies the existing source-unit/internalization
providers and Wasm compilation APIs above this module.

Validation execution, coverage requirements, and telemetry remain in
`Fir.Validation.LCNF`. Corpus-driven Wasm callers import
`Fir.Validation.WasmSource` for `withValidationInvocation` and
`compileValidationInvocation`; those functions retain their existing
`Fir.Wasm.Emit.Source` names. Production callers import `Fir.Wasm.Emit.Source`.

The old `Fir.Validation.Lcnf.Artifact`, `compileEntry`, `collectForms`, and
artifact constructor/projection/format names are compatibility aliases in the
production module. Existing package generators need not import validation or
migrate all their type annotations together. There is only one implementation.

CG-01 deliberately preserves eager form collection and the existing
`ModuleArtifact.formattedLcnf` behavior. Optional diagnostics, a canonical
driver over the capture providers, caching, and indexed analyses are later
slices. Source-unit/SCC boundaries, runtime contracts, and lowering policy do
not change in this extraction.

`Fir.Wasm.Emit.SourceDependencyExamples` checks the actual imported Lean
environment contains no `Fir.Validation` modules and checks compatibility
aliases by definitional equality. It runs in the existing W7 artifact gate.
