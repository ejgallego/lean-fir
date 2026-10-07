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

`Fir.Compiler.LCNF.Checkpoint` retains one named `Artifact` in its owning olean
using Lean's persistent environment extension. `add key artifact` is used
during module construction; `getModule? module key` reads only that imported
module's entries, including from a native consumer using `loadExts := false`.
Missing modules/keys return `none`, without searching another module's merged
state. This extracts the existing lean-zip mechanism; its `CaptureCache` names
remain compatible forwards to the single implementation.

Checkpoint oleans are ordinary current-toolchain Lake outputs. Rebuild their
dependencies after changes; do not use them as cross-version source archives.
This primitive does not define a Wasm output target, runtime/linker policy,
package cache, or publication registry. Those remain consumer responsibilities.

Run the focused checkpoint regression from the FIR root:

```sh
bash Fir/Compiler/LCNF/check-checkpoint.sh
```

It builds real identity/addition captures and their independent kernel-checked
AST references, then reads their oleans in a fresh process without recapture.
It checks full program fields/metadata, sorted export, same-key module isolation
and missing module/key rejection with `loadExts` both false and true. The
lean-zip compatibility module checks every forwarded type, constructor,
projection, extension and function by definitional equality. No Lean pin,
application source, runtime contract or Artifact schema changes are involved.

CG-01 deliberately preserves eager form collection and the existing
`ModuleArtifact.formattedLcnf` behavior. Optional diagnostics, a canonical
driver over the capture providers and indexed analyses remain later slices.
Source-unit/SCC boundaries, runtime contracts, and lowering policy are unchanged.

`Fir.Wasm.Emit.SourceDependencyExamples` checks the actual imported Lean
environment contains no `Fir.Validation` modules and checks compatibility
aliases by definitional equality. It runs in the existing W7 artifact gate.
