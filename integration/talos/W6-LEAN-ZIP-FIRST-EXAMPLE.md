# First W6 lean-zip example: captured stored-block compressor

## Target and boundary

Prove the actual final impure LCNF captured for
`Zip.Wasm.compressStored : ByteArray → ByteArray`, then connect its compiled
execution to WebAssembly. `LeanZipFir.Compile.captureStored` obtains a
`Fir.Validation.Lcnf.Artifact` from the real lean-zip source environment; its
`program` is the proof input. This is not a hand-written FIR lookalike and does
not require a Lean-source-to-LCNF correctness theorem. The stored entry is the
smallest real compressor boundary, not a stand-in for Level-1 or raw DEFLATE.
The current source contract pins lean-zip at
`273d0d6cd9cab77c7f3489b0b0b1f6e543315d21` and zip-common at
`4425bab1f9522307d77e8d485bc536149ba31c36`; a fresh capture must record
the exact checkouts, compiler/toolchain, artifact identity, and closure shape.
The historical `_build/stored.lcnf` is diagnostic, not proof-usable capture
evidence.

For an arbitrary admitted input ByteArray and a *successful finite* execution
of that captured impure program, the intended theorem is schematically:

```text
captured.program = P
  + production admission of P and its selected stored export
  + related initial source/wasm32 runtime and encoded input
  + required external/resident implementation and finite-resource laws
  + ExecEvaluates sourceExternals (entryState P input)
                  (ReturnedObservation sourceFinal output)
  -> target export TerminatesWith
       (RefinedReturnPost sourceFinal output selectedRootAbi [])
```

The result postcondition must retain the final heap, globals, world and event
trace, return one physical value with the caller tail preserved, clear the
structured failure channel, and relate that value to `output` at the **selected
root ABI**. A ByteArray boundary theorem must then show that decoding the
returned resident object yields exactly the source result bytes. This is
partial correctness for each successful source run, not a claim that all
inputs terminate or that every possible failure is yet matched. A small input
range such as length at most 65,535 may be a useful initial regression corpus;
it is not a proof assumption unless an explicit implementation/resource
bound requires it and the full theorem reports that bound honestly.

## Three artifacts, three claims

1. **Captured source and contracted unlinked module.** Retain a proof-usable
   `Artifact.program`, selected entry, declaration/external/call/cache
   inventory, and source-to-module identity. W6 proves the compiler theorem
   for the production supported-export lowering/adaptation contract. The
   `compileClosedClosureModuleArtifact` route used by lean-zip is not silently
   identified with W6's `ConcreteSupportedExport`/`lowerSupported`/`adapt`
   route; an explicit static correspondence is needed wherever they differ.
2. **Production resident-linked module.** `compileStored` takes the captured
   closure through `compileClosedClosureModuleArtifact` and
   `prepareArenaAndLinkArtifact`. W7 owns its helper signatures, checked
   linker, executable implementation and artifact acceptance. W6 proves the
   helper-to-concrete-host laws and the simulation/link-preservation facts
   needed to transport the unlinked theorem; root coordinates shared-contract
   changes and integration. Generation-ready checks alone are not proofs.
3. **Exact released bytes.** Relate the accepted linked module through encoding
   and any release transformations to a digest-pinned Wasm byte sequence, then
   connect execution/decoded output to the same postcondition. Node, browser,
   and native-oracle agreement are strong validation but do not replace the
   semantic or encoder/linker proof. Byte identity must be stated for the
   selected released package, not inferred from a prior diagnostic dump.

## Reusable static export assembly

`ConcreteSupportedExport.exists_ofSupportedPipeline` now reconstructs the
canonical compiler context, local layout, selected symbolic and concrete
function rows, numeric index and adapted body through the existing production
declaration selector. It retains `spec.sourceDeclaration = declaration` and
the context's canonical cache row. The effective result ABI is the lowerer's
choice, not assumed equal to the declaration's unrefined public kind.

Successful concrete resolution preserves every import key in order and its
count. Together with adaptation this derives host-table alignment and the
host environment's exact invocation-contract satisfaction. No application
supplies a table-length proof. `concreteRuntimeCallsAligned_ofPipeline` now also
derives the runtime contract table from successful adaptation and resolution:
it identifies the executable host function and semantic signature at every
runtime call slot. This is independent of lean-zip and adds no execution or
resource assumptions. `concreteExternalCallsAligned_ofPipeline` also derives
the external contract table from name uniqueness and the existing successful
lowering/adaptation/resolution equations. It selects the exact declaration's
import and original source types, then the resolver's actual `externalFn` at
that same slot. Neither runtimeAligned nor externalAligned is a constructor
premise now. This does not prove arbitrary external implementations correct.

Remaining constructor premises are static: `closureFlowSafeProgram = true`,
actual lowering/adaptation/resolution equations, selected
declaration/body/ABI classification. Canonical export lookup is derived internally.
The current `validateSupported` gate does not by itself provide the additional
closure-flow condition in `WasmSupported`; its supported-declaration and
reuse-capacity components are now derived from successful lowering. These
premises must not be disguised as execution certificates. Dynamic current-step
admission, resource safety and
entry-runtime refinement are separate subsequent obligations. All thirty-four
static infrastructure endpoints depend only on Lean's three standard axioms.

`lower_exports_eq_functionNames` exposes production lowering's exact export
table; the generated row retains its source index and declaration name.
`adapt_findExport_of_sourceExport` derives
`findExport name.toString = some (source.imports.size + index)` from the actual
source export and function lookup. It uses target validation's checked string
name uniqueness, not `Name.toString` injectivity. `row.canonicalExport` then
connects the lookup to that row's target index. The constructor returns an
export at `declaration.name.toString`, not an arbitrary caller-selected alias.
Its regression also recovers the concrete export lookup without supplying it.

`ConcreteSourceValidation.lean` now proves that exact source-check boundary:
`validateSupported_facts` extracts supported declarations and
reuse-capacity safety, while
`wasmSupported_iff_closureFlowSafe_of_lowerSupported` proves that the remaining
`WasmSupported` obligation is precisely `closureFlowSafeProgram = true`.
The constructor uses this equivalence instead of asking clients to repeat the
checks the compiler already performed. That extra closure-flow check is not
currently performed by `validateSupported`, and remains a visible premise.
Separate executable guards reuse the dictionary-underapplication fixture:
validation and lowering succeed, but closure-flow safety and `supportedProgram`
fail. These are specification-sensitivity tests, not proof witnesses; fixture
imports stay outside the reusable proof and constructor modules.
`NamesUnique` is not checked there either, but is now derived at the later
symbolic-validation boundary. `declarationNames_perm_of_lower` preserves every
source name, including duplicates, in the combined external/internal table.
`declarationNames_nodup_of_validateModule` proves that the actual production
hash-set check rejects duplicates in that combined table. Their composition,
`namesUnique_of_lower_validateModule`, reflects uniqueness back to the source.
`adapt_source_valid` supplies the check equation from successful adaptation;
`namesUnique_of_supportedPipeline` removes the constructor's client premise.
Separate regressions reject duplicated internal declarations and cross-table
external/internal collisions after successful lowering. No checker change,
caller certificate, `CheckedProgram` wrapper or new trust is involved.
The exact nominated lean-zip capture must also be checked for closure-flow
safety; no result for that capture is inferred from successful compilation.
Source admission, entry/resource contracts and capture fidelity remain
separate; the shared simulation relation and production admission set are
unchanged.

Capture review found that the production `Artifact.program` and olean capture
cache already retain full AST data, but as elaborator environment state, not
a kernel-referable program definition. The missing reusable capture facility
is structural reification of that same program into an ordinary checked Lean
definition, with exact same-capture binding to the lowering input. Lean's
`LCNF.ToExpr` is not this facility: it reconstructs source expressions, not an
LCNF AST quotation. Pretty text or a hash cannot substitute for this definition
or establish faithful source capture. Root coordinates this generic compiler
surface and its W7/package wiring; W6 does not duplicate it locally.

## W6 proof slices after static evidence

- Extend the existing concrete relation for semantic ByteArrays, including an
  `AllocationDescriptor` case and `LiveCellRel` case with exact
  bytes, capacity/length, ownership, and the selected borrowed/transferred input
  policy. A borrowed-input API additionally needs input-preservation evidence;
  do not infer it from a successful returned-value theorem alone.
  The physical `ObjectKind.byteArray` already exists, but these W6 relation
  cases do not. Reuse resident Array work where it genuinely shares laws;
  do not equate generic Array and ByteArray representations by name. Coordinate
  the descriptor/runtime surface with root and W7 as an isolated shared
  contract before dependent implementations or proofs; it is not merely a
  local theorem addition.
- Add operation/refinement laws for the *captured* external surface, notably
  ByteArray, Array, and `UInt16` operations absent from the current
  `PureExternalSupported` families. Account for mutation/copy-on-write,
  allocation cost, result ABI, release, and exact byte reads/writes. Derive
  compiler admission from production validation and source execution; do not
  put program-specific operation certificates or an arbitrary invariant in
  the public theorem.
- Close reachable lazy-cache misses whose initializer returns `.object` or
  `.tobject`. Current `ConcreteStructuredLazyMissBackendCoverageAt` explicitly
  excludes those result kinds. Preserve the actual cache publication,
  persistence and root-result provenance rather than assuming a warm cache.
  `ConcreteLazyPublication` now composes the compiler-selected initializer's
  ordinary transport with facts-aware publication for the complete miss,
  including heap-valued results. Its preferred entry consumes the existing
  `LazyCacheInternalPublicationInduction` disjointness postcondition; it does
  not infer alias safety from ABI typing. Physical cache publication already
  supports arbitrary related values. The remaining restriction is the
  all-location `ReuseCapacityCodeEntryTransports.ordinary` and its suspended
  resource-stack consumers: publishing an ordinary returned graph genuinely
  invalidates that stronger condition. A separate facts-aware stack transport
  and derivation of publication disjointness are still needed before changing
  the current admission boundary.
  The helper-level `ReuseTokenOrdinaryTransport` now supplies fixed-caller
  prefix composition and binding, including prefixes that publish heap values.
  `precomposeRetained` removes the all-location premise from this local
  composition, not from the current hereditary declaration/stack packages.
  A two-cache publication regression checks the weaker frame with a nonempty
  retained-token map. Wiring the suspended frames and deriving disjointness
  remain the next semantic work; no actual lean-zip admission is claimed yet.
- Apply the existing rooted finite-trace/terminal theorem only after its
  explicit compiler-current-step admission, address-space/resource safety,
  entry/runtime contracts and argument arity have been constructed for this
  closure. The current `ConcreteRootedTerminal` work supplies exact-root
  successful executable return under those premises; it is **not** PA3
  admission closure, resident linking, fault preservation, or exact bytes.

## Next bounded action

The authoritative `ROOT-W6-20260922-021` input is now retained
`RetainedStored.olean`, SHA-256
`e71219ab8443177481cfee3d940810942b165a61c7179e940664aba1b835119b`.
Independent import recovers `Zip.Wasm.compressStored`, 21 declarations,
14 external names and four object-valued cached initializers. Importability
is established, but the artifact stores its program only in an environment
extension and declares no kernel-referable program constant. Root must
coordinate structural reification and the same-input lowering boundary;
neither printed LCNF nor a fresh substitute capture closes this obligation.
The diagnostic closure-flow Boolean also needs kernel proof evidence for
the actual opaque production checker. No new native axiom is authorized.

Meanwhile, the independent W6 prefix-transport laws prepare the semantic
obstacle demonstrated by those object-valued initializers. The next bounded
proof work is to connect fixed-caller facts-aware transport to suspended
frames, retaining explicit publication disjointness, then derive that
disjointness from ownership. Do not remove the current admission exclusion
before those consumers are justified. W7 owns capture/emitter/package changes,
W6 owns these proof helpers, and root owns shared contracts and integration.
Existing audited native-evaluation debt remains explicit.
