# First W6 lean-zip example: captured stored-block compressor

## Active checkpoint — 2026-09-26

The checked input has arrived: W7 functional `249f476d5`, delivered by
`W7-ROOT-20260926-003` at `82f25e39c`, defines `RetainedRC2.program` and
kernel-checked initializer lookup/body equations. W6 reproduces it from the
exact source Git objects in its own build directory. The source-body consumer
is no longer blocked on capture. Root accepted the W7 dependency at
`5c922bb65` on main, recorded in `ROOT-W6-20260926-006`; this remains distinct
from acceptance of the W6 source-body proof.

The first actual-body connection is now implemented in
[`retained-initializer/RetainedInitializer.lean`](retained-initializer/RetainedInitializer.lean):

- `RetainedInitializer.reaches_published` derives the exact 12-step source
  prefix from a cold cache, using the checked program rather than a copied
  AST. The result is a published singleton Array containing tagged zero,
  unchanged world, and exactly two appended external events. The next step
  returns that Array.
- `RetainedInitializer.evaluates_and_preservesCaller` derives ordinary-token
  preservation for arbitrary historical caller facts from their saved
  interpretation, witness transport and current live-heap relation. It takes
  no body-execution, graph-separation or publication-transport premise.
- `freshArrayExternals_contract` provides an executable source-model witness
  for the two uniform primitive contracts used by the body. This is not a
  claim about the production external implementation or resident helpers.

The caller-consumer connection is now implemented in the same proof cone:
`reaches_published_withFrames` retains any suspended stack, `resumesCaller`
derives the 13-step source prefix through destination binding, and
`return_pop_preservesCaller` connects that prefix to the existing two-step
target return/pop transition. The exact resumed source state has the caller's
environment, joins and remaining frames; it is related to the resumed target
with the full caller cache/ABI frame restored. The ordinary-binding premise is
derived, not supplied.

The independent external premise is `FreshArrayExternalContract`: exact empty
allocation and unique, non-full, fresh-Array tagged push. Its production
refinement and the target callee prefix remain next obligations. The new
connection retains the target return focus,
callee frame, witness/capacity transports, original caller scope and historical
tail. In particular, it executes only the target return/bind suffix, not the
whole generated initializer, and does not remove central object/tobject
lazy-miss exclusions.

The central resource-stack migration is now implemented: active scopes and
suspended callers retain entry-indexed `RetainedCallerTransport`, and the
return/pop producer composes the callee transport back to the caller's original
entry. Ordinary local operation laws are lifted by composition, not by resetting
the saved scope. Legacy whole-declaration endpoints keep their stronger
ordinary-persistence contract. The generic heap-publication rule now derives
that cumulative transport from construction facts, and
`executes_and_publishesCache` applies it at the actual body's eleventh-step
publication boundary. Graph closure and root freshness are derived; pre-cache
concrete refinement, transport and slot facts remain explicit. The two global
updates are specified stores, not a generated instruction path or full
cache/stack invariant. Broadening central lazy-miss admission still requires
retaining and consuming this construction provenance there.

The [reproduction gate and trust boundary](retained-initializer/README.md)
include exact compiled-dependency audits. The source theorem inherits seven
existing boxing-policy native-evaluation axioms; no new axiom or native
evaluation was added. This distinguishes the achieved source result from
the broader publication-to-return/pop milestone below.

The immediate target is one real initializer's publication-to-return/pop proof,
not yet the complete compressor theorem. The live obligation table and scope
limits are in [the W6 frontier](PLAN.md#current-verification-frontier--2026-09-26).
`ConcreteSupportedExport.terminatesWith_of_rootedExecEvaluates` already gives
conditional executable successful-return preservation at the exact export ABI;
compiler admission, the ByteArray boundary, resident linking and bytes remain
separate work.

Root selected a new retained-input nomination under official Lean 4.34.0-rc2
in `ROOT-W6-20260925-002`, with W7 implementation assigned by
`ROOT-W7-20260925-001`. Preserve the exact nominated source/dependency bytes,
but report the new compiler and artifact identity; the old 4.33 retained olean
is historical evidence, not an RC2 proof input. The required delivery is a
kernel-checked `ImpureProgram`, exact lookup/body equations for
`Zip.Spec.DeflateStoredCorrect.deflateStoredPure._closed_0`, and production
lowering using that same definition. That input is now delivered as recorded
above. No diagnostic JSON, hand-copied LCNF or substitute capture suffices.

The first W6 consumer must derive publication/binding transport from the real
body's operations and apply `advance_popRetainedCache`, eliminating supplied
graph-separation/ordinary-binding obligations for this body. It must retain
the independent execution, representation, witness/capacity and historical-frame
premises. The generic hereditary scope consumer is now migrated; deriving its
complete transport package from actual target initializer execution remains
distinct from restoring the caller cache/ABI frame alone.

## Next proof plan: actual initializer to caller restoration

### Deliverable and theorem names

The original two-part milestone is now realized in
`retained-initializer/RetainedInitializer.lean`:

1. `RetainedInitializer.resumesCaller`: derive
   `ReuseTokenOrdinaryBindTransport` for execution of the exact selected body,
   followed by `setGlobal` and destination binding.
2. `RetainedInitializer.return_pop_preservesCaller`: supply that derived
   transport to `ConcreteStructuredBindFrameFocus.advance_popRetainedCache`.

The second theorem exposes the checked body's source prefix, existing target
return/pop transition and restored caller-frame conclusions. It does not claim
to rebuild the stronger hereditary resource scope or execute the target callee.

The premise removed is the caller-supplied publication/binding transport for
this actual initializer. The body proof must also derive any graph separation,
fresh-region closure, root bound and caller-prefix preservation that it uses.
It may not reintroduce those obligations through a body-specific certificate.

### 0. Consume the checked program, not its diagnostic inventory

W7's `ROOT-W7-20260925-001` supplies a new exact-source RC2 nomination, a
kernel-referable program, exact declaration/body equations and production
lowering of that same definition. W7 has completed the input; root owns its
landing coordination independently of this W6 proof successor.

Inspect the delivered body before choosing primitive lemmas. Confirm its
parameters, return kind, calls, control flow and owned-field values from the
checked equations. The historical `Array.mkEmpty`/`Array.push` inventory is a
lead only. If the exact nominated declaration is absent or changed, report
the difference rather than choose a convenient replacement. Capture fidelity
and changed toolchain identity remain disclosed boundaries.

### 1. Prove the body's source-side frame property

Work from the actual body execution and exact primitive semantics. For the
suspended caller's fixed facts `F` and environment `E`, derive:

```text
entry representation + execution of the checked body under specified externals
  -> preservation of Q(F,E) through the body
  -> separation of retained caller tokens from the returned owned graph
  -> preservation of Q(F minus destination, E[destination := result])
     after publication and binding
```

Here `Q` is `ReuseTokenOrdinaryRel`: each tracked token cell, if found, is
nonpersistent. This theorem is not a claim of token liveness, uniqueness,
payload preservation or complete memory safety.

The external environment must implement the exact primitive semantics used
by the body. Successful execution under arbitrary externals is insufficient.
Keep those semantic implementation contracts explicit; do not replace them
with assumptions that already assert the desired frame property.

Reuse `retainedToken_beforeNext`, `HeapRegionClosed.alloc`/`reachable` and
`freshRegion_setGlobal` if the body genuinely builds a closed fresh graph.
For Array operations, inspect both ownership and capacity conditions:
in-place push needs edge preservation through mutation, while copied push
needs allocation and ownership-transfer facts. Discharge unreachable branches
from the actual body/state facts, not a fixture-specific premise.

Add only primitive-local lemmas needed by this proof. Existing concrete
`LiveHeapRel.pushResidentArrayElementInPlaceRaw_refines` and
`LiveHeapRel.pushResidentArrayElementCopied_refines` are candidate building
blocks, not evidence that source frame preservation or compiler admission for
these calls is already proved. If the body legitimately shares older
persistent objects, prove the required token separation directly; do not
restrict admission or force it into the fresh-region sufficient condition.

### 2. Apply the result at the real return/pop consumer

Match the actual final runtime and result to the existing bind focus. Use
the derived publication/binding transport as the `ordinaryTransport` argument
of `advance_popRetainedCache`. Keep the original saved caller boundary and
historical tail; do not select a new reflexive entry after execution.

Retain the independent physical bind focus, callee cache/ABI frame,
witness/capacity transport, caller scope and suspended-stack premises. Their
classification is explicit: representation/execution interfaces still to be
composed, not facts proved by graph separation. The result is one source step,
two target steps, restored structural stack/current code and full caller
cache/ABI frame. No whole-initializer target execution is newly established
merely by applying this consumer.

### 3. Acceptance and scope

- Quantify over arbitrary caller facts/environments satisfying the existing
  entry relation; do not assume an empty token map or a fixed runtime fixture.
- The public body endpoint takes no supplied publication separation, region
  closure, caller-prefix preservation or ordinary-binding transport.
- Retain a nonempty-token positive application and the existing negative
  older-token-alias regression. Add a primitive regression only when the
  selected body exposes an uncovered allocation/mutation/ownership case.
- Do not edit the compiler, runtime ABI, central simulation relation or
  `ConcreteStructuredLazyMissBackendCoverageAt` to make this milestone pass.
  A semantic mismatch becomes a bug card, not a weakened contract.
- Use Lean Beam during iteration. At the complete checkpoint run the focused
  module/dependency-cone build, compiled endpoint axiom audit, `make check`,
  `make talos-check` with current setup, and `git diff --check`. No new axiom,
  native-evaluation shortcut or placeholder is allowed in these proof endpoints.
- Hand off the two connected endpoints as one useful result. Meta/root owns
  timely integration, board updates and dependency settlement; helper lemmas
  do not each require a new administrative thread.

### Following milestone: entry-relative preservation

The focused `ConcreteRetainedTransports.lean` module now proves a replacement
caller-restoration rule. Its `RetainedCallerTransport` ranges over saved facts
represented at entry, rather than every source heap cell. Exact-boundary
composition and `RetainedCacheEntryFrame.restoreCaller` preserve the original
entry through nested returns, keeping every other physical/implementation
transport. `RetainedInitializer.evaluates_and_retainsCallers` supplies the law
for this body without asking the client to select saved facts; the exact result
also has a negative regression against the old all-location requirement.

The replacement is deliberately sufficient rather than weakest: it protects
all representable saved fact maps, not only the current stack's actual maps.
No central simulation definition or lazy-miss exclusion has changed yet.

Replace the excessive all-location ordinaryness requirement in the reusable
call-history invariant with preservation of actual suspended-caller obligations,
then prove its push/pop closure. Only after that composition can the heap-valued
lazy-miss restriction be removed soundly from the central simulation. Keep
compiler-derived admission, ByteArray coverage and resident/byte correspondence
as separately visible obligations. This bounded initializer theorem is not a
substitute for PA3 or a proof of all of `compressStored`.

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
  Full caller-cache-frame reconstruction is now separated from the historical
  entry invariant: `ConcreteReuseCapacityCacheFrame.restoreCaller_of_retainedTransport`
  consumes the exact caller's binding transport, plus the existing checked
  local update and witness/capacity evidence. The original structured
  `restoreDirectCaller` uses it without changing its signature or its remaining
  stronger entry-transport obligation. A conditional two-publication regression
  reaches this complete frame consumer; it is not compiled-call execution and
  does not close the historical suspended-stack or ownership obligations.
  `ConcreteStructuredBindFrameFocus.advance_popRetainedCache` now also reaches
  the actual return/pop transition: one source step, two target steps, the
  structural tail and the full caller cache/ABI frame. Recursive historical
  frame reconstruction uses only witness transport. The exact saved scope
  and tail remain fixed; the callee need not supply blanket ordinaryness.
  Its two-publication regression discharges the retained-token binding
  obligation but still assumes physical frames and the bind focus. It does
  not reconstruct the stronger hereditary resource stack or establish an
  entire compiled callee execution.
  The first ownership producer now derives fresh leaf publication disjointness
  from the existing entry relation: tracked token mappings locate source cells
  strictly below the allocation frontier, and an allocated leaf has no owned
  path back to them. `allocLeaf_setGlobal` supplies binding transport directly
  to the actual pop regression for arbitrary fresh string contents and a
  nonempty caller-token map. No freshness/disjointness premise is supplied.
  Source ByteArray objects are leaves too, but this does not add the missing
  concrete ByteArray refinement or prove the retained initializer bodies.
  A fresh constructor containing an old token is an explicit negative test.
  `HeapRegionClosed` now extends the source ownership producer to fresh graphs:
  closure is established at entry and preserved per allocation using immediate
  field bounds; transitive separation is derived. The two-allocation shared
  string/constructor test supplies those bounds from actual field construction
  and reaches a genuine owned child. This still does not certify the retained
  Stored initializer bodies or add a new general source-machine invariant.
  Region preservation now also covers actual `setCell` mutation and in-place
  Array push. Existing element bounds follow from the pre-state; only a newly
  inserted heap reference needs a region bound. The concrete raw-push
  refinement supplies its semantic mutation equation and derives both region
  preservation and ordinary-cell transport. A positive allocation/push/cache
  publication regression has a nonempty caller-token map; inserting an older
  retained token gives a negative regression. These are reusable primitive
  laws, not execution of the nominated initializer or a proof of Array
  copy-on-write/ownership transfer. The concrete extension inherits exactly
  the original refinement's one native memory-decoding dependency; the source
  laws and regressions use only the standard axioms.
  `ConcreteArrayPublication` covers the source retain/allocate/release sequence
  exposed by the copied-push refinement. Header-only retention and recursive
  release preserve the region, including dead cells; copied element bounds
  come from the pre-state Array. Its regression exercises capacity exhaustion,
  retaining a string, killing the old Array and releasing the old ownership
  edge before publishing the copy. This source composition uses only standard
  axioms. Concrete allocation/resource premises, actual body execution and
  compiler admission remain separate; no copied-helper execution is inferred
  from this source lemma alone.
  Historical callers no longer need a reconstructed current state/capacity
  relation to derive fresh-region separation. Their saved capacity-fact
  interpretation, witness transport and the active entry's live heap relation
  suffice to bound retained-token locations below the new region. The new
  unbound transport preserves an older caller's environment; immediate return
  binding reuses `eraseBind`. A two-publication regression derives the source
  prefix and region and proves that retained-token preservation holds while
  blanket ordinaryness fails. Existing same-entry producers specialize the
  general law. This is a pointwise historical-caller producer, not yet the
  hereditary stack push/pop closure or an initializer execution theorem.
  `allocateEmptyArray_pushTagged_refines_publication` now composes successful
  concrete empty-Array allocation and raw immediate push. Allocation derives
  the mapped reference, descriptor, live empty cell and push preconditions;
  the exact singleton source result supplies graph closure and ordinary-token
  prefix preservation internally. Historical-caller publication therefore
  needs no separately supplied region, freshness or caller-preservation proof.
  A capacity-5/UInt8-zero regression includes actual heap-neutral boxing and
  immediate caller binding with a nonempty token map. Allocation success and
  numeric bounds remain explicit. This is not production external dispatch,
  helper branch selection, concrete cache execution or captured-body execution.
  Its concrete theorem inherits only the existing raw-push native memory debt;
  the source-only composition uses standard axioms.
- Apply the existing rooted finite-trace/terminal theorem only after its
  explicit compiler-current-step admission, address-space/resource safety,
  entry/runtime contracts and argument arity have been constructed for this
  closure. The current `ConcreteRootedTerminal` work supplies exact-root
  successful executable return under those premises; it is **not** PA3
  admission closure, resident linking, fault preservation, or exact bytes.

## Next bounded action

The historical 4.33 `RetainedStored.olean` is provenance evidence, not an
importable proof input under RC2. `W7-ROOT-20260926-002` supplies an inspectable
RC2 candidate at `249f476d5`: `RetainedRC2.program`,
`RetainedRC2.initializer.findDecl` and `.body` are kernel-referable, and
production lowering consumes the same program's readback. W6 inspected the
recipe and matched the recorded source/olean/report hashes. Completion
`W7-ROOT-20260926-003` records green full W7 gates at that functional head and
the documentation-only successor `82f25e39c`. Root integration remains pending
at this update; no W7 build state is shared with the W6 proof workspace.
Reproduce from the accepted recipe after landing.

The nominated initializer allocates an empty Array with capacity 5, boxes
UInt8 zero, pushes it, and returns the Array. Use its checked body equation
to connect the primitive composition above to actual source execution. In
particular, specify the two external Array operations, derive the fresh
unique/spare-capacity branch conditions, and connect their concrete refinements
and cache publication. Do not replace these obligations with a hand-copied
initializer or a per-body preservation certificate. The recorded closure-flow
Boolean still needs kernel proof evidence for the actual checker.

Meanwhile, the independent W6 prefix-transport laws prepare the semantic
obstacle demonstrated by those object-valued initializers. The next bounded
proof work is to retain the caller-specific transport through the stronger
hereditary resource history, beyond the now-proved structural frame and
operational pop consumers, and extend the fresh-leaf ownership producer to
the actual initializer graphs.
Current capacity, ordinary-token and representation facts do not establish
that a published graph cannot reach a saved token. Keep that separation
obligation explicit. Do not remove the current admission exclusion
before those consumers are justified. W7 owns capture/emitter/package changes,
W6 owns these proof helpers, and root owns shared contracts and integration.
Existing audited native-evaluation debt remains explicit.
