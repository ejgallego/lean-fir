# Checked retained initializer: source execution and publication

This optional W6 proof cone consumes `RetainedRC2.program`, generated from the
immutable lean-zip source snapshot by the W7 checked-capture recipe. It does
not contain a copied initializer AST. `RetainedDeclarations` extracts the two
external declarations from that same definition with kernel-checked lookup
and body equations. Production ordinary/closed/resident lowering in the
unchanged `RetainedRC2` harness consumes the definition's readback too.

`RetainedInitializer.reaches_published` proves that the actual initializer
`Zip.Spec.DeflateStoredCorrect.deflateStoredPure._closed_0` reaches its exact
published source state in 12 steps from a cold cache. The runtime contains a
fresh singleton Array holding tagged zero, its cache publication, unchanged
world, and the original trace followed by exactly the `Array.mkEmpty` and
`Array.push` events. A thirteenth step returns.

`evaluates_and_preservesCaller` connects that reached state to historical
caller facts. It asks for the saved fact interpretation, witness transport
and current live-heap relation; it does not ask for a region, graph separation,
prefix preservation, body execution or target path. The caller environment
stays fixed. This remains pointwise saved-caller preservation, not recursive
suspended-stack reconstruction.

`reaches_published_withFrames` generalizes the execution to an arbitrary
suspended frame stack. `resumesCaller` derives the exact 13-step prefix through
destination binding, restoring the caller's environment, joins and remaining
frames, and discharges `ReuseTokenOrdinaryBindTransport` for that result.

`return_pop_preservesCaller` applies this to the existing concrete return/pop
consumer: the 13-step source prefix and the two target return/bind steps end
in related states with the full caller cache/ABI frame restored. Its premises
still include the target return focus, callee frame, witness/capacity transports,
historical caller scope and suspended tail. It does not establish the target
callee prefix or reconstruct the stronger hereditary resource stack.
`resumedCaller` is a transparent proof-only state description, not an extra
compiled executable or a replacement source program.

`evaluates_and_retainsCallers` additionally derives the new entry-indexed
`RetainedCallerTransport` law for every representable historical caller map,
not a caller-selected map. That law is the source component consumed by
`RetainedCacheEntryFrame.restoreCaller`, which composes the entry package
through return without blanket ordinaryness. The negative regression
`example_not_blanketOrdinary` shows why the distinction matters: the actual
fresh published Array violates the old all-location condition. The central
active/suspended resource stack now uses the replacement. The remaining
heap-result publication rule must derive its cumulative transport before
lifting object/tobject lazy-miss exclusions; this body theorem alone is not
that central admission result.

`reaches_publicationInput_withFrames` exposes the actual 11-step prefix with
the cache marker still pending. `executes_and_publishesCache` takes that source
publication step and derives the concrete cache host operation, post-runtime
refinement, and cumulative entry transport including the two global-update
store expressions. It derives the closed fresh graph from the checked body's
singleton-Array result. The concrete pre-cache relation, entry transport,
represented result and cache-slot facts remain explicit; no target prefix,
seven-instruction publication path, global-index alignment or full post-cache
stack relation is claimed by this endpoint.

`executes_and_restoresCallerScope` strengthens that result by recovering the
suspended caller's full entry-relative resource scope: represented facts,
ordinary saved tokens, cache-table agreement, external-handler contracts,
allocation headroom and closure ABI. It uses the same restoration theorem as
the central validated non-heap dispatcher. Its pre-publication callee scope and
represented result remain premises; it does not prove the target callee prefix,
destination bind, full stack assembly or central heap-result admission.

`executes_publicationSuffix` additionally proves the seven generated Wasm
steps from initializer return through cache host publication, value/flag writes,
conditional exit and value reload. The compiler-supported caller is for the
same `RetainedRC2.program`; import contract alignment and physical global-lane
existence are derived. The source publication step and restored caller scope
are retained. The target initializer prefix and following destination bind are
still outside this theorem, as is complete source/target stack assembly.

`publication_bind_resumesCode` closes that destination-bind suffix. It runs
the checked source initializer for thirteen steps under a waiting caller and
matches publication/binding with eight target steps, ending in the ordinary
`ConcreteStructuredCodeCoreRel`. The returned value is bound, the saved join
environment restored, and the original caller scope/suspended resource tail
retained; the overwritten destination's reuse fact is erased. The proof
constructs the intermediate bind relation rather than requiring it. The
pre-publication callee scope and represented result, compiler continuation/local
alignment, and suspended resource tail remain premises. Target callee execution,
production Array external refinement, residual validation and general heap-miss
admission are still separate obligations.

The two source external contracts are uniform primitive laws, not a
per-program invariant. `FreshArrayExternalContract` specifies empty allocation
and the fresh/non-full tagged-push branch. `freshArrayExternals_contract`
provides an executable consistency witness; other requests are rejected by
that deliberately limited model. This is **not** the production external
implementation. Its connection to concrete external admission and resident
helper execution remains to be proved. No whole lean-zip or Wasm artifact
correctness follows from this source endpoint.

## Reproduce

From the W6 worktree, with repositories containing the exact source objects:

```sh
bash integration/talos/retained-initializer/check.sh \
  /path/to/lean-zip /path/to/zip-common
```

The script archives lean-zip `273d0d6c` and zip-common `4425bab1` into the
worktree-local `.deps/retained-rc2`, copies maintained source templates, and
uses the worktree's official toolchain and Talos setup. It fetches no substitute
source revision and shares no mutable build state with W7. Lake may obtain its
pinned build dependencies if absent. Source/setup identity and the limitations
of capture are documented in `Fir/Compiler/LCNF/README.md`. Adding the Talos
proof dependency changes the private Lake setup identity, not the captured
source or initializer body.

The gate builds the consumer, imports the checked definition in a fresh
process, and forces direct batch elaboration with an exact per-endpoint axiom
audit. The source endpoint inherits the seven **existing** native-evaluation
axioms of `boxUsesTaggedRepresentation_boxedScalar`, due to upstream opaque
expression comparison. It introduces no new native evaluation or axiom.
The captured program/body equations remain free of generated axioms. Generic
external-model and finite-prefix helper proofs use standard axioms and are
also in the ordinary Talos trust inventory.
The concrete publication endpoint additionally inherits the existing
`LinearMemory.assembleByte32` native bitvector axiom through recursive cache
persistence. Its separate exact audit records that dependency; the source-only
endpoints keep their narrower inventory. The full-scope consumer inherits the
same exact dependencies, as does the executable-suffix consumer. There are
fourteen consumer endpoints, including the publication/bind code-core result.
