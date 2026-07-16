# Interpreter validation

FIR validates its executable semantics against Lean programs compiled by the
normal native backend.  The native executable is the source-language oracle;
the first candidate is FIR's interpreter for the final impure LCNF emitted for
the same declarations.

```text
Lean source case
  +-- native Lean/C executable -- oracle observation
  +-- LCNF.main -- final impure program -- FIR observation
```

Run the quick corpus with:

```sh
make validate
```

Individual cases and tagged groups can be selected directly:

```sh
python3 scripts/validate_interpreters.py --case captured-partial
python3 scripts/validate_interpreters.py --tag quick
```

The backend pair is explicit and defaults to the current validation path:

```sh
python3 scripts/validate_interpreters.py --reference native --candidate lcnf
```

Repeated `--pair REFERENCE:CANDIDATE` options request a directed comparison
matrix and supersede the single `--reference`/`--candidate` pair:

```sh
python3 scripts/validate_interpreters.py \
  --adapter-config configs/v8-validation.json \
  --adapter-config configs/talos-validation.json \
  --pair native:lcnf \
  --pair native:v8 \
  --pair v8:talos
```

The matrix executes and audits each distinct backend exactly once, persists its
result records once, and then compares every requested edge from the cached
protocol results.  Backend execution/domain/audit findings appear in each pair
that uses that backend, while the process exit status counts each backend
finding only once.  Duplicate pairs, self-comparisons, unsafe names, and two
different adapter objects claiming the same name are rejected before execution.
`_build/validation/matrix.json` is the deterministic discovery artifact for the
run: it lists selected cases, participating backends, directed pair-report
paths, de-duplicated global findings, and aggregate backend/pair/comparison
counts.  Automation can start there and open only the detailed pair reports it
needs.  Its `inputs` array content-addresses the exact canonical `corpus.json`,
the validation plan when present, and every external adapter config with
SHA-256.  Paths inside the checkout use stable root-relative names; inputs from
outside it use only their basename, while the digest remains authoritative.
The corpus hash is computed from the same canonical bytes written to disk.
Compiler-produced files are kept separately in the matrix's `products` array,
so configuration inputs and executable semantic products cannot be confused.
The matrix also derives two full SHA-256 identities from compact canonical JSON.
`identity.selection` binds the corpus digest and ordered selected case IDs.
`identity.run` binds that selection, participating backends, directed pair
order, every input digest, and every sorted backend product.  Observations and
findings are deliberately excluded, so repeated executions of the same
evidence contract share an identity even when they expose nondeterminism or a
regression.

CI can check the requested graph into a strict, versioned plan instead of
assembling flags.  `make validate` uses
`validation-plans/native-lcnf.json`; a future Wasm plan can add adapter configs
without changing the harness:

```json
{
  "version": 1,
  "adapterConfigs": ["../validation-adapters/v8.json", "../validation-adapters/talos.json"],
  "pairs": [
    {"reference": "native", "candidate": "lcnf"},
    {"reference": "native", "candidate": "v8"},
    {"reference": "v8", "candidate": "talos"}
  ]
}
```

Adapter-config paths are resolved relative to the plan file, not the invoking
shell.  Unknown fields, protocol-version drift, duplicate paths or pairs,
self-comparisons, malformed backend names, and an empty graph are rejected.
`--plan` is exclusive with the pair/adapter flags; `--case`, `--tag`,
`--out-dir`, and `--no-build` remain valid runtime controls.

The driver discovers the corpus from the native executable, then composes two
named backend adapters.  Each adapter owns its build and execution strategy and
an optional backend-specific audit; the shared driver owns protocol result
domains, result artifacts, semantic comparison, and the comparison artifact.
Native therefore remains the corpus and source-semantics provider without
forcing a future V8 or Talos adapter to imitate native's one-process-per-case
execution strategy.

The implementation preserves that boundary at the module level:

- `scripts/validation_harness.py` owns backend-neutral protocol results,
  observations, findings, artifacts, adapter interfaces, and declarative
  external commands;
- `scripts/validation_lcnf.py` imports the generic layer and owns LCNF execution,
  diagnostics, and form/external coverage policy;
- `scripts/validate_interpreters.py` is the thin FIR CLI, native corpus/execution
  adapter, and built-in adapter registry.

The generic module never imports the LCNF module.  A V8 or Talos integration can
therefore reuse it without loading LCNF coverage assumptions.  It also has no
checkout-global root: every command receives the owning build/run context's
explicit root, allowing the same machinery to validate another controlled Lean
project without silently executing in FIR's directory.

Manifest validation follows the same direction.  The generic parser owns the
neutral execution fields and effect-projection shape, canonicalizes them, and
preserves unknown extension keys.  Before selection and artifact writing, each
participating adapter gets one `prepare_manifest` pass.  The LCNF adapter alone
requires and canonicalizes `requiredLcnfForms`, `requiredExecutedLcnfForms`,
`requiredExternals`, and `requiredExecutedExternals`, including the invariant
that every projected effect external is both present and executed.  Thus a
`native`–`v8` or `v8`–`talos` run does not acquire LCNF obligations merely
because the current native corpus happens to emit them.

An adapter can also be registered without changing the harness.  The config is
JSON, and commands are argv arrays executed directly rather than shell text:

```json
{
  "name": "v8",
  "buildCommand": ["node", "scripts/build-lean-wasm.mjs"],
  "runCommand": ["node", "scripts/run-lean-wasm-v8.mjs"],
  "resultDomain": "selected",
  "timeoutSeconds": 120,
  "products": [
    {"kind": "wasm-module", "path": "modules/validation.wasm"}
  ]
}
```

```sh
python3 scripts/validate_interpreters.py \
  --adapter-config configs/v8-validation.json \
  --reference native --candidate v8
```

`buildCommand` is optional.  `resultDomain` is `selected` when the command emits
only requested cases and `corpus` when it emits the whole manifest.  Both
commands receive `FIR_VALIDATION_BACKEND`, `FIR_VALIDATION_OUT_DIR`, and
`FIR_VALIDATION_PROTOCOL_VERSION`.  The run command additionally receives
`FIR_VALIDATION_CORPUS`, the absolute path of the canonical corpus JSON, and
`FIR_VALIDATION_CASES`, a JSON array preserving the requested order.  It writes
protocol JSONL to stdout; stdout, stderr, result records, domain failures, and
comparisons then follow the same path as built-in adapters.  This contract does
not assume how a Wasm module is produced or initialized, so it can be exercised
only after the compiler track deliberately supplies those pieces.

The optional `products` array declares regular build outputs whose bytes affect
the backend's semantics.  Each declaration has a restricted lowercase `kind`
and a normalized relative POSIX `path` beneath that backend's
`FIR_VALIDATION_OUT_DIR`; absolute paths, traversal, duplicate paths,
directories, and symlinks are rejected.  Products require `buildCommand`.
Before an ordinary build the harness removes any declared stale files, then
hashes the newly produced raw bytes with SHA-256 immediately after the build.
`--no-build` instead captures the existing declared files for deliberate reuse.
Before starting the engine and again after it exits, the harness verifies that
every product still has the captured digest.  Missing or mutated products are
structural validation errors rather than semantic mismatches.

The run command receives `FIR_VALIDATION_PRODUCTS`, a compact JSON array with
each verified product's backend, kind, stable output-relative name, SHA-256,
and absolute local path.  `matrix.json` records the same entries without the
machine-local path under `products`, sorted deterministically and counted as
`productCount`.  A future V8 adapter can therefore execute the exact declared
`.wasm` bytes and retain their identity in the report.  This establishes only
the generic producer/engine handoff: it neither invokes the developing Wasm
compiler nor assumes how V8 and Talos will later share one module.

Handoff is not, by itself, consumption evidence.  When products are declared,
each protocol result from the external engine must include exactly one
`validation-products` diagnostic.  Its string value is a JSON array of the
products that case actually loaded, with `kind`, stable `name`, and the SHA-256
recomputed from the loaded bytes.  Every returned result must report a nonempty
subset of the declared products.  This permits a selected case to load only its
own module without falsely claiming the other retained corpus products.
Missing, empty, malformed, duplicate, or undeclared receipts become structured
`audit` findings.  Thus the future V8 evidence will distinguish “the harness
produced this module” from “the engine reports consuming this exact module.”

## Case and observation contract

`Fir.Validation.Corpus` defines each case once.  A case names its source entry,
additional source helpers that must be compiled into the same impure program,
typed arguments and result schema, native invocation, fuel, tags, the LCNF
forms it intends to exercise, and the external names that must be present or
called.  Required-form and required-external checks prevent optimization,
dependency-closure, or compiler drift from silently turning a targeted case
into a weaker test.

Backends exchange versioned JSONL records from `Fir.Validation.Protocol`.
The semantic observation contains termination, stdout, stderr, and controlled
effect events.  Backend failures such as unsupported input, timeout, crash,
malformed output, and fuel exhaustion remain distinct from source behavior.
Result schemas are explicit because final impure LCNF represents `Nat`, `Bool`,
`Unit`, and nullary constructors with otherwise ambiguous tagged values.

The LCNF candidate asks Lean's own dependency collector for the declarations
reachable from the case's compilation roots.  Imported extern signatures are
retained instead of being fabricated, then dispatched through an explicit
reject-by-default validation allowlist.  Structured arguments are encoded into
an initial FIR heap; returned values are decoded using the declared result
schema.

Artifacts are written under `_build/validation/`.  Each case retains protocol
results, backend logs, generated impure LCNF, declaration names, instruction
forms, and the comparison summary.  Process logging, per-case result writing,
result-domain checks, and semantic comparison use actual backend names rather
than assuming LCNF.  Pair-scoped files under
`_build/validation/comparisons/`—for example `native--lcnf.json`—identify their
reference and candidate explicitly.  This is the backend-neutral artifact
boundary used by later V8 and Talos adapters, and it lets native–LCNF,
native–V8, and V8–Talos evidence coexist in one output tree.  Backend names are
validated before being used as path components.  A comparison file is written
for successful and failed comparisons, with selected/compared/equal/finding
counts and typed findings for
`execution`, `result-domain`, `audit`, and `comparison` phases.  Each finding
retains its backend and case ID when applicable, so automation does not need to
recover structure from stderr text.  The native oracle's `--manifest` JSONL is
the single discovery surface for the harness: case and tag selection no longer
depend on a second ad-hoc listing command.  The harness validates and
canonicalizes those descriptors into `_build/validation/corpus.json`, ordered
by case ID with deterministic tag and required-form lists.  Each attempted
comparison embeds the corresponding descriptor, so entry name, provenance,
arguments, schemas, fuel, tags, and intended LCNF/external coverage remain
attached to later differential runs, including semantic mismatches.
`requiredExternals` records names that
must occur in the compiled artifact; `requiredExecutedExternals` records the
stronger path obligation that the interpreter must actually dispatch them.
Both fields are required, even when empty, and are canonicalized as sorted
sets.  Each case also carries an `effectProjections` array describing which
external events become semantic effects, with external name, stable operation
name, argument schemas, and optional result schema.  The field is required and
canonicalized even when empty.  A projected external must also be required both
statically and dynamically.  Future backends can therefore consume the same
effect ABI without importing FIR's Lean definitions.  This manifest is the
backend-neutral input boundary for future adapters, including a real Wasm
engine once the compiler track can provide modules.

`_build/validation/lcnf/coverage.json` is the deterministic aggregate coverage
report for the selected cases.  It keeps two kinds of evidence separate:

- **static coverage** is the set of forms present in each compiler-produced
  LCNF artifact (`lcnf-forms`), checked against `requiredLcnfForms`;
- **executed coverage** is the set of forms the interpreter actually reached
  (`executed-lcnf-forms`), checked against `requiredExecutedLcnfForms`.

The same static/executed split applies to external identity, independently of
the generic `extern` instruction form:

- `externals` is the set of imported external names retained in the compiled
  artifact, checked against `requiredExternals`;
- `executed-externals` is the set of external names actually dispatched,
  checked against `requiredExecutedExternals`.

The LCNF backend also emits `missing-externals` and
`missing-executed-externals`.  The harness computes both missing sets itself,
requires all four diagnostics for every result, and rejects disagreement with
the backend.  Empty requirements therefore still collect explicit telemetry;
they do not make diagnostics optional.  This catches a fixture that still
contains some `extern` instruction but no longer retains or reaches the runtime
primitive it was meant to validate.

`external-events` reports the number of successful external calls captured with
event-time state.  Completion fails if that count diverges from the canonical
interpreter trace, preventing a missing snapshot from silently dropping a
projected semantic effect.

The report records per-case required, observed, and missing form and external
sets as well as their corpus-wide unions and interpreter step counts.  Every
LCNF result must emit `executed-lcnf-forms` and a positive `interpreter-steps`
value, including cases whose executed requirement list is empty.  An empty
list means “collect telemetry without a path-specific obligation”; it does not
make the telemetry optional.  Once a case lists an executed form or external,
failing to reach it fails validation just like a missing static obligation.
This distinction prevents code merely present in an unvisited branch from
satisfying an execution-coverage claim.  The checked corpus currently activates
at least one executed-form obligation for every case, and the Lean case type
has no default for that field: a new fixture must explicitly state its intended
path instead of silently inheriting telemetry-only coverage.  A second
compile-time guard requires the union to retain all 23 source-reachable forms
currently exercised in final impure LCNF, so removing a fixture cannot silently
lower corpus-wide instruction coverage.  Coverage failures and semantic
mismatches are independent signals: the harness still compares protocol
observations when an LCNF coverage obligation fails, and reports both findings
from the same run.

## Current corpus

The compiler-generated corpus currently has 52 cases.  Beyond literals,
branches, calls, closures, recursion, and ownership instructions, it covers a
heap-allocated natural above the tagged range, recursive structured-value
round trips, Unicode strings, maximum-width `UInt64`, portable `USize`,
polymorphic box/unbox, packed USize/scalar structure updates and `uproj`, and
nested tuple projection/reallocation.  Stress fixtures additionally execute
compiler-lowered ownership/reuse during recursive reassociation, change the
tag of a uniquely reused constructor through `setTag`, delete a unique object
before allocating a larger replacement, retain 17 closure captures,
allocate/project a 70-object-field constructor, and match a nullary enum that
Lean lowers to a scalar discriminant.  Several fixtures carry exact provenance
into Lean's `tests/compile` suite at `v4.32.0-rc1`.  The corpus contains no
hand-written LCNF: the native and FIR paths consume the same Lean source
declarations.  Signed-`Int` fixtures cover both signs on either side of the
immediate 32-bit ABI boundary.  The boundary matrix independently validates
runner-supplied identity, compiler-built literals through `Int.ofNat` and
`Int.neg`, and constructor classification through `Int.decLt`, so tagged/heap
codec behavior, external results, and scalar-driven control flow cannot mask
one another.  Controlled `Nat.add` cases execute a real imported runtime
primitive with tagged inputs, a tagged-to-heap result transition, and a
heap-natural input/result.  Runner-supplied `ByteArray` identity, size,
indexing, and mutation fixtures validate the packed scalar-array heap ABI,
including scalar reads of zero, high-bit, and maximum byte values.  Mutation
separately covers a unique in-place update and a shared copy-on-write update
that preserves the original alias.  The first controlled-effect case calls a
validation-owned `implemented_by` primitive: native Lean records the event it
actually executes, while the LCNF backend projects the matching external trace.
Both observations contain the ordered `validation.record` event with its
natural argument and result; no expected effect is stored as the oracle.  A
second case makes two data-dependent calls, requiring both backends to report
the exact sequence `7 → 8`, then `8 → 9`, as well as the final return value 9.
This distinguishes ordered semantic effects from the set-like instruction and
external coverage telemetry.  A heap-valued effect then performs two dependent
in-place ByteArray updates.  Native Lean and LCNF must preserve the original,
intermediate, and final byte arrays in the correct argument/result positions,
even though all runtime references point at the same uniquely owned location.

The protocol already has recursive data, signed integers, scalar-bit, `USize`,
output, and controlled effect fields.  The LCNF codec intentionally supports
only the shapes needed by the checked corpus.  Immediate signed integers use
Lean's signed-32-bit payload ABI; larger values use the interpreter's semantic
signed-integer heap object.  Externally supplied packed constructors,
boxed-object arrays, and more effect shapes remain vertical slices with matching
native cases.  Tagged-natural and mutable ByteArray effect arguments/results,
packed byte-array identity, size, in-bounds indexing, and unique/shared mutation
are supported; out-of-bounds behavior remains a controlled external-primitive
follow-up.  The LCNF adapter retains immutable runtime snapshots immediately
before and after each successful external call, so heap effects are decoded at
event time rather than through potentially mutated or dead final-heap
references.  A future V8 adapter will materialize the same schema-directed
datums at the Wasm import boundary.

The validation backend's external implementation is reject-by-default.
`Nat.add`, `Int.ofNat`, `Int.neg`, `Int.decLt`, `ByteArray.size`,
`ByteArray.get!`, `ByteArray.set!`, and the validation-owned Nat and ByteArray
effect recorders are currently allowlisted.  Natural addition decodes tagged or
heap operands, computes with Lean `Nat`, and re-encodes through the same
tagged/heap boundary as the interpreter.  The integer primitives decode and re-encode both the signed
immediate and heap representations; `Int.decLt` returns the scalar `UInt8`
discriminant consumed by lowered pattern matching.  Byte-array size reads the
packed heap object and returns a tagged natural; byte-array indexing returns
the selected packed byte as a scalar `UInt8`.  Byte-array mutation consumes its
array argument: unique cells update in place, while shared cells decrement the
consumed reference and return a newly allocated copy.  Validation-only guards
check both paths' locations, allocation counts, contents, and reference counts
in addition to the native observation comparison.  The Nat effect recorder
increments its argument; the ByteArray recorder updates its first byte.  Both
advance the interpreter world, and their event-time snapshots are decoded only
when selected by that case's projection metadata.  The native runner resets the
recorder before execution and drains it through a result-dependent hook, making
the effect ordering explicit even though the source-facing functions are pure.
`extern` must be present both statically and in executed-form coverage for every
runtime primitive fixture, while the matching name must independently satisfy
both external-name obligations.

## Deferred WebAssembly integration

Validation does not currently implement, modify, or constrain the Wasm
compiler.  When that track has an executable supported fragment, it hands the
validation track a stable compilation command or API, exported-entry mapping,
argument/result ABI, initialization semantics, runtime/import strategy, and a
deterministic Wasm artifact.

The first Wasm validation adapter will assemble compiler-produced WAT with a
pinned `wasm-tools`, execute the resulting module in Node/V8, and emit the same
backend record as the LCNF candidate.  Native Lean remains the source oracle.
Talos can subsequently consume the exact same module and inputs, with V8 as the
reference Wasm engine:

```text
native Lean <-> V8          compiler/runtime validation
native Lean <-> FIR LCNF    LCNF semantics validation
V8          <-> Talos       Wasm interpreter validation
```

Successful lowering or assembly is preparation, not semantic validation.
Adding either backend is a registry extension implementing the existing
build/execute/audit adapter contract; it does not change comparison semantics
or the native-owned corpus.  Wasm-specific compilation and engine telemetry
belong in that adapter's optional audit, just as instruction/external coverage
belongs to the LCNF adapter today.
