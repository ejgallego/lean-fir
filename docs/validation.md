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
retained instead of being fabricated, and initial cases deliberately avoid
extern-dependent behavior.  Structured arguments are encoded into an initial
FIR heap; returned values are decoded using the declared result schema.

Artifacts are written under `_build/validation/`.  Each case retains protocol
results, backend logs, generated impure LCNF, declaration names, instruction
forms, and the comparison summary.  The native oracle's `--manifest` JSONL is
the single discovery surface for the harness: case and tag selection no longer
depend on a second ad-hoc listing command.  The harness validates and
canonicalizes those descriptors into `_build/validation/corpus.json`, ordered
by case ID with deterministic tag and required-form lists.  Each successful
comparison embeds the corresponding descriptor, so entry name, provenance,
arguments, schemas, fuel, tags, and intended LCNF/external coverage remain
attached to later differential runs.  `requiredExternals` records names that
must occur in the compiled artifact; `requiredExecutedExternals` records the
stronger path obligation that the interpreter must actually dispatch them.
Both fields are required, even when empty, and are canonicalized as sorted
sets.  This manifest is the backend-neutral input boundary for future adapters,
including a real Wasm engine once the compiler track can provide modules;
adapters do not need to import FIR's Lean corpus definitions.

`_build/validation/coverage.json` is the deterministic aggregate coverage
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

The report records per-case required, observed, and missing form and external
sets as well as their corpus-wide unions and interpreter step counts.  Every
LCNF result must emit `executed-lcnf-forms` and a positive `interpreter-steps`
value, including cases whose executed requirement list is empty.  An empty
list means “collect telemetry without a path-specific obligation”; it does not
make the telemetry optional.  Once a case lists an executed form or external,
failing to reach it fails validation just like a missing static obligation.
This distinction prevents code merely present in an unvisited branch from
satisfying an execution-coverage claim.

## Current corpus

The compiler-generated corpus currently has 44 cases.  Beyond literals,
branches, calls, closures, recursion, and ownership instructions, it covers a
heap-allocated natural above the tagged range, recursive structured-value
round trips, Unicode strings, maximum-width `UInt64`, portable `USize`,
polymorphic box/unbox, packed USize/scalar structure updates, and nested tuple
projection/reallocation.  Stress fixtures additionally execute compiler-lowered
ownership/reuse during recursive reassociation, retain 17 closure captures,
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
heap-natural input/result.  Runner-supplied `ByteArray` identity, size, and
indexing fixtures validate the packed scalar-array heap ABI, including scalar
reads of zero, high-bit, and maximum byte values.

The protocol already has recursive data, signed integers, scalar-bit, `USize`,
output, and controlled effect fields.  The LCNF codec intentionally supports
only the shapes needed by the checked corpus.  Immediate signed integers use
Lean's signed-32-bit payload ABI; larger values use the interpreter's semantic
signed-integer heap object.  Externally supplied packed constructors, boxed-object arrays, and
observable external effects remain vertical slices with matching native
cases.  Packed byte-array identity, size, and in-bounds indexing are supported;
out-of-bounds behavior and mutation remain controlled external-primitive
follow-ups.

The validation backend's external implementation is reject-by-default.
`Nat.add`, `Int.ofNat`, `Int.neg`, `Int.decLt`, `ByteArray.size`, and
`ByteArray.get!` are currently allowlisted.  Natural addition decodes tagged or heap operands,
computes with Lean `Nat`, and re-encodes through the same tagged/heap boundary
as the interpreter.  The integer primitives decode and re-encode both the
signed immediate and heap representations; `Int.decLt` returns the scalar
`UInt8` discriminant consumed by lowered pattern matching.  Byte-array size
reads the packed heap object and returns a tagged natural; byte-array indexing
returns the selected packed byte as a scalar `UInt8`.  `extern` must be
present both statically and in executed-form coverage for every runtime
primitive fixture, while the matching name must independently satisfy both
external-name obligations.

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
