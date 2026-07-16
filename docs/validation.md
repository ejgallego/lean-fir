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
typed arguments and result schema, native invocation, fuel, tags, and the LCNF
forms it intends to exercise.  Required-form checks prevent optimization or
compiler drift from silently turning a targeted case into a weaker test.

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
arguments, schemas, fuel, tags, and intended LCNF coverage remain attached to
later differential runs.  This manifest is the backend-neutral input boundary
for future adapters, including a real Wasm engine once the compiler track can
provide modules; adapters do not need to import FIR's Lean corpus definitions.

## Current corpus

The compiler-generated corpus currently has 18 cases.  Beyond literals,
branches, calls, closures, recursion, and ownership instructions, it covers a
heap-allocated natural above the tagged range, recursive structured-value
round trips, Unicode strings, maximum-width `UInt64`, portable `USize`,
polymorphic box/unbox, packed USize/scalar structure updates, and nested tuple
projection/reallocation.  Several fixtures carry exact provenance into Lean's
`tests/compile` suite at `v4.32.0-rc1`.  The corpus contains no hand-written
LCNF: the native and FIR paths consume the same Lean source declarations.

The protocol already has recursive data, scalar-bit, `USize`, output, and
controlled effect fields.  The LCNF codec intentionally supports only the
shapes needed by the checked corpus.  Signed integers, byte arrays, externally
supplied packed constructors, and external effects must be added as vertical
slices with matching native cases.

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
