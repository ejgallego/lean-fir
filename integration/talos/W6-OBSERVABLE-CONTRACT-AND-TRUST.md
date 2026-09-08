# W6 observable contract and compiled trust audit

Review follow-up, 2026-09-09. Baseline: W6 `7affa1d2`, which includes the
conservative W7 recycler source at `e488c816`. The external review inspected
ancestor `a5449905`. This slice changes proof tests and audit tooling only.

## Destination and current evidence

The intended compiler guarantee includes finite external-event prefixes,
returned values, and semantic faults. A terminating source execution must
produce a corresponding target result under the explicit entry, runtime, and
resource contracts. No theorem needs to establish that every source program
terminates. Linking, encoding, and the application/session adapter remain
separate composition obligations before a claim about deployed bytes.

`ConcreteFiniteTraceCorrect` currently exposes only world and external-event
trace agreement. `finiteTraceCorrect_of_terminal_prefix` now formally exhibits
its limit: a terminal source and a stopped target satisfy the package whenever
their prefix observations agree. No target terminal result is constrained.
This is a test of the public interface, not a counterexample to the actual
compiler simulation relation.

The existing `RefinedReturnPost` and `RefinedFaultPost` are stronger. New
reusable lemmas in `ConcreteObservationSensitivity.lean` establish:

- `ConcreteExportTerminatesWith.postconditions_overlap`: two successful
  specifications of one invocation hold of one common `Wasm.run` result.
- `ConcreteExportTerminatesWith.uint64_result_unique`: those specifications
  cannot describe different returned UInt64 values, even with different
  existential heap witnesses or final source runtimes.
- `ConcreteExportTerminatesWith.not_trapsWith`: the same invocation cannot
  satisfy both success and trap specifications.
- `ObservationSensitivity.prettyObservation_injective`: observing the actual
  generated facade's text and reversed `eventsRev` retains all result
  information. Equal text with different styling is distinguished.

The first three lemmas use deterministic executable Talos semantics at a common
sufficient fuel. They require no extra determinism assumption. The pretty
lemma exercises the real facade type but does not prove its Wasm decoder or
its compilation. Resource exhaustion still has no general matching-failure
theorem; current resource preconditions remain explicit. This slice does not
change the schema, source/target relation, compiler admission, or runtime ABI.

## Measured trust budget

`TrustAudit.lean` is imported by the default `FirTalos` umbrella and compares
transitive compiled dependencies using Lean's `collectAxioms`. The inventory
is exact for each theorem, including removals: a changed set requires review.
There are no name-prefix allowlists, and `sorryAx` is rejected even if someone
adds it to an expected list. Missing or non-theorem endpoints are errors.

| Endpoint family | Standard axioms | Recorded generated axioms |
|---|---:|---:|
| `ConcreteRankedTraceSimulation.execSteps` | 3 | 0 |
| `precomposeStutteringPass` | 3 | 0 |
| `finiteTraceCorrect_of_sourceInvariant` | 3 | 57 |
| `finiteTraceCorrect_of_schemaSourceInvariant` | 3 | 57 |
| `ConcreteSupportedExport.correctReturn` | 3 | 0 |
| `ConcreteSupportedExport.faultCorrectOfSimulation` | 3 | 0 |
| `ResidentReplacement.externalLetStepSimulates_of_definedCall` | 3 | 0 |
| sampled `UInt64ObjectInstallation` termination theorem | 3 | 20 |
| concrete `abiLiteralMain_export_correct` | 3 | 27 |
| all ten new sensitivity lemmas | 0–3 | 0 |

The standard set is `propext`, `Classical.choice`, and `Quot.sound`. The exact
generated names live in `TrustInventory.lean`. Most dependencies in the two
export theorems arise through fixed scalar/boxing facts; two arise through
byte-assembly `bv_decide` proofs. Imported axioms are counted only if the named
theorem actually depends on them.

This inventory records existing debt, not new approval of those assumptions.
`FIR-BUG-wasm-none-endpoint-native-axiom-audit` stays confirmed until that debt
is resolved. Source hashes remain useful upstream drift checks; their success
does not establish an axiom-free endpoint or prove the upstream alpha bridge.

## Validation commands and integration wiring

```sh
python3 integration/talos/test_proof_trust.py
python3 integration/talos/check-proof-trust.py
make check
make talos-check
git diff --check
```

The Python gate scans maintained Lean sources under `Fir/`, `Inspect/`, the
root and Talos umbrellas, and `integration/talos/FirTalos/`, using the existing
comment/string-aware lexer and explicit project-axiom registry. It then builds
the audit dependency cone and forces direct batch elaboration of the audit,
so a stale audit olean cannot bypass the check. Scratch is worktree-local.

The Lean rejection tests inspect actual native-evaluation dependencies, a
temporary compiled theorem depending on an unregistered axiom, and a temporary
theorem depending on `sorryAx`; the latter two restore the environment. Source
tests reject integration axioms/placeholders and accept comments/strings.

The integration owner should wire the Python source scan and its tests into
the shared root gate. The compiled endpoint checks already participate in the
default Talos build through the W6-owned umbrella. The root `Makefile`, source
audit script, and repository-wide roadmap are integration-owned and are not
edited by this slice.

## Next proof checkpoint

Retain PA1/PA2 compiler provenance as the admission work. Add a terminal
correspondence requirement to PA3: from the internally constructed relation
and a terminating source observation, derive the existing executable
refined-return or refined-fault contract. Start by auditing the structured
machine's top-level return and trap endpoints and their Talos adequacy bridge.
Do not reintroduce a client source invariant in this corollary.

Separately remove native-evaluation dependencies in small owner-scoped batches,
starting with the fixed scalar/boxing facts, and update the measured inventory
downward. New public endpoints must begin with a standard-axioms-only budget.
W7's cache-elimination admissibility and complete linker preservation remain
separate generation contracts; this slice changes no emitter or artifact.
