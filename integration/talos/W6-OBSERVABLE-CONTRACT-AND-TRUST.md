# W6 observable contract and compiled trust audit

Review follow-up, 2026-09-09. Baseline: W6 `7affa1d2`, which includes the
conservative W7 recycler source at `e488c816`. The external review inspected
ancestor `a5449905`. The first checkpoint adds proof tests and audit tooling;
its successor adds the structured terminal-return bridge below. Neither
changes runtime behavior or a shared semantic relation.

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

## Structured return bridge

`ConcreteTerminalCorrectness.lean` now connects the already represented result
to actual Talos execution. Its main assembly helper is
`ConcreteSupportedExport.terminatesWith_of_structuredYield`:

```text
supported export + exact entry-argument count
  + finite structured prefix from that export's entry
  + existing yielded-value relation and checked frame stack
  + no remaining source continuation
  => executable export termination with RefinedReturnPost
```

This is an internal assembly lemma, not the closed compiler theorem. The
ranked simulation must produce the target prefix; clients must not be asked
to prove it. No new simulation, invariant, or certificate is introduced.

The reusable proof derives rather than assumes:

- terminal target label unwinding from
  `ConcreteStructuredSupportedFrameStack.returning_halts`;
- full heap/world/trace/value refinement and a clear failure channel from
  `ConcreteStructuredYieldFocus.refinedReturnPost`;
- a finite path to the exact halted store and stack from
  `ConcreteStructuredYieldFocus.finitePath_halted`;
- loop-arity safety from successful adaptation, using the existing
  `StructuredWasmStep.finitePath_run_of_adapt`;
- one sufficient fuel bound, singleton result selection, and caller-tail
  restoration. The function form supports an arbitrary caller operand tail;
  the export form specializes it to empty.

The yielding function's context is deliberately independent of the entry
function's context. Execution adequacy needs the actual target prefix, not an
extra equality between these compiler identities.

### Remaining terminal assembly obligations

| Obligation | Exact current evidence | Remaining work |
|---|---|---|
| Recover the terminal yield | `ConcreteStructuredValidatedCodeGlobalOutcome.returned` carries `ConcreteStructuredValidatedReturnedOutcome.yielded` and `.frames.supported` | Invert successful source termination against the maintained global relation and feed the recovered facts to the bridge. |
| Preserve the export's selected result ABI | `ConcreteStructuredCodeCoreRel.advance_return_at_functionResult` produces the exact kind; `ConcreteStructuredValidatedReturnedOutcome.activeResult` records the active function's result | The returned outcome's independent `kind` index is not equated to `functionResult`; compatibility with no caller is only `True`. Recover or retain the producer fact and the root result identity before existential packaging, without adding a client assumption. |
| Connect source termination to the prefix | `ConcreteRankedTraceSimulation.execSteps` gives the related target prefix for successful source transitions | Combine the terminal source observation with that specific relation, rather than destructing the lossy public existential package. |
| Match faults | `StructuredWasmControl` has running/breaking/returning/halted states, and `StructuredWasmOutcome` describes successful control only | A trap-aware extension and its adequacy proof are a separately coordinated semantic change. Existing `ConcreteFaultSimulation` results do not automatically supply this missing structured-machine branch. |

These are interface obligations, not evidence of incorrect generated code.
In particular, the current return rule does produce the precise result kind;
the audit identifies where its general relation forgets that precision.
Resource exhaustion remains governed by explicit preconditions, not an
unproved general matching-failure claim.

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
| all five structured terminal-return bridge lemmas | 2–3 | 0 |

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

Retain PA1/PA2 compiler provenance as the admission work. For PA3's terminal
corollary, connect the maintained global relation to the return bridge above:
recover its terminal yielded state, precise selected result kind, and the
prefix constructed by simulation. Handle the trap-model extension separately.
Do not reintroduce a client source invariant, target path, or ABI-provenance
assumption in the final corollary.

Separately remove native-evaluation dependencies in small owner-scoped batches,
starting with the fixed scalar/boxing facts, and update the measured inventory
downward. New public endpoints must begin with a standard-axioms-only budget.
W7's cache-elimination admissibility and complete linker preservation remain
separate generation contracts; this slice changes no emitter or artifact.
