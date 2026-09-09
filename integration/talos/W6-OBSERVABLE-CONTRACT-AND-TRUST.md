# W6 observable contract and compiled trust audit

Review follow-up, 2026-09-09. Baseline: W6 `7affa1d2`, which includes the
conservative W7 recycler source at `e488c816`. The external review inspected
ancestor `a5449905`. The first checkpoint adds proof tests and audit tooling;
its successor adds the structured terminal-return bridge below. Neither
changes runtime behavior or a shared semantic relation.
The following terminal-extraction slice recovers the bridge inputs from the
unchanged validated global relation.
The precise-return successor retains the exact active-function result kind
at the two producer interfaces that previously hid it existentially.
The terminal-simulation successor then removes the separately supplied target
prefix by composing the existing classifier's ranked simulation.

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

## Terminal extraction from the global relation

`ConcreteTerminalExtraction.lean` removes the separately supplied yielded-value
relation and checked-frame arguments from the assembly boundary:

```text
supported export + exact entry-argument count + finite target prefix
  + existing validated global relation
  + successful final source step returning v
  => there exists a represented kind k such that executable Wasm returns v
     with RefinedReturnPost at k
```

`sourceCoreReturned_terminal` and `sourceExecReturned_terminal` show that a
successful final observation can arise only from a yielded value with no
remaining source continuation. An external response resumes execution rather
than creating a successful terminal observation. The source observation is
also identified exactly, including its heap, world and external-event trace.

`ConcreteStructuredValidatedCodeGlobalOutcome.terminalYield_of_control`
recovers the existing yielded-value relation and supported frame stack. A
staged external result cannot be mistaken for a terminal return: it still has
its bind frame. All other non-return branches have different source control.
The function and export `terminatesWith_of_validatedReturn` corollaries then
apply the reviewed executable return bridge, including arbitrary caller-tail
restoration for the function form.

The result kind remains existential. This slice does **not** establish that
it equals the root export's selected ABI, and does not weaken that remaining
goal. The finite target prefix is still an internal simulation assembly input,
not a new application-client certificate. No admission predicate, simulation
relation, runtime behavior, or trusted axiom was added or changed.

## Precise return producers

The return rule already proves the exact active-function result ABI. The new
`ConcreteStructuredCodePointwiseRel.advance_return_precise` exposes that fact
instead of existentially hiding the result kind. It uses the same current-node
admission and successful source step as `advance_return`; the old theorem is
now a compatibility wrapper around the precise one.

`ConcreteStructuredValidatedCodeOutcome.advance_returnPrecise_of_step`
transports the same precision through suspended-frame validation. Its returned
outcome has both its `functionResult` and its represented `kind` indexed by the
same active-function result. It also exposes the unchanged source/target frame
equalities. The existing `advance_returnAt_of_step` keeps its public signature
by packaging this stronger local outcome into the witness-indexed global
relation.

This is a hidden-interface repair, not a new provenance assumption: no premise
was added, and the existing source-semantic return admission is still required.
In particular, physical lane compatibility alone is not treated as semantic
result refinement. The new producer lemmas do not change the global relation,
which can still hide the precise kind, or establish that the active function
is the root export. Retaining those facts across the whole simulation remains
the next obligation.

## Source termination through the compiler simulation

`ConcreteTerminalSimulation.lean` closes the target-prefix assembly boundary:

```text
supported export + universal current-step classifier
  + ordinary concrete entry contracts + correct argument count
  + successful source evaluation returning v
  => executable Wasm export termination with RefinedReturnPost for v
     at some represented kind k
```

`ConcreteSupportedFunction.terminatesWith_of_classifiedExecSteps` obtains the
target prefix and terminal related state from the existing
`ConcreteRankedTraceSimulation.execSteps`, then applies terminal extraction.
It preserves arbitrary caller operand tails. The export-facing
`terminatesWith_of_classifiedExecEvaluates` constructs the initial relation
from production validation and the concrete entry frame; its caller supplies
neither a simulation relation nor a target path. It also identifies the source
observation exactly as `ReturnedObservation resultRuntime value`, retaining
heap, world, and external trace alongside the represented value.
`terminatesWith_of_classifiedRun` accepts an ordinary successful executable
interpreter run via the existing `run_done_sound` theorem. Target execution
and a sufficient target fuel bound are derived, not assumed.

These are conditional result theorems, not the closed PA3 endpoint. The
universal `ConcreteStructuredCurrentStepClassifier` remains a compiler-proof
obligation. Its general derivation still depends on unfinished admission work
and explicit runtime/resource safety. No caller-chosen source invariant or
per-program execution certificate is added, and source evaluation is simply
the antecedent of partial correctness, not a termination claim for all inputs.
The result kind is still existential; the theorem does not yet justify
decoding at the root export's selected ABI. Global root-kind provenance and
trap semantics remain separate. No existing relation is redesigned.

### Remaining terminal assembly obligations

| Obligation | Exact current evidence | Remaining work |
|---|---|---|
| Recover the terminal yield | `sourceExecReturned_terminal`, `ConcreteStructuredValidatedCodeGlobalOutcome.terminalYield_of_control`, and the function/export `terminatesWith_of_validatedReturn` lemmas | Discharged for the existing global relation and a successful final source step. |
| Preserve the export's selected result ABI | `ConcreteStructuredCodePointwiseRel.advance_return_precise` and `ConcreteStructuredValidatedCodeOutcome.advance_returnPrecise_of_step` now retain the exact active-function kind through local return production | The general returned outcome still permits an independent `kind`; compatibility with no caller is only `True`. Retain producer precision and root result identity across the global relation, without adding a client assumption. |
| Connect source termination to executable return | `terminatesWith_of_classifiedExecSteps`, `terminatesWith_of_classifiedExecEvaluates`, and `terminatesWith_of_classifiedRun` compose the existing ranked prefix with terminal extraction and adequacy | Discharged conditional on the existing universal classifier and entry contracts, with existential represented kind. Compiler admission closure and root-kind provenance are not discharged. |
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
| all five terminal-extraction and validated-return lemmas | 3 | 0 |
| both precise-return producer lemmas | 3 | 0 |
| all three classified terminal-simulation lemmas | 3 | 0 |

The standard set is `propext`, `Classical.choice`, and `Quot.sound`. The exact
generated names live in `TrustInventory.lean`. Most dependencies in the two
export theorems arise through fixed scalar/boxing facts; two arise through
byte-assembly `bv_decide` proofs. Imported axioms are counted only if the named
theorem actually depends on them.

The classified terminal theorems are generic in the existing classifier. Their
standard-only inventories do not remove the generated dependencies of a
particular classifier construction or application instance; such instances
must still receive their own exact audits.

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

Integration at main `1121f917` wires the expanded source scan and its tests into
the shared root gate, and forces the compiled audit in `make talos-check`.
The endpoint checks also participate in the default Talos build through the
W6-owned umbrella. The root `Makefile`, source audit script, and repository-wide
roadmap remain integration-owned and are not edited by the terminal-proof slice.

## Next proof checkpoint

Retain PA1/PA2 compiler provenance as the admission work. For PA3's terminal
corollary, the maintained global relation now supplies the terminal yielded
state, and the local return producers now retain the exact active-function
result kind. The classifier's simulation now also supplies the complete target
prefix internally. Carry precise producer and root result identity through
global simulation so the new classified terminal corollaries can state the
root export's selected ABI, then discharge the universal compiler classifier
through the ongoing admission work.
Handle the trap-model extension separately.
Do not reintroduce a client source invariant, target path, or ABI-provenance
assumption in the final corollary.

Separately remove native-evaluation dependencies in small owner-scoped batches,
starting with the fixed scalar/boxing facts, and update the measured inventory
downward. New public endpoints must begin with a standard-axioms-only budget.
W7's cache-elimination admissibility and complete linker preservation remain
separate generation contracts; this slice changes no emitter or artifact.
