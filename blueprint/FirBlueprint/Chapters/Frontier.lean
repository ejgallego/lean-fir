import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Frontier explanations and acceptance cases" =>
%%%
tag := "frontier-cases"
%%%

This chapter specifies useful selected-goal explanations. Its original queue
and status evidence was measured at FIR `4b260be59`, VBP
`b2c83f7f14d8d247783bd71421b1215ae2ac8916`, Lean 4.34.1. That dated report
has reproduction inputs in the {ref "pr475-status-cases"}[completion evidence cases]. The scenarios below describe
desired explanations, not newly run status-transition tests or a claim about
latest upstream behavior.

# Start with a selected goal

For {bpref "validated-return"}[], the composition is written and checked;
the external specification and admission construction remain incomplete.
A useful answer should identify what would advance this goal and why.

:::table +header
*
  * Work item
  * Local evidence
  * Useful next action
*
  * {bpref "external-spec"}[external-spec]
  * An explicit definition hole; intended primitive semantics under review
  * Review clauses, implementation coverage and retained assumptions using the {ref "external-domains"}[external-domain account].
*
  * {bpref "admission-closure"}[admission-closure]
  * An elaborated theorem with a direct proof hole and an unsettled specification dependency
  * Review its statement and develop the authored branch/invariant plan; a frozen contributor task is premature.
*
  * {bpref "validated-return"}[validated-return]
  * Checked assembly using incomplete specification/proof ancestors
  * Work on those prerequisites and recheck their consumer when they change; its existing body needs no independent proof task.
*
  * {bpref "provenance-closure"}[provenance-closure]
  * Prose target, now split into static coverage and semantic preservation plans
  * Review the {ref "provenance-design"}[shared interfaces and alternatives] before fixing formal signatures.
*
  * {bpref "heap-miss-closure"}[heap-miss-closure]
  * Prose target with checked entry/return/publication ingredients
  * Review the documented maintained relation; compose general heap-result admission. Accepted W6 `f6850d79f` already retains the fresh saved validated caller; the unassociated newer result is identified in the heap/caller chapter.
:::

The last two rows are authored subproblems of admission. Their detailed
{ref "heap-caller-invariant"}[heap/caller account] distinguishes accepted
construction/caller progress from the remaining central admission assembly.
These accepted results remain cited source evidence without direct Blueprint
Lean associations.

The concrete {bpref "stored-export-instance"}[] has a separate current proof
route through program-specific admission and {bpref "conditional-return"}[].
Its scope is every related admitted input of one fixed program. Later
specialization of the general {bpref "validated-return"}[] is a planned proof
replacement; a frontier must not add that unfinished theorem as the independent
instance's prerequisite. The {ref "retained-example-boundary"}[concrete account]
distinguishes existing source/initializer theorems from this open whole-export
claim and finite execution validation.

The
{ref "admission-coverage"}[coverage chapter] now accounts for all twenty audit
rows, including other open families. Neither table claims an exhaustive minimal
frontier or a kernel-checked decomposition. Statement design and exploratory
proof work may proceed together; an unsettled specification need not serialize
every activity. The graph alone does not establish mathematical independence.

# Keep paths and their evidence

Read each arrow below as “consumer needs prerequisite”:

```
validated-return -- statement, inferred --> external-spec
validated-return -- proof, inferred -----> admission-closure
admission-closure -- statement, inferred -> external-spec
admission-closure -- proof, authored ----> provenance-closure
admission-closure -- proof, authored ----> heap-miss-closure
```

Deduplicate {bpref "external-spec"}[external-spec] as a work item while retaining both reasons it
matters. Show an immediate prerequisite and its proposed subproblems together,
preserving statement/proof axes and inferred/authored origin. An empty edge
list for a prose target does not establish a settled statement or independence.

{bpref "address-space"}[] and {bpref "finite-runtime"}[] are retained execution
conditions, not requests to prove those bounds universally.
{bpref "conditional-return"}[] is reusable for its stated assumptions.
{bpref "fault-closure"}[] and {bpref "resident-linking"}[] are outside this
successful-return goal's prerequisite cone. Selecting {bpref "closed-export"}[]
adds fault work; selecting resident linking adds another implementation boundary.

# Selecting the full closed export

{bpref "closed-export"}[] has the broader property $`P_{\mathrm{closed}}`:
finite-prefix agreement, exact returns and corresponding source semantic faults.
Its selected-goal advice must cover all three components:

:::table +header
*
  * Component
  * Existing consumer and remaining work
*
  * Finite prefixes
  * {bpref "rooted-steps"}[] retains world and ordered trace agreement once compiler admission and the entry/resource conditions are supplied.
*
  * Successful returns
  * {bpref "validated-return"}[] assembles the selected-ABI return contract; its external specification and admission construction remain incomplete.
*
  * Semantic faults
  * {bpref "conditional-fault"}[] consumes a fault-simulation certificate. {bpref "fault-closure"}[] must construct the fault evidence and executable trap from compiler validation and the maintained relation, including source/concrete external-failure agreement.
:::

The rough fault plan includes terminal leaves, transport through successful
prefixes and trap/export adequacy. Its interface alternatives are in
{bpref "fault-closure"}[] and the {ref "fault-safety"}[fault/safety account].
The successful-response external specification alone supplies no agreement for
external `.error` outcomes. Target-only failure exclusion (T4S) is a distinct
claim; it needs an explicit statement and its own justification when included
in a selected goal. Neither terminal-return closure nor an operation audit
establishes the full fault theorem. Resident implementation, encoding and
released artifacts remain further boundaries.

# Evidence comes before advice

The reviewed candidate recommended proof work for both the admitted admission
theorem and the already-written return assembly. It also recommended proof
work for prose targets without formal signatures. A single `nextStep` field
did not distinguish a local hole, inherited incompleteness, or statement design.

A separate classifier bug at that candidate lost proof-gap evidence when a
statement dependency was incomplete. The inspected admission and return bodies
were available: one contained a direct hole and the other did not, yet both
exported only statement/dependency evidence. The
{ref "pr475-status-cases"}[independent-axis reproduction] identifies the pipeline
scoping error. The classifier must
preserve the evidence before frontier logic derives advice; a graph algorithm
should not compensate for evidence discarded earlier.

For hidden imported bodies, a cached {name}`sorryAx` footprint can establish
incompleteness without locating a direct hole in the consumer. Preserve that
uncertainty or consult evidence captured when the body was available. Absence
of a direct marker alone cannot certify local completion.

# What a frontier explanation must contain

1. What is locally present: prose, elaborated statement, unfinished definition
   or proof, or checked composition, with declaration and source location.
2. What is incomplete: direct/inherited evidence and statement/proof axes,
   including simultaneous gaps and any uncertainty about imported bodies.
3. Why it matters to the selected goal: a dependency path with its origin and
   intent, including the difference between a plan and checked dependencies.
4. What can start: statement design, local proof, prerequisite work or consumer
   rechecking, without hiding unsettled interfaces.
5. What must be reviewed before contribution handoff: exact statement and
   revision, environment and consumer. An owner, priority or tag is insufficient.

These are acceptance questions, not a proposed storage schema. Existing tags
record editorial review notes; this experiment does not give arbitrary tag
strings new automatic readiness semantics.

# Eight acceptance cases
%%%
tag := "frontier-transitions"
%%%

These preserve the original eight cases while linking to the current argument.
“Complete” and “revise” rows are hypothetical transitions to evaluate against a
future implementation; no proofs or specifications were changed to run them.

:::table +header
*
  * Case
  * Expected explanation or transition
*
  * Case 1: {bpref "external-spec"}[external-spec] as it stands
  * Definition/statement design, with intended semantics and source; its sorry body is not an ordinary theorem proof task.
*
  * Case 2: {bpref "admission-closure"}[admission-closure] as it stands
  * A local proof hole and an unsettled specification coexist. Exploratory proof/design work is allowed; immutable external task publication is premature.
*
  * Case 3: {bpref "validated-return"}[validated-return] as it stands
  * A checked assembly with incomplete dependencies, linked to {bpref "external-spec"}[external-spec] and {bpref "admission-closure"}[admission-closure]; no independent task to rewrite its existing proof.
*
  * Case 4: Provenance and heap targets as they stand
  * Formal statement/design work with authored routes and review notes. Complete graph prerequisites do not supply missing Lean signatures.
*
  * Case 5: Complete {bpref "external-spec"}[external-spec] while preserving its signature
  * Recompute statement dependencies. Admission's direct proof hole remains, and return still waits on admission.
*
  * Case 6: Complete the admission proof
  * Recheck the consumer and recompute Lean status and dependencies. Review obsolete authored plan edges rather than leaving unexplained blockers.
*
  * Case 7: Revise either statement
  * Identify the changed source revision and recheck consumers. Prior successful assembly is evidence for the previous statement.
*
  * Case 8: Select closed-export instead
  * Include fault work and its path. Successful-return completion does not establish the broader theorem.
:::

FIR's trust policy and accepted integration evidence are separate from these
completion/readiness explanations. Passing a local proof check does not by
itself satisfy those gates or publish a contribution task.

# Relation to the VBP findings and formalization roadmap

BP-FIR-03 concerns actionable stage and contributor readiness; BP-FIR-06 concerns
selected-goal paths; BP-FIR-08 concerns compact node inspection with status and
reasons. BP-FIR-09 supplies the transitive-hole baseline; the mixed-axis report
adds a distinct classifier case. BP-FIR-10 concerns statement revisions, and
BP-FIR-11 the scope/evidence of a proposed decomposition. The
{ref "evaluation-findings"}[acceptance cases] contain their reviewed revisions
and useful reproduction inputs.

The proposed upstream formalization roadmap asks for completion to exclude a
known {name}`sorryAx` dependency, preservation of independent gap evidence, and
frontier answers with justified actions and valid explanatory paths. Its
extraction boundary must account for uncertainty; proposed frontier laws must
also address cycles, missing nodes and unsettled statements. These are proposed
properties and design questions, not laws proved by this FIR documentation.

The immediate review is case by case: establish the evidence, explain the
mathematical work, and then decide whether existing authoring/query surfaces
suffice or a VBP change is needed. The status-classifier correction and the
frontier-algorithm design remain separate upstream concerns.
