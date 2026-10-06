import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Development roadmap" =>
%%%
tag := "development-roadmap"
%%%

This roadmap records the selected proof argument and its development plan.
Progress means that a reader can recover
the intended argument, assumptions, holes, design choices and useful next work
from this document. FIR proof work follows its owners; VBP evaluation checks
whether the tool can represent that argument and explain useful next actions.

Read the {ref "retained-example-boundary"}[concrete lean-zip account] first:
source application theorems and retained initializer proofs supply real
semantic examples. The {bpref "successful-export-property"}[successful-export property],
open {bpref "stored-export-instance"}[program instance] and general
{bpref "validated-return"}[compiler theorem] then use one exact return relation.
Finite execution checks remain validation evidence alongside this proof plan.

The W6 chapter contains the mathematical statements and dependency graph. This
page links to those nodes without adding planning arrows to the mathematical
graph. A checked conditional lemma, an unsettled statement and a completed
endpoint are different milestones.

The {ref "documentation-migration"}[source and evidence boundaries] distinguish
the maintained argument from production definitions, owner audits and build
instructions. The completed migration census remains in Git history.

# Blueprint work: capture, review, evaluate

## 1. Make the selected argument recoverable

Define the property and concrete instance before following
{bpref "validated-return"}[] to its intended conclusion,
retained execution assumptions, unfinished specification and admission proof.
The formal slice already exposes {bpref "external-spec"}[] and
{bpref "admission-closure"}[] as holes. Explain how the broader
{bpref "closed-export"}[] adds faults and how {bpref "resident-linking"}[]
adds another implementation boundary.

The {ref "admission-coverage"}[Admission coverage chapter] now maps all twenty audit rows to existing
ingredients and open obligations, reviewed at experiment FIR `93c2e7ec7` with accepted-main comparison at
`8f4222cb2`. Four previously
unrepresented families have explicit nodes: {bpref "direct-let-closure"}[],
{bpref "closure-call-closure"}[], {bpref "object-field-closure"}[] and
{bpref "scalar-field-closure"}[]. This closes the inventory gap in the prose;
it does not prove exhaustive assembly or preservation of the required invariant.

The {ref "provenance-design"}[shared provenance argument] now separates the
precise row's construction/coverage from semantic preservation and its existing
call/return consumers. Producer, projection and join transfer rules and the
checked-program alternatives are documented; their final formal signatures
still require mathematical owner review.
The {ref "external-domains"}[external-domain account] and
{ref "frontier-cases"}[frontier acceptance brief] now have rendered destinations.
The {ref "heap-caller-invariant"}[maintained heap/caller invariant] covers
construction regions, retained caller entries and publication alternatives.
The {ref "proof-scope"}[proof scope and boundaries] places this selected W6
argument within pass correctness, observations, trust and resident generation.
The accepted-main source review is dated 2026-10-05 at `8f4222cb2`; current
associations use the accepted-pin package and checkout described in the W6
chapter. Historical candidate evaluations retain their original environments.

## 2. Encode the reasoning behind open work

For each open obligation, capture the intended statement, retained hypotheses,
proposed argument, prerequisites, intended consumers and unresolved choices.
Use formal stubs where the statement is sufficiently understood; keep unsettled
alternatives explicit rather than freezing a guessed signature. Review whether
every missing premise has a visible obligation and a path from its consumer.

The existing Nat slice is a useful example: {bpref "nat-add-realization"}[]
proves handler behavior, {bpref "nat-add-admission"}[] proves a conditional
bridge, and {bpref "nat-add-site"}[] records the missing input construction.
The immediate Blueprint task is to make that distinction understandable and
queryable. Selecting its next lemma belongs to the FIR proof track below.

The rendered chapters capture the branch subfamilies, maintained heap/caller
relations, provenance transfer choices, external clauses, frontier cases and
{ref "statement-revisions"}[statement revision workflow]. Their open items
are mathematical/design questions.

Move conclusions and live design choices into their existing rendered account
as they are reviewed, with the source needed to assess the claim.

## 3. Turn each representation difficulty into a VBP acceptance case

First try existing declarations/stubs, associations, statement/proof `uses`,
dependency intent, owners, groups, tags and prose references. Mathematical
edges express dependencies; `bpref` links express navigation and planning.
Tags can record editorial review state but do not change computed readiness.

Evaluate these concrete cases, one at a time:

* *Hole evidence:* preserve statement and proof gaps simultaneously, including
  direct and inherited evidence. A checked assembly with incomplete prerequisites
  must remain distinguishable from an admitted local proof.
* *Selected-goal frontier:* explain what advances {bpref "validated-return"}[],
  why it matters, and whether statement design, proof, or consumer review remains.
  Retained resource assumptions must remain visible as conditions.
* *Dependency meaning:* preserve authored/inferred origin, statement/proof axis
  and auxiliary intent; make the overview's incomplete branch coverage clear.
* *Revision and contribution readiness:* identify the reviewed statement and
  environment. Keep a stable label while identifying changes to its statement.

For each case, record what current VBP can express, what requires prose, the
observed limitation at an exact revision, and the desired behavior. Distinguish
a correctness bug from a missing feature or an authoring problem before
requesting upstream work. The {ref "evaluation-findings"}[numbered evaluation findings] and
{ref "formalization-roadmap"}[formalization roadmap] make these cases
discoverable. Reproduction inputs and reviewed revisions belong with their
cases; historical review chronology remains in Git. Earlier observations
describe their tested revisions, not the latest upstream state.

The proposed upstream formalization roadmap covers completion soundness,
preservation of gap evidence and justified frontier explanations. These remain
proposals; this experiment does not establish those laws.

## Working agreement and review criterion

Keep the authoritative target statements, holes and proof plans in the
Blueprint. Use Lean and existing FIR gates for proof/trust evidence. Do not
build a second status database or a local replacement for VBP analysis.
New proof implementation is justified here only when a concrete Blueprint
evaluation question needs it; ordinary proof advancement stays with its owner.

Review a case by asking: can a reader explain the target, remaining work,
retained assumptions, design alternatives and route to its consumer without
recovering the chat history? The maintainer's most useful input is correction
of that mathematical account and prioritization of the resulting VBP cases.
The authoring work and evidence collection can proceed autonomously.

# FIR proof roadmap being documented

This track records mathematical development and its owners. It supplies the
subject matter for the Blueprint experiment; it does not assign new proof
implementation to this session. Current milestones are described below.

## From program instances to general correctness

1. Fix {bpref "successful-export-property"}[]: the source runtime/value,
   observation and selected export ABI agree at instance and general levels.
2. Prove {bpref "stored-export-instance"}[] independently for every admitted
   input of the captured stored-compression program. Checked static equations
   and genuine concrete semantic blocks guide its admission/invariant proof.
   This whole-export instance remains open.
3. Generalize the argument at {bpref "validated-return"}[], constructing the
   compiler-owned admission facts for supported programs. The same concrete
   instance can then be a corollary by specialization and premise discharge.

The future specialization route is a plan, with prose links; it is not a
current proof dependency of the independent instance. Closed computational
premises may reduce with {tactic}`cbv`; external behavior, entry refinement and finite
resources remain reviewed semantic/execution conditions. The source roundtrip
and stronger initializer theorems retain their distinct claims. A compiled
roundtrip further needs the source/capture, ByteArray, resident and released-byte
bridges in the {ref "retained-example-boundary"}[concrete account].

## Nat call from semantics to admission

The existing example slice is Nat addition in the actual validation interpreter.

1. *Checked:* {bpref "nat-add-contract"}[] states the exact sum response, including
   heap, next location and world. {bpref "nat-add-realization"}[] proves the real
   dispatcher succeeds on decoded tagged/heap arguments and supplies that response.
2. *Checked with explicit inputs:* {bpref "nat-add-admission"}[] consumes that
   result to establish production natural-result admission and exact allocation
   cost. The compiler call shape and ABI/argument facts remain inputs.
3. *Open proof-design task:* {bpref "nat-add-site"}[] reconstructs those inputs
   from the guarded validator/source-step boundary. In particular, resolve the
   difference between directional ABI refinement and the equality required by
   the current admission constructor.

The exit criterion is a reviewed Nat-addition slice whose admission follows
from the existing validated state and primitive semantics, without a new
caller-supplied call-shape or canonical-response premise. A theorem count or
a green conditional node does not establish this milestone. Blueprint-local
proofs require W6 review and normal integration before becoming accepted
production results.

## Shared semantic decision: Int responses

W6/root have the request to reconcile validation's tagged small-Int responses
with the present heap-only W6 contract. The recommended first acceptance case
is {InlineLean.lean}`Int.ofNat 0`: response, heap effects, refinement and allocation cost must
agree. The reviewed discrepancy is between a tagged small-Int validation
response and an always-allocating W6 response. One option is a representation-aware
W6 response/refinement and cost model, preserving validation behavior. Another
is an explicit normalization bridge with observation and ownership proofs.
The first is the review recommendation; the semantic owners must settle it.
This decision is still open in this Blueprint; it does not block documenting
the other obligations.

The discrepancy and checked example are in
`bugs/FIR-BUG-impure-none-external-int-response-contract.md`.
{bpref "external-spec"}[] remains an explicit hole while this and the wider
primitive coverage are reviewed. We must not make the specification reject
successful supported calls just to obtain admission.

## Assemble the external contract and implementation coverage

After the first slice, expand the reviewed primitive families and their effect
clauses. {bpref "external-realization"}[] must establish both correct successful
responses and availability on a stated, independently defined request domain.
Its current Nat proof is one component, not the global realization.

{bpref "external-admission"}[] connects those primitive contracts to compiler
admission. External initializers, mutating operations and families outside the
current pure admission inventory remain visible coverage work. The detailed
contract review is the {ref "external-domains"}[external-domain chapter].

## Close compiler admission and the selected endpoint

{bpref "provenance-closure"}[] and {bpref "heap-miss-closure"}[] can advance as
independent design strands under their owners. Together with external coverage
and the other branches of the source-admission audit, they feed
{bpref "admission-closure"}[]. The graph is a selected overview; the 20-branch
audit in `docs/w6-source-admission-audit.md` supplies the broader inventory.

The selected endpoint is {bpref "validated-return"}[]. Its composition is
already written; completing admission and the specification must be followed
by rechecking that composition at their reviewed statements. Address-space and
finite-runtime conditions remain explicit execution assumptions.

The broader {bpref "closed-export"}[] also needs {bpref "fault-closure"}[].
{bpref "resident-linking"}[] is a further implementation boundary. These are
later goals for this slice, not claims that return-only progress proves them.

## Contribution handoff comes after statement review

Once a precise local obligation is stable, use the
{ref "contribution-packet"}[rendered contribution packet] to prepare its pinned
statement, environment, proof prerequisites and production consumer. Evaluate the eventual Prove2Me integration on that concrete packet.
No external task is published or assigned by this roadmap. The {ref "scalar-trust-history"}[historical scalar trust-reduction case]
records the earlier candidates and their blockers with the tested revisions. Evaluating whether the Blueprint
can supply a complete, revision-pinned task packet is Blueprint work; solving
the selected theorem is proof work.
