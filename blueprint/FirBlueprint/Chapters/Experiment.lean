import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "What this experiment tells us" =>

The baseline links 18 existing declarations and describes six open targets.
The full graph renders 24 nodes and 34 edges. Grouping provides a useful view
of the argument's layers. Statement/proof edge separation and manual/inferred
origins survive the query interface. These are useful foundations to preserve.

# Which premise would a contribution remove?

Compare {bpref "conditional-return"}[], {bpref "admission-interface"}[] and
{bpref "admission-closure"}[]. The definition and conditional theorem are
formalized, while constructing the compiler law is open. A mathematical
dependency edge points to the assumption's definition. It cannot by itself
say that another open theorem will discharge a particular hypothesis.

The proposed improvement is an explicit relation between an obligation and
the premise it removes at a named consumer, with retained execution contracts
shown separately. This is a proposed product feature; the pilot expresses it
in prose.

# What is actually ready to work on?

At the pinned Blueprint version, `vbp query work-queue` recommends proof work
for {bpref "provenance-closure"}[], {bpref "heap-miss-closure"}[] and
{bpref "fault-closure"}[]. They have no associated formal statement yet.
One is part of active invariant design. Tags documenting that situation do not
change the readiness calculation.

A useful frontier would explain why each task is ready or blocked, separating
statement review, proof work, dependency work and consumer integration. An
inferred or manually planned graph alone does not establish contributor
readiness. A selected-goal view should retain paths from useful tasks to
{bpref "closed-export"}[] while collapsing completed subarguments.

# Which edges are evidence?

The existing declarations use inferred Lean dependencies. Open targets have
manually authored proof plans. The pilot intentionally expands only selected
branches of the 20-branch admission audit. The graph should help readers
distinguish a proposed plan, a partial overview and a checked decomposition.
The current query interface preserves edge origin and statement/proof axes,
which is a useful start.

# Which kinds of completion matter?

The graph reports the linked declarations as formalized. FIR separately audits
exact transitive axioms and public theorem contracts. The return endpoint
still carries generated axiom debt. A proof can also be locally checked before
its exact commit has been accepted into the integration branch.

Formalization, premise elimination, trust policy and integration evidence need
separate explanations. The goal is to present existing FIR evidence clearly,
without maintaining a duplicate validation registry in the Blueprint.

# Contribution trial

The repository's `blueprint/CONTRIBUTING.md` specifies the task packet: exact
statement, explanation, pinned environment, prerequisites, intended consumer,
trust policy and local acceptance command. W6 reviews the selected statements.
No external task has been published by this pilot.

The first trial should return a proof that is consumed by FIR and removes a
specific assumption or axiom. The experiment should record the work needed to
understand, prove and integrate it. This will test the proposed frontier
semantics as well as the upcoming contribution-service integration.

# Reproduce and report

From the `blueprint` package, use `lake exe vbp query work-queue`,
`lake exe vbp query uses admission-closure`, and
`lake exe vbp query used-by heap-miss-closure`.
The detailed findings and acceptance scenarios are in
`blueprint/EVALUATION.md`. They also cover the template creation mismatch,
nested Lake discovery, and the large node query payload without status fields.

The dependency graph and formalization summary follow this chapter. Their
computed colors should be read with the distinctions above in mind.
