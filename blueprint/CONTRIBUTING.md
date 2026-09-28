# Contribution experiment

The first purpose of this pilot is to make work understandable. Public task
publication follows only when an exact statement and environment are reviewed.
An open Blueprint node is not automatically a ready Prove2Me task.

## Candidate selection

[The scalar trust-reduction packets](TASKS.md) preserve existing decoding and
boxing signatures. W6 reviewed them: the full replacements are blocked by
opaque `Lean.Expr.eqv`; their current trust inventories contain ten and seven
generated dependencies respectively. The only smaller candidate is removing
the contradictory UInt64 branch from T1, with a source-based expected change
of ten to six dependencies. That delta still needs an exact compiled audit.
It is unassigned; no proof lease or external service task exists.

W6 is selecting small stable obligations through local coordination thread
`ROOT-W6-20260928-100`. The current candidate areas are:

| Area | Intended consequence | Readiness boundary |
| --- | --- | --- |
| A non-directional producer/use-site fact | Remove a semantic argument or return-provenance input at an existing admission consumer | Select an exact production use and review its quantified statement |
| A construction-preservation lemma | Carry entry cutoff/scope through an intermediate initializer state | Check W6 ownership and current invariant migration before assigning |
| A contained native-axiom reduction | Reduce an exact transitive trust inventory using a kernel proof | Only the T1 UInt64 branch is currently ready to scope; full T1/T2 need a reviewed proof interface |

These are selection categories, not three assigned theorem tasks. General heap
lazy-miss closure and the entire fault counterpart are too broad for the first
external contribution. No new caller invariant, source restriction, arbitrary
axiom or weakened public conclusion may be introduced to complete a task.

## Required task packet

Each selected task needs:

- stable Blueprint label and intended parent consumer;
- exact Lean statement, imports and a plain-language reading;
- immutable FIR commit, Lean toolchain, Talos/Blueprint dependency manifests;
- prerequisite declarations and a short suggested argument;
- permitted axioms and a focused local check command;
- owner/review contact and integration path;
- an explicit distinction between proof accepted by a service and proof
  consumed by FIR's parent theorem.

The task must use FIR's real definitions. If a portable mathematical subproblem
is extracted, the checked bridge back to its FIR consumer belongs in the task's
acceptance criteria. Definition copies that silently drift are not acceptable.

## Prove2Me boundary

The upcoming Blueprint integration is an experimental delivery option. Its
ability to reproduce the pinned FIR/Talos package environment and to represent
FIR's existing trust debt needs verification before publication. Keep the
Blueprint useful locally while this is settled. Store any service task ID as an
external reference to the stable label; the Lean declaration and reviewed
statement remain the mathematical identity.

A returned proof is reviewed for exact type and dependency changes, built in
FIR's environment, and integrated under the normal focused proof, `make check`
and `make talos-check` gates. The public contract regressions protect the parent
endpoint. The experiment should record whether the contribution actually
removed a premise or axiom at that endpoint, and the effort needed to achieve
that integration.
