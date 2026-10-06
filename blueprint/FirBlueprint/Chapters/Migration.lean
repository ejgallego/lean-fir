import Verso
import VersoManual
import VersoBlueprint
import FirBlueprint.Chapters.W6

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Source and evidence boundaries" =>
%%%
tag := "documentation-migration"
%%%

The Blueprint contains the selected proof argument, assumptions, open
obligations and contribution policy. Its maintained accounts are the
{ref "proof-scope"}[proof architecture], W6 nodes,
{ref "admission-coverage"}[admission coverage],
{ref "heap-caller-invariant"}[heap/caller argument],
{ref "external-domains"}[external contracts] and
{ref "contribution-policy"}[contribution policy].

Production definitions, proof/trust inventories, source audits and artifact
identities remain authoritative in their owner-maintained files. In particular,
`integration/talos/PLAN.md`, `W6-COVERAGE.md`, `W6-OBSERVABLE-CONTRACT-AND-TRUST.md`
and `docs/w6-source-admission-audit.md` retain their own owners and purposes.
Build, cache, worktree and handoff instructions remain in `AGENTS.md` and the
small Blueprint README. Generic authoring and CLI behavior belongs to VBP's
public documentation.

A checked Lean association describes a declaration in the loaded package.
A dated source citation can explain an accepted or historical result outside
that environment; it does not create an association or a fresh proof/trust
receipt. Chapters retain their reviewed revisions and distinguish source
identity, semantic correctness and execution/resource assumptions. The
{ref "retained-example-boundary"}[concrete-to-general account] illustrates
these boundaries for lean-zip.

Record new proof knowledge at its existing statement or chapter and identify
its supporting source. The completed migration census and historical review
chronology are preserved in Git history. Generated sites and local receipts
are disposable working state; they are not a second proof-status registry.
