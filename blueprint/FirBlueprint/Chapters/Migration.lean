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
{ref "proof-scope"}[proof architecture], {ref "w6-formal-catalog"}[formal catalog],
{ref "admission-coverage"}[admission coverage],
{ref "heap-caller-invariant"}[heap/caller argument],
{ref "external-domains"}[external contracts] and
{ref "contribution-policy"}[contribution policy].

Lean definitions, proofs and their compiled checks determine the formal
results. Owner-maintained audits, case inventories and reproduction guides
record how those results were investigated and checked; they do not form a
parallel mathematical roadmap or proof-status registry. The single
{ref "source-disposition-inventory"}[supporting-evidence section] identifies
those records and their reviewed revisions. Repository setup and integration
follow the operational rules in the contributor's current checkout.

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
