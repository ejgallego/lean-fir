import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FirBlueprint.Chapters.W6
import FirBlueprint.Chapters.Experiment
import FirBlueprint.Chapters.Roadmap
import FirBlueprint.Chapters.AdmissionMap
import FirBlueprint.Chapters.Provenance
import FirBlueprint.Chapters.Migration
import FirBlueprint.Chapters.ExternalDomains
import FirBlueprint.Chapters.Frontier
import FirBlueprint.Chapters.HeapInvariant
import FirBlueprint.Chapters.Contribution
import FirBlueprint.Chapters.ProofScope

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "FIR compiler correctness Blueprint" =>

This Blueprint records the selected W6 compiler-correctness argument and its
development roadmap. Start with the
{ref "retained-example-boundary"}[concrete lean-zip proofs and compiler property],
then follow the {ref "development-roadmap"}[roadmap] from an independent program
instance to general correctness and future specialization. The roadmap also
separates Blueprint evaluation from the FIR proof development being documented.
The chapters contain the proof account, contribution policy and VBP acceptance
cases. The README supplies repository setup; source and trust evidence remain
with production definitions and owner audits. Chapters distinguish checked
declaration associations from explicitly dated source facts.

{include 0 FirBlueprint.Chapters.Roadmap}

{include 0 FirBlueprint.Chapters.Migration}

{include 0 FirBlueprint.Chapters.ProofScope}

{include 0 FirBlueprint.Chapters.W6}

{include 0 FirBlueprint.Chapters.HeapInvariant}

{include 0 FirBlueprint.Chapters.AdmissionMap}

{include 0 FirBlueprint.Chapters.Provenance}

{include 0 FirBlueprint.Chapters.ExternalDomains}

{include 0 FirBlueprint.Chapters.Contribution}

{include 0 FirBlueprint.Chapters.Experiment}

{include 0 FirBlueprint.Chapters.Frontier}

{blueprint_graph (direction := "LR")}
{blueprint_summary}
