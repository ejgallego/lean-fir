import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FirBlueprint.Chapters.CompilerArgument
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

Start with the {ref "compiler-argument"}[compiler argument]: a concrete
initializer call motivates the machines, result representation and
successful-return guarantee, then its worked proof leads to the selected-program
and general theorem strategy. The {ref "w6-formal-catalog"}[formal catalog]
records checked associations and open obligations. Semantic and trust
boundaries, detailed invariants and the remaining proof obligations follow.

The README supplies repository setup. Production definitions and owner audits
remain the source and trust authorities; checked declaration associations and
dated source-reviewed evidence are identified separately.

{include 0 FirBlueprint.Chapters.CompilerArgument}

{include 0 FirBlueprint.Chapters.W6}

{include 0 FirBlueprint.Chapters.ProofScope}

{include 0 FirBlueprint.Chapters.HeapInvariant}

{include 0 FirBlueprint.Chapters.AdmissionMap}

{include 0 FirBlueprint.Chapters.Provenance}

{include 0 FirBlueprint.Chapters.ExternalDomains}

{include 0 FirBlueprint.Chapters.Roadmap}

{include 0 FirBlueprint.Chapters.Contribution}

{include 0 FirBlueprint.Chapters.Migration}

{include 0 FirBlueprint.Chapters.Experiment}

{include 0 FirBlueprint.Chapters.Frontier}

{blueprint_graph (direction := "LR")}
{blueprint_summary}
