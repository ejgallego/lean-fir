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

What should a compiled program guarantee, and how can we prove it? Start with
the {ref "w6-theorem-menu"}[theorem statements and their status]: conditional
results are checked, the selected whole-program instance is open, and general
compiler correctness is the eventual target. A fixed-program instance still
quantifies every allowed input. The initial proof route is independent of the
unfinished general theorem; later the same statement can follow by specialization.

The argument then introduces the {ref "w6-machines"}[source and target machines],
their {ref "w6-rooted-relation"}[rooted relation], and the
{ref "w6-proof-mechanism"}[step, finite-path and terminal proof]. The
{ref "retained-example-boundary"}[lean-zip account] distinguishes genuine source
and local initializer proofs from the open whole-export property. Detailed
invariants and operation obligations extend that argument through the graph.
Development policy and tool-evaluation cases follow the mathematical chapters.

The README supplies repository setup. Production definitions and owner audits
remain the source and trust authorities; checked declaration associations and
dated source-reviewed evidence are identified separately.

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
