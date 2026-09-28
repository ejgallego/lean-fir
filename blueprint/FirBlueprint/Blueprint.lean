import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FirBlueprint.Chapters.W6
import FirBlueprint.Chapters.Experiment

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "FIR proof development experiment" =>

This Blueprint is a small, executable map of the W6 compiler-correctness
argument. Its second purpose is to evaluate how Blueprint communicates proof
dependencies, conditional results and the actionable contribution frontier.
The accompanying repository files `blueprint/EVALUATION.md` and
`blueprint/CONTRIBUTING.md` record observations and contribution boundaries.

{include 0 FirBlueprint.Chapters.W6}

{include 0 FirBlueprint.Chapters.Experiment}

{blueprint_graph (direction := "LR")}
{blueprint_summary}
