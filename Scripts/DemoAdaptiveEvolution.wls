#!/usr/bin/env wolframscript
(* Fixed-seed demonstration of the HypergraphGuidedAdaptiveEvolution MVP.
   Run with: wolframscript -file DemoAdaptiveEvolution.wls *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$InputFileName]]];
Needs["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`"];
Needs["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`Visualizations`"];

Print["=== HypergraphGuidedAdaptiveEvolution demo (RandomSeed -> 2026) ==="];

result = StructureAdaptiveEvolution[
  "Rule" -> ({{x, y}, {y, z}} -> {{x, z}}),
  "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 1}},
  "Rounds" -> 2,
  "MutationBudget" -> 10,
  "EvolutionLimits" -> <|
    "MaxGenerations" -> 6,
    "MaxEvents" -> 400,
    "TimeConstraint" -> 20.
  |>,
  "RandomSeed" -> 2026
];

If[FailureQ[result],
  Print["Run failed: ", result];
  Exit[1]
];

Print["Seed rule:            ", result["Seed"]["Rule"]];
Print["Seed initial state:   ", result["Seed"]["InitialState"]];
Print["Candidates evaluated: ", Length[result["Candidates"]]];
Print["Status counts:        ", Counts[Lookup[result["Candidates"], "Status"]]];
Print["Search front size:    ", Length[result["SearchParetoFront"]]];
Print["Solution front size:  ", Length[result["SolutionParetoFront"]]];
Print["Final weights:        ", result["FinalStrategyWeights"]];

If[result["SolutionParetoFront"] === {},
  Print["No verified terminating candidate was found under the supplied limits."],
  Print["Verified terminating solution(s):"];
  Scan[
    Print["  ", StringTake[#["CandidateID"], 8], "  ", #["Rule"],
      "  states=", #["Fitness"]["MultiwayStateCount"],
      "  maxVertices=", #["Fitness"]["HGMaxVerticesCount"]] &,
    result["SolutionParetoFront"]
  ]
];

Print[""];
Print["Summary table (first rows):"];
Print[Normal[EvolutionSummaryTable[result][;; UpTo[6]]] // Column];

Print[""];
Print["Finalist initial-state diagnostics:"];
Scan[
  Print["  ", StringTake[#["CandidateID"], 8],
    "  applicableRate=", #["InitiallyApplicableRate"],
    "  terminationRate=", #["TerminationRate"],
    "  medianStates=", #["MedianMultiwayStateCount"]] &,
  Replace[result["InitialStateDiagnostics"], m_Missing :> <|"Finalists" -> {}|>]["Finalists"]
];

Print["=== Demo complete ==="];
