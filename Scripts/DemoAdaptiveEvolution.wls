#!/usr/bin/env wolframscript
(* Fixed-seed demonstration of StructureAdaptiveEvolution.
   Run with: wolframscript -file DemoAdaptiveEvolution.wls *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$InputFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`"];

Print["=== StructureAdaptiveEvolution demo (RandomSeed -> 2026) ==="];

result = StructureAdaptiveEvolution[
  "Rule" -> ({{x, y}, {y, z}} -> {{x, z}}),
  "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 1}},
  "Rounds" -> 2,
  "MutationBudget" -> 10,
  "EvolutionLimits" -> <|
    "MaxGenerations" -> 6,
    "MaxEvents" -> 400,
    "MaxStates" -> 2000,
    "TimeConstraint" -> 20.
  |>,
  "RandomSeed" -> 2026
];

If[FailureQ[result],
  Print["Run failed: ", result];
  Exit[1]
];

Print["Run ID:               ", result["RunID"]];
Print["Versions:             ", KeyTake[result["Provenance"],
  {"PacletVersion", "HypergraphPacletVersion", "EvaluatorVersion", "WolframVersionNumber", "StateEquivalence"}]];
Print["Seed rule:            ", result["Seed"]["Rule"]];
Print["Seed initial state:   ", result["Seed"]["InitialState"]];
Print["Candidates evaluated: ", Length[result["Candidates"]]];
Print["Status counts:        ", Counts[Lookup[result["Candidates"], "Status"]]];
Print["Search front size:    ", Length[result["SearchParetoFront"]]];
Print["Solution front size:  ", Length[result["SolutionParetoFront"]]];
Print["Proposal failures:    ", Length[result["ProposalFailures"]]];
Print["Final weights:        ", result["FinalStrategyWeights"]];
Print["Performance:          ", KeyTake[result["Performance"],
  {"FreshEvaluations", "CacheHits", "DuplicateProposals", "EvaluationsPerSecond", "PeakStateCount"}]];

If[result["SolutionParetoFront"] === {},
  Print["No candidate was verified to halt under the stated limits."],
  Print["Verified to halt under this finite reachable exploration:"];
  Scan[
    Print["  ", StringTake[#["CandidateID"], 8], "  ", #["Rule"],
      "  states=", #["Fitness"]["MultiwayStateCount"],
      "  longestDerivation=", #["Fitness"]["MultiwayLongestDerivation"],
      "  maxVertices=", #["Fitness"]["HGMaxVerticesCount"],
      "  operators=", Lookup[#["Provenance"]["AppliedOperators"], "Operator", {}]] &,
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
  Replace[result["InitialStateDiagnostics"], _Missing -> <|"Finalists" -> {}|>]["Finalists"]
];

Print["=== Demo complete ==="];
