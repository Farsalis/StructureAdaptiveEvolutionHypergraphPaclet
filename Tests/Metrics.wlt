PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

(* Known vertex/edge counts under unordered, duplicate-free semantics. *)
VerificationTest[
  Module[{m = HypergraphBasicSizeMetrics[{{1, 2}, {2, 1}, {2, 3}, {3, 3}}]},
    {m["HypergraphEdgesCount"], m["HypergraphVerticesCount"]}
  ],
  {3, 3},
  TestID -> "Metrics-KnownCounts"
]

VerificationTest[
  HypergraphBasicSizeMetrics[{}]["HypergraphEdgesCount"],
  0,
  TestID -> "Metrics-EmptyStateGuard"
]

(* Degree is hyperedge incidence, not clique degree. *)
VerificationTest[
  DegreeMetrics[{{1, 2, 3}, {1, 4}}]["MaxVertexDegree"],
  2,
  TestID -> "Metrics-IncidenceDegree"
]

VerificationTest[
  DegreeMetrics[{}],
  <|"MaxVertexDegree" -> 0, "VertexDegreeVariance" -> 0.|>,
  TestID -> "Metrics-DegreeEmptyGuard"
]

(* Aggregates over a states list. *)
VerificationTest[
  Module[{m = HypergraphBasicSizeMetrics[{{{1, 2}}, {{1, 2}, {2, 3}}}]},
    {m["HGMaxEdgesCount"], m["HGMaxVerticesCount"], m["HGMaxEdgeToVertexRatio"]}
  ],
  {2, 3, N[2/3]},
  TestID -> "Metrics-StatesAggregates"
]

(* FinalStateSizeMetrics reads the last state (regression: undefined hg). *)
VerificationTest[
  Module[{m = FinalStateSizeMetrics[{{{1, 2}}, {{1, 2}, {2, 3}}}]},
    {m["FinalEdgeCount"], m["FinalVertexCount"]}
  ],
  {2, 3},
  TestID -> "Metrics-FinalStateSize"
]

(* Branching metrics on a known degree sequence. *)
VerificationTest[
  Module[{g = Graph[{1 -> 2, 1 -> 3, 2 -> 4}],
          m},
    m = BranchingUncertainty[g];
    {m["MeanBranchingStrength"], m["BranchingVertexFraction"]}
  ],
  {0.5, 0.5},
  TestID -> "Metrics-BranchingKnownDegrees"
]

(* Reconvergence on a hand-built diamond. *)
VerificationTest[
  ReconvergenceReport[
    Graph[{1 -> 2, 1 -> 3, 2 -> 4, 3 -> 4}]]["ReconvergenceRatio"],
  1.,
  TestID -> "Metrics-ReconvergenceDiamond"
]

VerificationTest[
  ReconvergenceReport[
    Graph[{1 -> 2, 1 -> 3}]]["ReconvergenceRatio"],
  0.,
  TestID -> "Metrics-NoReconvergence"
]

(* Registry: every default-goal metric has a Function and known Input. *)
VerificationTest[
  Module[{registry = Symbol[$P <> "$FitnessMetricRegistry"],
          inputs = Symbol[$P <> "$AllowedMetricInputs"]},
    {
      SubsetQ[
        Keys[registry],
        {"HaltedWithinCapQ", "MultiwayStateCount", "MultiwayTransitionCount",
         "MaxMultiwayFrontierSize", "MultiwayLifetime", "TerminalStateCount",
         "NonIsomorphicTerminalStateCount", "HGMaxVerticesCount",
         "HGMaxEdgesCount", "HGMaxEdgeToVertexRatio", "Runtime"}
      ],
      AllTrue[Values[registry], KeyExistsQ[#, "Function"] &],
      AllTrue[Values[registry], MemberQ[inputs, #["Input"]] &]
    }
  ],
  {True, True, True},
  TestID -> "Metrics-RegistryComplete"
]

(* Registry functions produce correct values on a real evaluation. *)
VerificationTest[
  Module[{cfg, cand},
    cfg = ValidateEvolutionConfiguration[
      <|"FitnessMetrics" -> {
          "MultiwayStateCount", "MultiwayTransitionCount", "MultiwayLifetime",
          "TerminalStateCount", "NonIsomorphicTerminalStateCount",
          "MaxMultiwayFrontierSize"},
        "MutationStrategies" -> {"GrowthBudget"},
        "EvolutionLimits" -> <|"MaxGenerations" -> 10|>|>];
    Symbol[$P <> "ClearEvaluationCache"][];
    cand = EvaluateCandidate[
      <|"CandidateID" -> "m",
        "Rule" -> ({{1, 2}, {2, 3}} -> {{1, 3}}),
        "InitialState" -> {{1, 2}, {2, 3}, {3, 4}}|>, cfg];
    KeyTake[cand["Fitness"],
      {"MultiwayStateCount", "MultiwayTransitionCount", "MultiwayLifetime",
       "TerminalStateCount", "NonIsomorphicTerminalStateCount"}]
  ],
  <|"MultiwayStateCount" -> 3, "MultiwayTransitionCount" -> 2,
    "MultiwayLifetime" -> 2, "TerminalStateCount" -> 1,
    "NonIsomorphicTerminalStateCount" -> 1|>,
  TestID -> "Metrics-RegistryValuesOnEvolution"
]

(* Metric result validation rejects wrong types. *)
VerificationTest[
  FailureQ @ Symbol[$P <> "ValidateFitnessMetricResult"][
    "MultiwayStateCount", <|"Validator" -> NumericQ|>, "oops"],
  True,
  TestID -> "Metrics-ValidatorRejects"
]

(* Runtime metrics are numeric and nonnegative. *)
VerificationTest[
  Module[{m = HypergraphRuntimeAndLifetime[
      {{1, 2}, {2, 3}} -> {{1, 3}}, {{1, 2}, {2, 3}, {3, 4}}, 5]},
    {NumericQ[m["Runtime"]] && m["Runtime"] >= 0, m["Lifetime"], m["HaltedWithinCapQ"]}
  ],
  {True, 2, True},
  TestID -> "Metrics-RuntimeLifetime"
]

VerificationTest[
  Module[{m = MWHypergraphRuntimeAndLifetime[
      {{1, 2}, {2, 3}} -> {{1, 3}}, {{1, 2}, {2, 3}, {3, 4}}]},
    {NumericQ[m["MultiwayRuntime"]], m["MultiwayLifetime"]}
  ],
  {True, 2},
  TestID -> "Metrics-MultiwayRuntimeLifetime"
]
