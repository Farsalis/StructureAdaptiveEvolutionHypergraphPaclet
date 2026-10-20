PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`"];

$fastLimits = <|"MaxGenerations" -> 3, "MaxEvents" -> 150, "TimeConstraint" -> 15.|>;

(* 1. Explicit rule + explicit state + Growth-budget + one round. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y}} -> {{x, z}, {z, y}}),
      "InitialState" -> {{1, 2}},
      "MutationStrategies" -> {"GrowthBudget"},
      "Rounds" -> 1,
      "MutationBudget" -> 4,
      "EvolutionLimits" -> $fastLimits,
      "RandomSeed" -> 1
    ];
    {
      AssociationQ[result],
      result["Baseline"]["Strategy"],
      Length[result["Candidates"]] >= 1,
      DeleteDuplicates @ Lookup[Rest @ result["Candidates"], "Strategy"],
      ListQ[result["SearchParetoFront"]]
    }
  ],
  {True, "Seed", True, {"GrowthBudget"}, True},
  TestID -> "Integ-ExplicitSeedOneRound"
]

(* 2. Automatic Registry seed with fixed random seed (requires internet on
   first retrieval). *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> Automatic,
      "InitialState" -> Automatic,
      "MutationStrategies" -> {"RuntimeThrottling"},
      "Rounds" -> 1,
      "MutationBudget" -> 2,
      "EvolutionLimits" ->
        <|"MaxGenerations" -> 2, "MaxEvents" -> 60, "TimeConstraint" -> 20.|>,
      "RandomSeed" -> 99
    ];
    If[FailureQ[result],
      result[[1]] === "SeedResolutionFailed",  (* offline fallback accepted *)
      {result["Seed"]["Source"], result["Seed"]["InitiallyApplicableQ"]} ===
        {"WolframModelData", True}
    ]
  ],
  True,
  TestID -> "Integ-AutomaticRegistrySeed"
]

(* 3. Two implemented strategies with adaptive allocation over two rounds. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y}, {y, z}} -> {{x, z}}),
      "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
      "MutationStrategies" -> {"GrowthBudget", "OverlappingMatch"},
      "Rounds" -> 2,
      "MutationBudget" -> 5,
      "EvolutionLimits" -> $fastLimits,
      "RandomSeed" -> 2
    ];
    {
      Sort @ Keys[result["FinalStrategyWeights"]],
      Length[result["StrategyWeightHistory"]],
      AllTrue[Values[result["FinalStrategyWeights"]], NonNegative],
      Abs[Total[Values[result["FinalStrategyWeights"]]] - 1] < 1.*^-9
    }
  ],
  {{"GrowthBudget", "OverlappingMatch"}, 3, True, True},
  TestID -> "Integ-TwoStrategyAdaptiveRun"
]

(* 4. One custom metric, validated on the baseline evaluation. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y}} -> {{x, z}, {z, y}}),
      "InitialState" -> {{1, 2}},
      "MutationStrategies" -> {"GrowthBudget"},
      "CustomFitnessMetrics" -> <|
        "StateGraphSize" -> <|
          "Function" -> Function[graph, VertexCount[graph] + EdgeCount[graph]],
          "Input" -> "StatesGraph",
          "Direction" -> "Maximize"
        |>
      |>,
      "Rounds" -> 1,
      "MutationBudget" -> 3,
      "EvolutionLimits" -> $fastLimits,
      "RandomSeed" -> 3
    ];
    {
      NumericQ[result["Baseline"]["Fitness"]["StateGraphSize"]],
      MemberQ[result["Configuration"]["FitnessMetrics"], "StateGraphSize"],
      KeyExistsQ[result["MetricChampions"], "StateGraphSize"]
    }
  ],
  {True, True, True},
  TestID -> "Integ-CustomMetric"
]

(* 5. No terminating candidate found: empty solution front, retained search
   front, explicit round log. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y}} -> {{x, z}, {z, y}}),
      "InitialState" -> {{1, 2}},
      "MutationStrategies" -> {"GrowthBudget"},
      "Rounds" -> 1,
      "MutationBudget" -> 3,
      "EvolutionLimits" -> <|"MaxGenerations" -> 2, "MaxEvents" -> 40, "TimeConstraint" -> 10.|>,
      "RandomSeed" -> 4
    ];
    {
      result["SolutionParetoFront"],
      Length[result["SearchParetoFront"]] >= 1,
      MatchQ[result["RunLog"], {__Association}]
    }
  ],
  {{}, True, True},
  TestID -> "Integ-NoSolutionRun"
]

(* 6. At least one verified terminating candidate found. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y}, {y, z}} -> {{x, z}}),
      "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
      "Rounds" -> 1,
      "MutationBudget" -> 6,
      "EvolutionLimits" -> <|"MaxGenerations" -> 6, "MaxEvents" -> 300, "TimeConstraint" -> 20.|>,
      "RandomSeed" -> 77
    ];
    $solutionResult = result;
    {
      Length[result["SolutionParetoFront"]] >= 1,
      DeleteDuplicates @ Lookup[result["SolutionParetoFront"], "Status"],
      AllTrue[result["SolutionParetoFront"], #["TransitionCount"] >= 1 &]
    }
  ],
  {True, {"Halted"}, True},
  TestID -> "Integ-VerifiedSolutionRun"
]

(* 7. Finalist initial-state diagnostics. *)
VerificationTest[
  Module[{diag = $solutionResult["InitialStateDiagnostics"]},
    {
      AssociationQ[diag],
      Length[diag["Finalists"]] >= 1,
      AllTrue[
        diag["Finalists"],
        NumericQ[#["InitiallyApplicableRate"]] || MissingQ[#["InitiallyApplicableRate"]] &
      ],
      KeyExistsQ[diag, "EnsemblePolicy"]
    }
  ],
  {True, True, True, True},
  TestID -> "Integ-FinalistDiagnostics"
]

(* 8. The result feeds every visualization without rerunning evolution. *)
VerificationTest[
  Module[{cid},
    cid = $solutionResult["SolutionParetoFront"][[1, "CandidateID"]];
    {
      Head @ EvolutionSummaryTable[$solutionResult],
      MatchQ[ParetoFrontPlot[$solutionResult, {"MultiwayStateCount", "HGMaxVerticesCount"}],
        _Legended | _Graphics],
      GraphQ @ RuleLineageGraph[$solutionResult],
      GraphQ @ CandidateEvolutionPlot[$solutionResult, cid],
      MatchQ[FitnessTrajectoryPlot[$solutionResult, cid, "MultiwayStateCount"], _Graphics],
      FailureQ @ CandidateEvolutionPlot[$solutionResult, "no-such-id"]
    }
  ],
  {Dataset, True, True, True, True, True},
  TestID -> "Integ-VisualizationConsumption"
]

(* 9. Deterministic candidate identity under a fixed random seed. *)
VerificationTest[
  Module[{run},
    run[] := Lookup[
      StructureAdaptiveEvolution[
        "Rule" -> ({{x, y}} -> {{x, z}, {z, y}}),
        "InitialState" -> {{1, 2}},
        "Rounds" -> 1,
        "MutationBudget" -> 5,
        "EvolutionLimits" -> $fastLimits,
        "RandomSeed" -> 2024
      ]["Candidates"],
      "CandidateID"
    ];
    run[] === run[]
  ],
  True,
  TestID -> "Integ-DeterministicWithFixedSeed"
]

(* 10. A custom metric whose output fails its validator on the baseline
   evaluation aborts the run with a clear Failure. *)
VerificationTest[
  Module[{failure},
    failure = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y}} -> {{x, z}, {z, y}}),
      "InitialState" -> {{1, 2}},
      "MutationStrategies" -> {"GrowthBudget"},
      "CustomFitnessMetrics" -> <|
        "BrokenMetric" -> <|
          "Function" -> Function[graph, "not a number"],
          "Input" -> "StatesGraph",
          "Direction" -> "Maximize"
        |>
      |>,
      "Rounds" -> 1,
      "MutationBudget" -> 2,
      "EvolutionLimits" -> $fastLimits,
      "RandomSeed" -> 6
    ];
    {FailureQ[failure], failure[[1]]}
  ],
  {True, "InvalidCustomMetricResult"},
  TestID -> "Integ-CustomMetricValidatorOnBaseline"
]

(* 11. Invalid options fail with informative Failure objects. *)
VerificationTest[
  Module[{failure = StructureAdaptiveEvolution["Rounds" -> -1]},
    {FailureQ[failure], failure[[2, "Field"]]}
  ],
  {True, "Rounds"},
  TestID -> "Integ-InvalidOptionsFail"
]
