(* Result-only visualizations: summary table, plots and dashboard. *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`"];

$vizResult = StructureAdaptiveEvolution[
  "Rule" -> ({{x, y}, {y, z}} -> {{x, z}}),
  "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
  "Rounds" -> 2,
  "MutationBudget" -> 4,
  "EvolutionLimits" -> <|"MaxGenerations" -> 4, "MaxEvents" -> 300, "TimeConstraint" -> 20.|>,
  "InitialStateDiagnostics" -> None,
  "RandomSeed" -> 11
];


VerificationTest[
  AssociationQ[$vizResult] && ListQ[$vizResult["Candidates"]] && Length[$vizResult["Candidates"]] >= 1,
  True,
  TestID -> "Viz-ResultAvailable"
]

VerificationTest[
  Module[{table = Normal @ EvolutionSummaryTable[$vizResult]},
    {
      Length[table] === Length[$vizResult["Candidates"]],
      SubsetQ[
        Keys[First[table]],
        {"EvaluationID", "MultiwayTransitionCount", "MultiwayLongestDerivation", "MultiwayLifetime", "ParetoMembership"}
      ]
    }
  ],
  {True, True},
  TestID -> "Viz-SummaryTableColumns"
]

VerificationTest[
  {Head[StrategyWeightPlot[$vizResult]], Head[FrontHistoryPlot[$vizResult]]},
  {Legended, Legended},
  TestID -> "Viz-WeightAndFrontPlots"
]

VerificationTest[
  Module[{dashboard = EvolutionDashboard[$vizResult]},
    {Head[dashboard], Length[First[dashboard]], Keys[First[dashboard]][[;; 6]]}
  ],
  {TabView, 7, {"Summary", "Candidates", "Pareto front", "Lineage", "Strategy weights", "Front history"}},
  TestID -> "Viz-DashboardTabs"
]

VerificationTest[
  With[{id = $vizResult["Candidates"][[1, "CandidateID"]]},
    Keys[First[EvolutionDashboard[$vizResult, id]]][[7]] === "Candidate " <> StringTake[id, UpTo[8]]
  ],
  True,
  TestID -> "Viz-DashboardFocus"
]

(* Visualizations consume stored results: nothing is evolved or evaluated. *)
VerificationTest[
  Catch[
    Block[
      {
        CanonicalMultiwayEvolution = (Throw["reevaluated", "viz"] &),
        EvaluateCandidate = (Throw["reevaluated", "viz"] &),
        RewriteEventEvolution = (Throw["reevaluated", "viz"] &)
      },
      EvolutionDashboard[$vizResult];
      EvolutionSummaryTable[$vizResult];
      StrategyWeightPlot[$vizResult];
      FrontHistoryPlot[$vizResult];
      "result-only"
    ],
    "viz"
  ],
  "result-only",
  TestID -> "Viz-ResultOnly"
]

VerificationTest[
  StringContainsQ[
    SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`Private`statusClaimSummary[$vizResult["Candidates"]],
    "verified to halt under this finite reachable exploration"
  ],
  True,
  TestID -> "Viz-OutcomeClaims"
]

VerificationTest[
  {
    FailureQ @ EvolutionDashboard[$vizResult, "no-such-candidate"],
    FailureQ @ CandidateEvolutionPlot[$vizResult, "no-such-candidate"],
    FailureQ @ EvolutionDashboard[<|"x" -> 1|>],
    FailureQ @ EvolutionDashboard[$vizResult, "ParetoMetrics" -> {"OnlyOne"}],
    FailureQ @ StrategyWeightPlot[KeyDrop[$vizResult, "StrategyWeightHistory"]],
    FailureQ @ FrontHistoryPlot[KeyDrop[$vizResult, "FrontHistory"]]
  },
  {True, True, True, True, True, True},
  TestID -> "Viz-Failures"
]
