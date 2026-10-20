(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage[
  "SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`",
  {"SamuelFrerichs`StructureAdaptiveEvolution`"}
];


EvolutionSummaryTable::usage =
  "EvolutionSummaryTable[result] returns a Dataset summarizing every candidate of a StructureAdaptiveEvolution result.";

ParetoFrontPlot::usage =
  "ParetoFrontPlot[result, {metric1, metric2}] plots two fitness metrics for all valid candidates, highlighting the search and solution Pareto fronts.";

RuleLineageGraph::usage =
  "RuleLineageGraph[result] returns the mutation lineage graph of a StructureAdaptiveEvolution result.";

CandidateEvolutionPlot::usage =
  "CandidateEvolutionPlot[result, candidateID] plots the stored multiway states graph of a candidate without rerunning evolution.";

FitnessTrajectoryPlot::usage =
  "FitnessTrajectoryPlot[result, candidateID, metric] plots a metric along the mutation lineage from the seed to the given candidate.";

StrategyWeightPlot::usage =
  "StrategyWeightPlot[result] plots the mutation-strategy weights of a StructureAdaptiveEvolution result round by round (round 0 holds the initial weights), from the stored StrategyWeightHistory.";

FrontHistoryPlot::usage =
  "FrontHistoryPlot[result] plots the sizes of the search and solution Pareto fronts after every round, from the stored FrontHistory.";

EvolutionDashboard::usage =
  "EvolutionDashboard[result] returns a tabbed overview of a StructureAdaptiveEvolution result (run summary, candidate table, Pareto front, lineage, strategy weights, front history and one candidate) built only from stored data, without re-evaluating anything. EvolutionDashboard[result, candidateID] focuses the candidate tab on the given candidate. The option \"ParetoMetrics\" -> {metric1, metric2} chooses the plotted objectives.";


Begin["`Private`"];


(* ::Section:: *)
(*Helpers*)


candidateIndex[result_Association] :=
  Association[#["CandidateID"] -> # & /@ result["Candidates"]]


shortID[id_String] := StringTake[id, UpTo[8]]
shortID[other_] := other


paretoMembership[candidate_, result_Association] :=
  Which[
    MemberQ[Lookup[result["SolutionParetoFront"], "CandidateID", {}], candidate["CandidateID"]],
    "Solution",
    MemberQ[Lookup[result["SearchParetoFront"], "CandidateID", {}], candidate["CandidateID"]],
    "Search",
    True,
    "None"
  ]


metricValue[candidate_, metric_String] :=
  Lookup[Lookup[candidate, "Fitness", <||>], metric, Missing["NotComputed"]]


unknownCandidate[candidateID_] :=
  Failure[
    "UnknownCandidate",
    <|"Message" -> "No candidate with the given ID exists in the result.", "CandidateID" -> candidateID|>
  ]


resultQ[result_] := AssociationQ[result] && ListQ[Lookup[result, "Candidates", None]]


(* ::Section:: *)
(*Summary table*)


EvolutionSummaryTable[result_Association] :=
  Dataset @ Map[
    Function[candidate,
      <|
        "CandidateID" -> shortID[candidate["CandidateID"]],
        "EvaluationID" -> shortID[Lookup[candidate, "EvaluationID", Missing["NotRecorded"]]],
        "ParentID" -> shortID[candidate["ParentID"]],
        "Strategy" -> candidate["Strategy"],
        "Status" -> candidate["Status"],
        "CanonicalRule" -> candidate["Rule"],
        "CanonicalInitialState" -> candidate["InitialState"],
        "MultiwayStateCount" ->
          Replace[
            metricValue[candidate, "MultiwayStateCount"],
            _Missing :> Length[Lookup[candidate, "States", {}]]
          ],
        "MultiwayTransitionCount" ->
          Replace[
            metricValue[candidate, "MultiwayTransitionCount"],
            _Missing :> Lookup[candidate, "TransitionCount", Missing["NotComputed"]]
          ],
        "MultiwayLongestDerivation" ->
          Replace[
            metricValue[candidate, "MultiwayLongestDerivation"],
            _Missing :> Lookup[candidate, "LongestDerivation", Missing["NotComputed"]]
          ],
        "HGMaxVerticesCount" -> metricValue[candidate, "HGMaxVerticesCount"],
        "HGMaxEdgesCount" -> metricValue[candidate, "HGMaxEdgesCount"],
        "MultiwayLifetime" ->
          Replace[
            metricValue[candidate, "MultiwayLifetime"],
            _Missing :>
              Max[0, Length[DeleteCases[Lookup[candidate, "Generations", {}], {}]] - 1]
          ],
        "HaltedWithinCapQ" -> candidate["HaltedWithinCapQ"],
        "Runtime" -> candidate["Runtime"],
        "ParetoMembership" -> paretoMembership[candidate, result]
      |>
    ],
    result["Candidates"]
  ]


(* ::Section:: *)
(*Pareto front plot*)


ParetoFrontPlot[result_Association, {metric1_String, metric2_String}] := Module[
  {valid, point, groups},

  valid = Select[
    result["Candidates"],
    TrueQ[#["ValidQ"]] &&
      NumericQ[metricValue[#, metric1] /. True -> 1 /. False -> 0] &&
      NumericQ[metricValue[#, metric2] /. True -> 1 /. False -> 0] &
  ];

  point[candidate_] := Tooltip[
    {
      metricValue[candidate, metric1] /. True -> 1 /. False -> 0,
      metricValue[candidate, metric2] /. True -> 1 /. False -> 0
    },
    Column[{shortID[candidate["CandidateID"]], candidate["Strategy"], candidate["Status"]}]
  ];

  groups = GroupBy[valid, paretoMembership[#, result] &];

  ListPlot[
    {
      point /@ Lookup[groups, "None", {}],
      point /@ Lookup[groups, "Search", {}],
      point /@ Lookup[groups, "Solution", {}]
    },
    PlotStyle -> {Gray, Orange, Darker[Green]},
    PlotLegends -> {"Dominated", "Search front", "Solution front"},
    PlotMarkers -> {Automatic, Small},
    Frame -> True,
    FrameLabel -> {metric1, metric2}
  ]
]


(* ::Section:: *)
(*Lineage graph*)


RuleLineageGraph[result_Association] := Module[
  {edges, vertices},

  edges = DeleteDuplicates[
    DirectedEdge[#["Parent"], #["Child"]] & /@ result["LineageEdges"]
  ];

  vertices = DeleteDuplicates @ Join[
    Lookup[result["Candidates"], "CandidateID", {}],
    Catenate[List @@@ edges]
  ];

  Graph[
    vertices,
    edges,
    VertexLabels -> (# -> Placed[shortID[#], Tooltip] & /@ vertices),
    EdgeLabels ->
      (DirectedEdge[#["Parent"], #["Child"]] -> Placed[#["Strategy"], Tooltip] & /@
        result["LineageEdges"]),
    GraphLayout -> "LayeredDigraphEmbedding",
    VertexStyle -> Directive[White, EdgeForm[Gray]],
    VertexSize -> 0.4
  ]
]


(* ::Section:: *)
(*Candidate evolution plot*)


CandidateEvolutionPlot[result_Association, candidateID_String] := Module[
  {candidate, graph},

  candidate = Lookup[candidateIndex[result], candidateID, Missing["UnknownCandidate"]];

  If[MissingQ[candidate], Return @ unknownCandidate[candidateID]];

  graph = Lookup[candidate, "StatesGraph", Missing["NotStored"]];

  If[
    !GraphQ[graph],
    Return @ Failure[
      "NoStatesGraph",
      <|
        "Message" -> "The candidate has no stored states graph (its evaluation failed or was not stored).",
        "CandidateID" -> candidateID,
        "Status" -> Lookup[candidate, "Status", Missing["NotRecorded"]]
      |>
    ]
  ];

  Graph[
    graph,
    VertexLabels -> (# -> Placed[Grid[List /@ #], Tooltip] & /@ VertexList[graph]),
    GraphLayout -> "LayeredDigraphEmbedding",
    VertexStyle -> Directive[LightBlue, EdgeForm[Gray]],
    VertexSize -> 0.3,
    PlotLabel ->
      Row[{"Candidate ", shortID[candidateID], ": ", candidate["Status"]}]
  ]
]


(* ::Section:: *)
(*Fitness trajectory plot*)


FitnessTrajectoryPlot[result_Association, candidateID_String, metric_String] := Module[
  {index, chain, current, values},

  index = candidateIndex[result];

  If[!KeyExistsQ[index, candidateID], Return @ unknownCandidate[candidateID]];

  chain = {};
  current = index[candidateID];
  While[
    AssociationQ[current] && !MemberQ[chain, current],
    PrependTo[chain, current];
    current = Lookup[index, Lookup[current, "ParentID", Missing[]], Missing[]]
  ];

  values = MapIndexed[
    {First[#2] - 1, metricValue[#1, metric] /. True -> 1 /. False -> 0} &,
    chain
  ];

  ListLinePlot[
    Select[values, NumericQ[Last[#]] &],
    PlotMarkers -> Automatic,
    Frame -> True,
    FrameLabel -> {"Lineage step (seed = 0)", metric},
    PlotLabel ->
      Row[{"Lineage of ", shortID[candidateID], ": ", metric}]
  ]
]


(* ::Section:: *)
(*Strategy weights and front history*)


StrategyWeightPlot[result_Association] := Module[
  {history, strategies, adaptive},

  history = Lookup[result, "StrategyWeightHistory", {}];

  If[
    !MatchQ[history, {__Association}],
    Return @ Failure[
      "NoWeightHistory",
      <|"Message" -> "The result has no stored strategy weight history."|>
    ]
  ];

  strategies = Union @@ (Keys /@ history);
  adaptive = Lookup[Lookup[result, "Configuration", <||>], "AdaptiveWeights", Missing["NotRecorded"]];

  ListLinePlot[
    Table[
      MapIndexed[{First[#2] - 1, Lookup[#1, strategy, 0]} &, history],
      {strategy, strategies}
    ],
    PlotLegends -> strategies,
    PlotMarkers -> Automatic,
    PlotRange -> {All, {0, All}},
    Frame -> True,
    FrameLabel -> {"Round (0 = initial weights)", "Strategy weight"},
    PlotLabel -> If[adaptive === False, "Strategy weights (fixed)", "Strategy weights"]
  ]
]


FrontHistoryPlot[result_Association] := Module[
  {history},

  history = Lookup[result, "FrontHistory", {}];

  If[
    !MatchQ[history, {__Association}],
    Return @ Failure[
      "NoFrontHistory",
      <|"Message" -> "The result has no stored front history (no completed rounds)."|>
    ]
  ];

  ListLinePlot[
    {
      {#["Round"], Length[#["SearchFrontIDs"]]} & /@ history,
      {#["Round"], Length[#["SolutionFrontIDs"]]} & /@ history
    },
    PlotLegends -> {"Search front", "Solution front"},
    PlotStyle -> {Orange, Darker[Green]},
    PlotMarkers -> Automatic,
    PlotRange -> {All, {0, All}},
    Frame -> True,
    FrameLabel -> {"Round", "Front size"}
  ]
]


(* ::Section:: *)
(*Dashboard*)


$preferredParetoMetrics = {
  "MultiwayStateCount", "MultiwayLongestDerivation", "MultiwayTransitionCount",
  "HGMaxVerticesCount", "HGMaxEdgesCount"
};


(* Two numeric fitness metrics to plot: preferred names first, then any
   other metric with a numeric value for some candidate; None when there
   are fewer than two. *)
defaultParetoMetrics[result_Association] := Module[{names, numeric, ordered},
  names = DeleteDuplicates @ Catenate[Keys[Lookup[#, "Fitness", <||>]] & /@ result["Candidates"]];
  numeric = Select[names, Function[metric, AnyTrue[result["Candidates"], NumericQ[metricValue[#, metric]] &]]];
  ordered = Join[
    Select[$preferredParetoMetrics, MemberQ[numeric, #] &],
    Complement[numeric, $preferredParetoMetrics]
  ];
  If[Length[ordered] >= 2, Take[ordered, 2], None]
]


(* Solution front first, then search front, then the baseline. *)
defaultFocus[result_Association] :=
  First[
    Join[
      Lookup[Lookup[result, "SolutionParetoFront", {}], "CandidateID", {}],
      Lookup[Lookup[result, "SearchParetoFront", {}], "CandidateID", {}],
      Lookup[{Lookup[result, "Baseline", <||>]}, "CandidateID", {}] /. _Missing -> Nothing,
      Lookup[result["Candidates"], "CandidateID", {}]
    ],
    Missing["NoCandidates"]
  ]


statusClaimSummary[candidates_List] := Module[{counts},
  counts = Counts[Lookup[candidates, "Status", Missing["NotRecorded"]]];
  StringRiffle[
    DeleteCases[
      {
        If[Lookup[counts, "Halted", 0] > 0,
          ToString[counts["Halted"]] <> " verified to halt under this finite reachable exploration", Nothing],
        If[Lookup[counts, "CycleDetected", 0] > 0,
          ToString[counts["CycleDetected"]] <> " with a detected cycle (an infinite derivation exists)", Nothing],
        With[{capped = Total @ KeyDrop[counts, {"Halted", "CycleDetected", "Invalid"}]},
          If[capped > 0, ToString[capped] <> " not resolved within the stated limits", Nothing]
        ],
        If[Lookup[counts, "Invalid", 0] > 0,
          ToString[counts["Invalid"]] <> " invalid (no conclusion)", Nothing]
      },
      Nothing
    ],
    "; "
  ] <> "."
]


runSummaryGrid[result_Association] := Module[
  {provenance, seed},
  provenance = Lookup[result, "Provenance", <||>];
  seed = Lookup[result, "Seed", <||>];
  Grid[
    {
      {"Run ID", Lookup[result, "RunID", Missing["NotRecorded"]]},
      {"Seed rule", Lookup[seed, "CanonicalRule", Missing["NotRecorded"]]},
      {"Seed initial state", Lookup[seed, "CanonicalInitialState", Missing["NotRecorded"]]},
      {"State equivalence", Lookup[provenance, "StateEquivalence", Missing["NotRecorded"]]},
      {"Rewrite semantics", Lookup[provenance, "RewriteSemantics", Missing["NotRecorded"]]},
      {"Versions", KeyTake[provenance, {"PacletVersion", "HypergraphPacletVersion", "EvaluatorVersion", "WolframVersion"}]},
      {"Random seed", Lookup[provenance, "RandomSeed", Missing["NotRecorded"]]},
      {"Candidates", Length[result["Candidates"]]},
      {"Outcomes", statusClaimSummary[result["Candidates"]]},
      {"Search front", Length[Lookup[result, "SearchParetoFront", {}]]},
      {"Solution front", Length[Lookup[result, "SolutionParetoFront", {}]]},
      {"Proposal failures", Length[Lookup[result, "ProposalFailures", {}]]},
      {"Performance", Lookup[result, "Performance", Missing["NotRecorded"]]}
    },
    Alignment -> Left,
    Frame -> All,
    Background -> {{LightGray, None}}
  ]
]


candidatePanel[result_Association, candidate_Association, metrics_] :=
  Column[
    {
      Grid[
        {
          {"Candidate", candidate["CandidateID"]},
          {"Evaluation ID", Lookup[candidate, "EvaluationID", Missing["NotRecorded"]]},
          {"Rule", candidate["Rule"]},
          {"Initial state", candidate["InitialState"]},
          {"Strategy", Lookup[candidate, "Strategy", Missing["NotRecorded"]]},
          {"Applied operators",
            Lookup[Lookup[Lookup[candidate, "Provenance", <||>], "AppliedOperators", {}], "Operator", {}]},
          {"Status", Lookup[candidate, "Status", Missing["NotRecorded"]]},
          {"Limits reached", Lookup[candidate, "LimitsReached", {}]},
          {"Front membership", Lookup[Lookup[result, "FrontMembership", <||>], candidate["CandidateID"], Missing["NotRecorded"]]},
          {"Fitness", Lookup[candidate, "Fitness", <||>]}
        },
        Alignment -> Left,
        Frame -> All,
        Background -> {{LightGray, None}}
      ],
      CandidateEvolutionPlot[result, candidate["CandidateID"]],
      If[
        ListQ[metrics],
        FitnessTrajectoryPlot[result, candidate["CandidateID"], First[metrics]],
        Nothing
      ]
    },
    Spacings -> 2
  ]


Options[EvolutionDashboard] = {"ParetoMetrics" -> Automatic};

EvolutionDashboard[result_Association, opts : OptionsPattern[]] :=
  EvolutionDashboard[result, Automatic, opts]

EvolutionDashboard[result_Association, focusSpec : (_String | Automatic), opts : OptionsPattern[]] := Module[
  {index, focus, metrics},

  If[
    !resultQ[result],
    Return @ Failure["NotAResult", <|"Message" -> "Expected a StructureAdaptiveEvolution result association."|>]
  ];

  index = candidateIndex[result];
  focus = Replace[focusSpec, Automatic :> defaultFocus[result]];
  If[!KeyExistsQ[index, focus], Return @ unknownCandidate[focus]];

  metrics = Replace[OptionValue["ParetoMetrics"], Automatic :> defaultParetoMetrics[result]];
  If[
    !MatchQ[metrics, {_String, _String} | None],
    Return @ Failure["InvalidParetoMetrics", <|"Message" -> "\"ParetoMetrics\" must be Automatic or a list of two metric names.", "ParetoMetrics" -> metrics|>]
  ];

  TabView[
    {
      "Summary" -> runSummaryGrid[result],
      "Candidates" -> EvolutionSummaryTable[result],
      "Pareto front" ->
        If[metrics === None, "Fewer than two numeric fitness metrics are stored.", ParetoFrontPlot[result, metrics]],
      "Lineage" -> RuleLineageGraph[result],
      "Strategy weights" -> StrategyWeightPlot[result],
      "Front history" -> FrontHistoryPlot[result],
      "Candidate " <> shortID[focus] -> candidatePanel[result, index[focus], metrics]
    }
  ]
]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];


(* The visualizations act on StructureAdaptiveEvolution results, so loading
   them also puts the main package context on $ContextPath. *)
If[
  !MemberQ[$ContextPath, "SamuelFrerichs`StructureAdaptiveEvolution`"],
  PrependTo[$ContextPath, "SamuelFrerichs`StructureAdaptiveEvolution`"]
];
