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


(* ::Section:: *)
(*Summary table*)


EvolutionSummaryTable[result_Association] :=
  Dataset @ Map[
    Function[candidate,
      <|
        "CandidateID" -> shortID[candidate["CandidateID"]],
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

  If[
    MissingQ[candidate],
    Return @ Failure[
      "UnknownCandidate",
      <|"Message" -> "No candidate with the given ID exists in the result.",
        "CandidateID" -> candidateID|>
    ]
  ];

  graph = candidate["StatesGraph"];

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

  If[
    !KeyExistsQ[index, candidateID],
    Return @ Failure[
      "UnknownCandidate",
      <|"Message" -> "No candidate with the given ID exists in the result.",
        "CandidateID" -> candidateID|>
    ]
  ];

  chain = {};
  current = index[candidateID];
  While[
    AssociationQ[current],
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
(*Package Footer*)


End[];
EndPackage[];
