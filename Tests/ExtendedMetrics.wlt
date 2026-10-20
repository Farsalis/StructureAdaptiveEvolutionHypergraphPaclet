(* Extended metrics: structural, branching/confluence, causal, update-order,
   local-persistence and branchial metric families, the BranchialGraphs
   artifact, and the classification criteria. *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";
$priv[name_String] := Symbol[$P <> name];

$registry := $priv["$FitnessMetricRegistry"];

(* A registered metric applied to an explicit input; given parameters
   replace the registry defaults. *)
$metric[name_String, input_] :=
  $priv["applyMetricFunction"][$registry[name], input];
$metric[name_String, input_, parameters_Association] :=
  $priv["applyMetricFunction"][Append[$registry[name], "Parameters" -> parameters], input];

(* A full EvaluateCandidate call computing the given metrics. *)
$evaluate[rule_, state_, metrics_List, options_Association : <||>] :=
  EvaluateCandidate[
    <|"Rule" -> rule, "InitialState" -> state|>,
    ValidateEvolutionConfiguration[Join[<|"FitnessMetrics" -> metrics|>, options]]
  ];

(* Numbers compare to 1e-9, everything else exactly. *)
$close[a_?NumericQ, b_?NumericQ] := Abs[a - b] < 10^-9;
$close[a_List, b_List] := Length[a] === Length[b] && And @@ MapThread[$close, {a, b}];
$close[a_, b_] := a === b;

$extendedMetrics = {
  "LargestComponentRatio", "NumberOfConnectedComponents", "LargestConnectedComponentSize",
  "EffectiveDimensionEstimate", "DimensionVariance", "MaxVertexDegree", "VertexDegreeVariance",
  "MaxVertexDegreeVariance", "HGMeanEdgeToVertexRatio", "FinalVertexCount", "FinalEdgeCount",
  "FinalDensity", "FinalMaxVertexDegree", "FinalVertexDegreeVariance", "OutDegreeEntropy",
  "MeanBranchingStrength", "ReconvergenceRatio", "ResolvedBranchPairRatio",
  "CausalInvariantWithinCapQ", "CausalMergeEventsRatio", "CausalDependencyEntropy",
  "RewriteActivityMean", "RewriteActivityEntropy", "UpdateOrderSensitivity",
  "CausalUpdateOrderSensitivity", "UpdateOrderTerminalOutcomeCount",
  "LocalComponentLifetimeMean", "LocalComponentLifetimeMax", "MotifPersistence", "HubPersistence",
  "EdgeSurvivalRate",
  "BranchialMeanDegree", "MeanBranchialDistance"
};

$contract = {{x, y}, {y, z}} -> {{x, z}};
$grow = {{x, y}} -> {{x, z}, {z, y}};
$branchGrow = {{x, y}} -> {{x, y}, {y, z}};
$delete = {{x, y}} -> {};
$stuck = {{x, y}, {y, z}} -> {};
(* Delete two adjacent edges or one edge: overlapping events, one terminal
   state. Contract or delete two adjacent edges: two terminal states. *)
$confluentSet = {{{x, y}, {y, z}} -> {}, {{u, v}} -> {}};
$divergentSet = {{{x, y}, {y, z}} -> {{x, z}}, {{u, v}, {v, w}} -> {}};
$cycle4 = {{1, 2}, {2, 3}, {3, 4}, {4, 1}};
$path2 = {{1, 2}, {2, 3}};
$path3 = {{1, 2}, {2, 3}, {3, 4}};
$pairs3 = {{1, 2}, {3, 4}, {5, 6}};
$pathMotif = {{motifA, motifB}, {motifB, motifC}};

$confluenceMetrics = {"ReconvergenceRatio", "ResolvedBranchPairRatio", "CausalInvariantWithinCapQ", "TerminalStateCount"};


(* ::Section:: *)
(*Registration*)


VerificationTest[
  {
    SubsetQ[Keys[$registry], $extendedMetrics],
    Union @ Lookup[Lookup[$registry, $extendedMetrics], "Stage"],
    Sort[$priv["$xmMetricNames"]] === Sort[$extendedMetrics],
    AllTrue[Lookup[Lookup[$registry, $extendedMetrics], "Description"], StringQ[#] && StringEndsQ[#, "."] &]
  },
  {True, {"Diagnostic"}, True, True},
  TestID -> "ExtendedMetrics-Registration"
]

VerificationTest[
  {
    Lookup[$registry["EffectiveDimensionEstimate"], {"Direction", "Target"}],
    Lookup[$registry["UpdateOrderTerminalOutcomeCount"], {"Direction", "Target"}],
    $registry["HGMeanEdgeToVertexRatio"]["Direction"],
    Lookup[$registry["CausalInvariantWithinCapQ"], {"ValueType", "Direction"}],
    $registry["ResolvedBranchPairRatio"]["Artifacts"],
    $registry["MotifPersistence"]["Parameters"],
    $registry["MeanBranchialDistance"]["Parameters"]
  },
  {
    {"Target", 2.}, {"Target", 1}, "Range", {"Boolean", "Maximize"},
    {"EventRecords"}, <|"Motif" -> Automatic|>, <|"Slice" -> Automatic|>
  },
  TestID -> "ExtendedMetrics-Specifications"
]

VerificationTest[
  {
    KeyExistsQ[$priv["$ArtifactBuilders"], "BranchialGraphs"],
    $priv["$ArtifactDependencies"]["BranchialGraphs"],
    MemberQ[$priv["$AllowedMetricInputs"], "BranchialGraphs"],
    SubsetQ[
      $priv["requiredArtifacts"][
        ValidateEvolutionConfiguration[<|"FitnessMetrics" -> {"ResolvedBranchPairRatio", "MeanBranchialDistance"}|>]
      ],
      {"EventRecords", "BranchialGraphs", "EvolutionGraph"}
    ]
  },
  {True, {"EvolutionGraph"}, True, True},
  TestID -> "ExtendedMetrics-ArtifactsRegisteredAndRequested"
]

VerificationTest[
  AssociationQ @ ValidateEvolutionConfiguration[<|
    "MetricOverrides" -> <|
      "ReconvergenceRatio" -> <|"Stage" -> "Objective"|>,
      "MotifPersistence" -> <|"Parameters" -> <|"Motif" -> $pathMotif|>|>,
      "MeanBranchialDistance" -> <|"Parameters" -> <|"Slice" -> 1|>|>
    |>
  |>],
  True,
  TestID -> "ExtendedMetrics-PromotableByOverrides"
]


(* ::Section:: *)
(*Structural metrics*)


VerificationTest[
  With[{states = {{{1, 2}, {3, 4}, {4, 5}}, {}, {{1, 2}, {2, 3}}}},
    {
      $metric["LargestComponentRatio", states],
      $metric["NumberOfConnectedComponents", states],
      $metric["LargestConnectedComponentSize", states]
    }
  ],
  {0.8, 2, 3},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-Components"
]

VerificationTest[
  With[{state = {{1, 2, 3}, {3, 4}, {5, 6}, {7}}},
    {
      $metric["LargestComponentRatio", {state}],
      $metric["NumberOfConnectedComponents", {state}],
      $metric["LargestConnectedComponentSize", {state}]
    } - Lookup[
      ComponentMetrics[state],
      {"LargestComponentRatio", "NumberOfConnectedComponents", "LargestConnectedComponentSize"}
    ]
  ],
  {0., 0, 0},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-ComponentsMatchSpatialProjection"
]

VerificationTest[
  With[{states = {{{1, 2}, {1, 3}, {1, 4}}, {{1, 2}}}},
    {
      $metric["MaxVertexDegree", states],
      $metric["VertexDegreeVariance", states],
      $metric["MaxVertexDegreeVariance", states],
      $metric["HGMeanEdgeToVertexRatio", {{{1, 2}, {2, 3}}, {{1, 2}}, {}}]
    }
  ],
  {3, 0.5, 1., 7/12},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-DegreesAndRatio"
]

VerificationTest[
  With[{grid = EdgeList[GridGraph[{4, 4}]] /. UndirectedEdge -> List},
    {
      $metric["EffectiveDimensionEstimate", {grid, {{1, 2}}}] - EffectiveDimensionEstimate[grid],
      $metric["DimensionVariance", {grid, {{1, 2}}, {}}] - DimensionVariance[grid]
    }
  ],
  {0., 0.},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-DimensionMeanOverStatesWithEstimate"
]

VerificationTest[
  With[{finals = {{{1, 2}, {2, 3}}, {}}},
    {
      $metric["FinalVertexCount", finals],
      $metric["FinalEdgeCount", finals],
      $metric["FinalMaxVertexDegree", finals],
      $metric["FinalVertexDegreeVariance", {{{1, 2}, {1, 3}, {1, 4}}}]
    }
  ],
  {1.5, 1., 1., 1.},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-TerminalStateMeans"
]

VerificationTest[
  {
    $metric["LargestComponentRatio", {{}}],
    $metric["LargestConnectedComponentSize", {{}}],
    $metric["MaxVertexDegree", {{}}],
    $metric["VertexDegreeVariance", {{}}],
    $metric["HGMeanEdgeToVertexRatio", {{}}],
    $metric["NumberOfConnectedComponents", {{}}],
    $metric["EffectiveDimensionEstimate", {{{1, 2}}, {}}],
    $metric["DimensionVariance", {{{1, 2}}}],
    $metric["FinalVertexCount", {}],
    $metric["FinalDensity", {}],
    $metric["FinalVertexDegreeVariance", {}]
  },
  {
    Missing["NoVertices"], Missing["NoVertices"], Missing["NoVertices"], Missing["NoVertices"],
    Missing["NoVertices"], 0, Missing["InsufficientStructure"], Missing["InsufficientStructure"],
    Missing["NoTerminalStates"], Missing["NoTerminalStates"], Missing["NoTerminalStates"]
  },
  TestID -> "ExtendedMetrics-StructuralMissing"
]


(* ::Section:: *)
(*Branching and confluence*)


VerificationTest[
  With[{candidate = $evaluate[$contract, $cycle4, $confluenceMetrics]},
    {candidate["Status"], Lookup[candidate["Fitness"], $confluenceMetrics]}
  ],
  {"Halted", {Missing["NoBranchPairs"], Missing["NoCriticalPairs"], True, 1}},
  TestID -> "ExtendedMetrics-ContractionOfCycleHaltsConfluent"
]

VerificationTest[
  With[{candidate = $evaluate[$confluentSet, $path2, $confluenceMetrics]},
    {candidate["Status"], Lookup[candidate["Fitness"], $confluenceMetrics]}
  ],
  {"Halted", {1., 1., True, 1}},
  TestID -> "ExtendedMetrics-ResolvedCriticalPairs"
]

VerificationTest[
  With[{candidate = $evaluate[$divergentSet, $path2, $confluenceMetrics]},
    {candidate["Status"], Lookup[candidate["Fitness"], $confluenceMetrics]}
  ],
  {"Halted", {0., 0., False, 2}},
  TestID -> "ExtendedMetrics-UnresolvedCriticalPairs"
]

VerificationTest[
  With[
    {
      candidate = $evaluate[
        $branchGrow, {{1, 2}}, {"CausalInvariantWithinCapQ", "ReconvergenceRatio"},
        <|"EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>
      ]
    },
    {candidate["Status"], candidate["Fitness"]["CausalInvariantWithinCapQ"], NumericQ[candidate["Fitness"]["ReconvergenceRatio"]]}
  ],
  {"GenerationCap", False, True},
  TestID -> "ExtendedMetrics-CappedExplorationNotCausalInvariant"
]

VerificationTest[
  With[{graph = Graph[{1 -> 2, 1 -> 3, 1 -> 6, 2 -> 4, 3 -> 5, 6 -> 4}]},
    {
      $metric["ReconvergenceRatio", graph],
      ReconvergenceReport[graph]["ReconvergenceRatio"],
      $metric["OutDegreeEntropy", graph],
      $metric["MeanBranchingStrength", graph]
    }
  ],
  {1/3, 1/3, N @ Entropy[2, {3, 1, 1, 1}], N @ Mean[Log2[{3, 1, 1, 1}]]},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-ReconvergenceOnHandBuiltGraph"
]

(* Events 1 and 2 overlap and their successors a, b reconverge at t; events
   3 and 4 overlap and their successors c, d never meet; event pairs 1-3,
   2-3 and so on do not overlap. *)
VerificationTest[
  {
    $priv["xmResolvedBranchPairRatio"][<|
      "EventRecords" -> {
        <|
          "State" -> "s",
          "Matches" -> {{1, {1}}, {1, {1, 2}}, {1, {3}}, {2, {3}}},
          "Successors" -> {"a", "b", "c", "d"}
        |>
      },
      "StatesGraph" -> Graph[{"s" -> "a", "s" -> "b", "s" -> "c", "s" -> "d", "a" -> "t", "b" -> "t"}]
    |>],
    FailureQ @ $priv["xmResolvedBranchPairRatio"][<|"StatesGraph" -> Graph[{1 -> 2}]|>]
  },
  {0.5, True},
  TestID -> "ExtendedMetrics-CriticalPairsOnHandBuiltRecords"
]


(* ::Section:: *)
(*Causal and rewrite-activity metrics*)


VerificationTest[
  With[{evolution = RewriteEventEvolution[$grow, {{1, 2}}, <|"MaxGenerations" -> 3|>]},
    {
      Values @ KeySort @ Counts[Lookup[evolution["Events"], "Generation"]],
      $metric["RewriteActivityMean", evolution],
      $metric["RewriteActivityEntropy", evolution],
      $metric["CausalMergeEventsRatio", evolution["CausalGraph"]],
      $metric["CausalDependencyEntropy", evolution["CausalGraph"]]
    }
  ],
  {{1, 2, 4}, 7/3, Log2[7.] - 10/7, 0., 0.},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-GrowthEventsPerGeneration"
]

VerificationTest[
  Lookup[
    $evaluate[
      $grow, {{1, 2}},
      {"RewriteActivityMean", "RewriteActivityEntropy", "MotifPersistence", "EdgeSurvivalRate", "LocalComponentLifetimeMax"},
      <|"EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>
    ]["Fitness"],
    {"RewriteActivityMean", "RewriteActivityEntropy", "MotifPersistence", "EdgeSurvivalRate", "LocalComponentLifetimeMax"}
  ],
  {7/3, Log2[7.] - 10/7, Missing["NoKeptMotif"], 0., 1},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-GrowthPipeline"
]

VerificationTest[
  With[{graph = Graph[{1, 2, 3, 4}, {1 -> 2, 1 -> 2, 2 -> 3, 1 -> 3, 3 -> 4}]},
    {$metric["CausalMergeEventsRatio", graph], $metric["CausalDependencyEntropy", graph]}
  ],
  {0.5, N @ Entropy[2, {3, 1, 1}]},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-CausalMultigraphCounts"
]

VerificationTest[
  {
    $metric["CausalMergeEventsRatio", Graph[{}, {}]],
    $metric["CausalDependencyEntropy", Graph[{1, 2}, {}]],
    $metric["CausalMergeEventsRatio", Graph[{1, 2}, {}]],
    $metric["RewriteActivityMean", RewriteEventEvolution[$stuck, {{1, 2}}]],
    $metric["RewriteActivityEntropy", RewriteEventEvolution[$stuck, {{1, 2}}]],
    FailureQ @ $metric["CausalMergeEventsRatio", Missing["NotRequested"]]
  },
  {Missing["NoEvents"], Missing["NoCausalEdges"], 0., Missing["NoEvents"], Missing["NoEvents"], True},
  TestID -> "ExtendedMetrics-CausalMissing"
]


(* ::Section:: *)
(*Update orders*)


$runs = <|
  "A" -> <|"Status" -> "Terminated", "FinalState" -> {{1, 2}}, "CanonicalFinalState" -> {{1, 2}},
    "CausalGraph" -> Graph[{1, 2, 3}, {1 -> 2, 1 -> 3}]|>,
  "B" -> <|"Status" -> "Terminated", "FinalState" -> {{5, 6}}, "CanonicalFinalState" -> {{1, 2}},
    "CausalGraph" -> Graph[{4, 5, 6}, {4 -> 5, 4 -> 6}]|>,
  "C" -> <|"Status" -> "EventCap", "FinalState" -> {{1, 2}, {2, 3}}, "CanonicalFinalState" -> {{1, 2}, {2, 3}},
    "CausalGraph" -> Graph[{1, 2, 3}, {1 -> 2, 2 -> 3}]|>,
  "D" -> Failure["EvolutionFailed", <||>]
|>;

VerificationTest[
  {
    $metric["UpdateOrderSensitivity", $runs],
    $metric["CausalUpdateOrderSensitivity", $runs],
    $metric["UpdateOrderTerminalOutcomeCount", $runs]
  },
  {2/3, 2/3, 1},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-UpdateOrderRunsHandBuilt"
]

VerificationTest[
  With[
    {
      m1 = Graph[{1, 2, 3}, {1 -> 2, 1 -> 2, 2 -> 3}],
      m2 = Graph[{1, 2, 3}, {1 -> 2, 2 -> 3, 2 -> 3}],
      m3 = Graph[{"a", "b", "c"}, {"b" -> "c", "a" -> "b", "a" -> "b"}]
    },
    {
      $priv["xmCausalGraphsIsomorphicQ"][m1, m2],
      $priv["xmCausalGraphsIsomorphicQ"][m1, m3],
      $priv["xmCausalSignature"][m1] === $priv["xmCausalSignature"][m3],
      $metric["CausalUpdateOrderSensitivity", <|
        1 -> <|"Status" -> "Terminated", "CanonicalFinalState" -> {}, "CausalGraph" -> m1|>,
        2 -> <|"Status" -> "Terminated", "CanonicalFinalState" -> {}, "CausalGraph" -> m2|>,
        3 -> <|"Status" -> "Terminated", "CanonicalFinalState" -> {}, "CausalGraph" -> m3|>
      |>]
    }
  ],
  {False, True, True, 2/3},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-CausalMultigraphIsomorphism"
]

VerificationTest[
  {
    $metric["UpdateOrderTerminalOutcomeCount", KeyTake[$runs, {"C", "D"}]],
    $metric["UpdateOrderSensitivity", KeyTake[$runs, {"A", "D"}]],
    $metric["CausalUpdateOrderSensitivity", KeyTake[$runs, {"A", "D"}]],
    FailureQ @ $metric["UpdateOrderSensitivity", Missing["NotRequested"]]
  },
  {Missing["NoTerminatedRuns"], 0., 0., True},
  TestID -> "ExtendedMetrics-UpdateOrderMissing"
]

VerificationTest[
  Lookup[
    $evaluate[$delete, $path3, {"UpdateOrderSensitivity", "CausalUpdateOrderSensitivity", "UpdateOrderTerminalOutcomeCount"}]["Fitness"],
    {"UpdateOrderSensitivity", "CausalUpdateOrderSensitivity", "UpdateOrderTerminalOutcomeCount"}
  ],
  {0., 0., 1},
  TestID -> "ExtendedMetrics-UpdateOrdersConfluentDeletion"
]

(* Sequential applies the two-edge deletion (one event), LeastRecent the
   one-edge deletion twice: same final state, different causal graphs. *)
VerificationTest[
  With[
    {
      fitness = $evaluate[
        $confluentSet, $path2, {"UpdateOrderSensitivity", "CausalUpdateOrderSensitivity"},
        <|"UpdateOrders" -> {"Sequential", "LeastRecent"}|>
      ]["Fitness"]
    },
    {fitness["UpdateOrderSensitivity"], fitness["CausalUpdateOrderSensitivity"]}
  ],
  {0., 1.},
  TestID -> "ExtendedMetrics-StateVersusCausalSensitivity"
]


(* ::Section:: *)
(*Local persistence*)


VerificationTest[
  With[{evolution = RewriteEventEvolution[$delete, $pairs3, <||>, "UpdateOrder" -> "Sequential"]},
    {
      evolution["LiveEdges"],
      $metric["LocalComponentLifetimeMean", evolution],
      $metric["LocalComponentLifetimeMax", evolution],
      $metric["MotifPersistence", evolution],
      $metric["EdgeSurvivalRate", evolution],
      $metric["MotifPersistence", evolution, <|"Motif" -> {{motifA, motifB}}|>],
      $metric["MotifPersistence", evolution, <|"Motif" -> $pathMotif|>]
    }
  ],
  {{{1, 2, 3}, {2, 3}, {3}, {}}, 2., 3, Missing["NoKeptMotif"], 7/18, 7/18, Missing["NoOccurrences"]},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-PersistenceOfSequentialDeletion"
]

VerificationTest[
  With[{evolution = RewriteEventEvolution[$delete, $path3, <||>, "UpdateOrder" -> "Sequential"]},
    {
      $metric["MotifPersistence", evolution, <|"Motif" -> $pathMotif|>],
      $metric["LocalComponentLifetimeMean", evolution],
      $metric["LocalComponentLifetimeMax", evolution]
    }
  ],
  {0.25, 1., 1},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-PathMotifPersistence"
]

VerificationTest[
  Lookup[
    $evaluate[
      $delete, $pairs3, {"LocalComponentLifetimeMean", "LocalComponentLifetimeMax", "MotifPersistence", "EdgeSurvivalRate"},
      <|"UpdateOrder" -> "Sequential"|>
    ]["Fitness"],
    {"LocalComponentLifetimeMean", "LocalComponentLifetimeMax", "MotifPersistence", "EdgeSurvivalRate"}
  ],
  {2., 3, Missing["NoKeptMotif"], 7/18},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-PersistencePipeline"
]

VerificationTest[
  With[{evolution = RewriteEventEvolution[$delete, {}]},
    {
      $metric["LocalComponentLifetimeMean", evolution],
      $metric["LocalComponentLifetimeMax", evolution],
      $metric["MotifPersistence", evolution],
      $metric["MotifPersistence", evolution, <|"Motif" -> {{motifA, motifB}}|>],
      $metric["EdgeSurvivalRate", evolution],
      $metric["HubPersistence", evolution],
      FailureQ @ $metric["MotifPersistence", evolution, <|"Motif" -> "notAMotif"|>],
      FailureQ @ $metric["MotifPersistence", Missing["NotRequested"]],
      FailureQ @ $metric["HubPersistence", Missing["NotRequested"]],
      FailureQ @ $metric["EdgeSurvivalRate", Missing["NotRequested"]]
    }
  ],
  {
    Missing["NoComponents"], Missing["NoComponents"], Missing["NoKeptMotif"], Missing["NoStepPairs"],
    Missing["NoStepPairs"], Missing["NoStepPairs"], True, True, True, True
  },
  TestID -> "ExtendedMetrics-PersistenceMissing"
]


(* The rule's kept motif is followed through the rewrites that write it back.
   The local-stability recipe keeps a self-loop that every event consumes and
   writes back: the motif persists although most edges do not (the edge
   survival rate is (0 + 1/3 + 2/4 + 3/5) / 4 = 43/120), and every self-loop
   edge belongs to one lineage. *)
$keepLoop = {{1, 2}, {2, 2}} -> {{1, 3}, {3, 2}, {2, 2}};

VerificationTest[
  With[{evolution = RewriteEventEvolution[$keepLoop, {{1, 2}, {2, 2}}, <|"MaxEvents" -> 4|>, "UpdateOrder" -> "Sequential"]},
    {
      $priv["xmKeptMotifs"][$keepLoop],
      evolution["Rule"] === $keepLoop,
      Length[evolution["LiveEdges"]],
      $metric["MotifPersistence", evolution],
      $metric["EdgeSurvivalRate", evolution],
      With[{lineage = $priv["xmEdgeLineages"][evolution], records = evolution["EdgeRecords"]},
        Length @ Union[Lookup[lineage, #, #] & /@ Select[Keys[records], MatchQ[records[#]["Edge"], {v_, v_}] &]]
      ]
    }
  ],
  {{{{2, 2}}}, True, 5, 1., 43/120, 1},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-KeptMotifFollowsWriteBacks"
]

(* Kept motifs come from the rule: left-hand edges written back unchanged, in
   connected pieces, over every member of a rule set, isomorphic pieces once. *)
VerificationTest[
  {
    $priv["xmKeptMotifs"][{{1, 2}, {2, 3}} -> {{1, 3}}],
    Sort /@ $priv["xmKeptMotifs"][{{1, 2}, {2, 3}} -> {{2, 1}, {3, 2}, {3, 4}}],
    $priv["xmKeptMotifs"][{{{1, 2}, {2, 3}} -> {{1, 3}}, {{1, 1}} -> {{1, 1}, {1, 2}}}],
    Length @ $priv["xmKeptMotifs"][{{1, 1}, {2, 2}} -> {{1, 1}, {2, 2}, {1, 2}}],
    $metric["MotifPersistence", RewriteEventEvolution[$contract, $path3]]
  },
  {{}, {{{1, 2}, {2, 3}}}, {{{1, 1}}}, 1, Missing["NoKeptMotif"]},
  TestID -> "ExtendedMetrics-KeptMotifFromRule"
]

(* Writing an edge back reversed keeps it in the unordered universe, where
   slot order carries no meaning, and replaces it in the ordered universe. *)
$reverseKeep = {{1, 2}, {2, 3}} -> {{2, 1}, {3, 2}, {3, 4}};

VerificationTest[
  Lookup[#["Fitness"], "MotifPersistence"] & /@ {
    $evaluate[$reverseKeep, $path3, {"MotifPersistence"},
      <|"UpdateOrder" -> "Sequential", "EvolutionLimits" -> <|"MaxEvents" -> 3|>|>],
    $evaluate[$reverseKeep, $path3, {"MotifPersistence"},
      <|"UpdateOrder" -> "Sequential", "EvolutionLimits" -> <|"MaxEvents" -> 3|>, "EdgeSymmetry" -> "Ordered"|>]
  },
  {1., Missing["NoKeptMotif"]},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-KeptMotifUniverse"
]

(* Hubs are followed by their vertex: a star that keeps growing keeps its
   hub, a star that is rewritten away loses it. *)
VerificationTest[
  {
    $metric["HubPersistence",
      RewriteEventEvolution[{{1, 2}} -> {{1, 2}, {1, 3}}, {{1, 2}, {1, 3}, {1, 4}}, <|"MaxEvents" -> 3|>, "UpdateOrder" -> "Sequential"]],
    $metric["HubPersistence", RewriteEventEvolution[{{1, 2}, {1, 3}, {1, 4}} -> {{2, 3}, {3, 4}}, {{1, 2}, {1, 3}, {1, 4}}]],
    $metric["HubPersistence", RewriteEventEvolution[$delete, $path3, <||>, "UpdateOrder" -> "Sequential"]],
    $metric["HubPersistence", RewriteEventEvolution[$delete, $path3, <||>, "UpdateOrder" -> "Sequential"], <|"HubDegree" -> 2|>],
    FailureQ @ $metric["HubPersistence", RewriteEventEvolution[$delete, $path3], <|"HubDegree" -> 0|>],
    $registry["HubPersistence"]["Parameters"]
  },
  {1., 0., Missing["NoHubs"], 0.25, True, <|"HubDegree" -> 3|>},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-HubPersistence"
]


(* ::Section:: *)
(*Branchial graphs*)


VerificationTest[
  With[{graphs = BranchialGraphs[CanonicalMultiwayEvolution[$delete, $path3]]},
    {Keys[graphs], VertexCount /@ Values[graphs], EdgeCount /@ Values[graphs], VertexList[graphs[3]]}
  ],
  {{0, 1, 2, 3}, {1, 2, 1, 1}, {0, 1, 0, 0}, {{}}},
  TestID -> "ExtendedMetrics-BranchialGraphsOfDeletion"
]

VerificationTest[
  With[{evolution = CanonicalMultiwayEvolution[$delete, $path3]},
    {
      EdgeCount @ BranchialGraph[evolution, 1],
      BranchialGraph[evolution, 7],
      FailureQ @ BranchialGraphs[42],
      FailureQ @ BranchialGraph[42, 1],
      Keys @ BranchialGraphs[evolution, 1],
      Map[EdgeList, BranchialGraphs[MultiwayEvolutionGraph[evolution]]] === Map[EdgeList, BranchialGraphs[evolution]]
    }
  ],
  {1, Missing["NoSuchLayer", 7], True, True, {0, 1}, True},
  TestID -> "ExtendedMetrics-BranchialGraphAccessors"
]

$handEvolution = <|
  "StatesGraph" -> Graph[{"r" -> "p", "r" -> "q", "p" -> "b", "p" -> "c", "q" -> "c", "q" -> "d"}],
  "Generations" -> {{"r"}, {"p", "q"}, {"b", "c", "d"}},
  "EvolutionLimits" -> <|"MaxGenerations" -> 5|>
|>;

VerificationTest[
  With[{graphs = BranchialGraphs[$handEvolution]},
    {
      $metric["BranchialMeanDegree", graphs],
      $metric["MeanBranchialDistance", graphs],
      $metric["BranchialMeanDegree", graphs, <|"Slice" -> 1|>],
      $metric["MeanBranchialDistance", graphs, <|"Slice" -> 1|>],
      $metric["BranchialMeanDegree", graphs, <|"Slice" -> 0|>],
      $metric["MeanBranchialDistance", graphs, <|"Slice" -> 0|>],
      $metric["MeanBranchialDistance", graphs, <|"Slice" -> 9|>]
    }
  ],
  {4/3, 4/3, 1., 1., 0., Missing["FewerThanTwoStates"], Missing["NoSuchSlice", 9]},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-BranchialSlices"
]

VerificationTest[
  With[
    {
      graphs = BranchialGraphs[<|
        "StatesGraph" -> Graph[{"r" -> "p", "r" -> "q", "p" -> "b", "q" -> "d"}],
        "Generations" -> {{"r"}, {"p", "q"}, {"b", "d"}},
        "EvolutionLimits" -> <|"MaxGenerations" -> 5|>
      |>]
    },
    {
      $metric["MeanBranchialDistance", graphs, <|"Slice" -> 2|>],
      $metric["BranchialMeanDegree", graphs, <|"Slice" -> 2|>],
      $metric["MeanBranchialDistance", graphs]
    }
  ],
  {Missing["NoConnectedPairs"], 0., 1.},
  SameTest -> $close,
  TestID -> "ExtendedMetrics-BranchialNoConnectedPairs"
]

VerificationTest[
  {
    Lookup[
      $evaluate[$delete, $path3, {"BranchialMeanDegree", "MeanBranchialDistance"}]["Fitness"],
      {"BranchialMeanDegree", "MeanBranchialDistance"}
    ],
    Lookup[
      $evaluate[
        $delete, $path3, {"BranchialMeanDegree", "MeanBranchialDistance"},
        <|"MetricOverrides" -> <|
          "BranchialMeanDegree" -> <|"Parameters" -> <|"Slice" -> 0|>|>,
          "MeanBranchialDistance" -> <|"Parameters" -> <|"Slice" -> 0|>|>
        |>|>
      ]["Fitness"],
      {"BranchialMeanDegree", "MeanBranchialDistance"}
    ]
  },
  {{1., 1.}, {0., Missing["FewerThanTwoStates"]}},
  TestID -> "ExtendedMetrics-BranchialPipeline"
]


(* ::Section:: *)
(*Classification*)


VerificationTest[
  With[{criteria = DefaultClassificationCriteria[]},
    {
      Keys[criteria],
      criteria["Status"],
      Select[
        DefaultClassificationCriteria[<|"TargetDimension" -> 3.|>]["SpaceLike"]["AllOf"],
        #["Metric"] === "EffectiveDimensionEstimate" &
      ][[1, "Value"]],
      FailureQ @ DefaultClassificationCriteria[<|"NoSuchThreshold" -> 1|>],
      Lookup[criteria["CausalInvariant"]["AnyOf"][[2]], "Metric"]
    }
  ],
  {
    {"Status", "RichTerminalStates", "SpaceLike", "Homogeneous", "LocallyStable", "CausalInvariant"},
    "Provisional (owner review pending)",
    3.,
    True,
    {"UpdateOrderTerminalOutcomeCount", "UpdateOrderSensitivity"}
  },
  TestID -> "ExtendedMetrics-DefaultCriteria"
]

VerificationTest[
  Module[{config, candidate, result},
    config = ValidateEvolutionConfiguration[<|"FitnessMetrics" -> {"MultiwayStateCount"}|>];
    candidate = EvaluateCandidate[<|"Rule" -> $contract, "InitialState" -> $cycle4|>, config];
    result = ClassifyCandidate[candidate, {"CausalInvariant", "RichTerminalStates"}, config];
    {
      Lookup[Values[result], "Satisfied"],
      Lookup[Values[result], "CriteriaStatus"],
      result["CausalInvariant"]["Evidence"]["CausalInvariantWithinCapQ"],
      result["RichTerminalStates"]["Evidence"]["NonIsomorphicTerminalStateCount"],
      AllTrue[Lookup[Values[result], "Claim"], StringContainsQ[#, "within the explored limits", IgnoreCase -> True] &],
      SubsetQ[Keys[result["CausalInvariant"]], {"Label", "Satisfied", "Evidence", "Criteria", "CriteriaStatus", "Claim"}]
    }
  ],
  {{True, False}, {"Provisional", "Provisional"}, True, 1, True, True},
  TestID -> "ExtendedMetrics-ClassifyEvaluatesMissingMetrics"
]

VerificationTest[
  With[{result = ClassifyCandidate[<|"Rule" -> $confluentSet, "InitialState" -> $path2|>, {"SpaceLike"}]["SpaceLike"]},
    {
      result["Satisfied"],
      result["Evidence"]["EffectiveDimensionEstimate"],
      result["Evidence"]["LargestComponentRatio"],
      StringContainsQ[result["Claim"], "undetermined"]
    }
  ],
  {Undetermined, Missing["InsufficientStructure"], 1., True},
  TestID -> "ExtendedMetrics-ClassifyUndetermined"
]

VerificationTest[
  {
    ClassifyCandidate[
      <|"Status" -> "Halted", "Fitness" -> <|"DimensionVariance" -> 0.05, "VertexDegreeVariance" -> 0.5|>|>,
      {"Homogeneous"}
    ]["Homogeneous"]["Satisfied"],
    ClassifyCandidate[
      <|"Status" -> "Halted", "Fitness" -> <|"DimensionVariance" -> 0.05, "VertexDegreeVariance" -> 2.|>|>,
      {"Homogeneous"}
    ]["Homogeneous"]["Satisfied"],
    Lookup[
      ClassifyCandidate[<|"Status" -> "Halted", "Fitness" -> <|"DimensionVariance" -> 0.05|>|>, {"Homogeneous"}]["Homogeneous"],
      {"Satisfied", "Evidence"}
    ]
  },
  {True, False, {Undetermined, <|"DimensionVariance" -> 0.05, "VertexDegreeVariance" -> Missing["NotEvaluated"]|>}},
  TestID -> "ExtendedMetrics-ClassifyReusesFitness"
]

VerificationTest[
  {
    Lookup[
      ClassifyCandidate[
        <|"Status" -> "GenerationCap", "Fitness" -> <|"MultiwayStateCount" -> 12|>|>,
        <|"Large" -> <|"AllOf" -> {<|"Metric" -> "MultiwayStateCount", "Test" -> "AtLeast", "Value" -> 10|>}|>|>
      ]["Large"],
      {"Satisfied", "CriteriaStatus"}
    ],
    Lookup[
      Values @ ClassifyCandidate[
        <|
          "Status" -> "Halted",
          "Fitness" -> <|
            "EffectiveDimensionEstimate" -> 3.1, "DimensionVariance" -> 0.05,
            "LargestComponentRatio" -> 1., "VertexDegreeVariance" -> 0.5
          |>
        |>,
        KeyTake[DefaultClassificationCriteria[<|"TargetDimension" -> 3.|>], {"Status", "SpaceLike", "Homogeneous"}]
      ],
      {"Satisfied", "CriteriaStatus"}
    ]
  },
  {{True, "UserSupplied"}, {{True, "UserSupplied"}, {True, "Provisional"}}},
  TestID -> "ExtendedMetrics-ClassifyCriteriaStatus"
]

VerificationTest[
  {
    FailureQ @ ClassifyCandidate[<||>, <|"X" -> <|"AllOf" -> {<|"Metric" -> "Foo"|>}|>|>],
    FailureQ @ ClassifyCandidate[<||>, {"NoSuchLabel"}],
    FailureQ @ ClassifyCandidate[<||>, Automatic, <|"EdgeSymmetry" -> "Bogus"|>],
    FailureQ @ ClassifyCandidate[42]
  },
  {True, True, True, True},
  TestID -> "ExtendedMetrics-ClassifyInvalidInput"
]

VerificationTest[
  With[{claims = Lookup[Values @ ClassifyCandidate[<|"Rule" -> $delete, "InitialState" -> $path3|>], "Claim"]},
    {
      Length[claims],
      AllTrue[
        claims,
        StringStartsQ[#, "Within the explored limits"] &&
          StringFreeQ[#, {"physic", "spacetime", "space-time", "universe", "particle"}, IgnoreCase -> True] &
      ]
    }
  ],
  {5, True},
  TestID -> "ExtendedMetrics-ClaimsStayWithinExploredLimits"
]


(* ::Section:: *)
(*Every metric in a full evaluation*)


VerificationTest[
  Map[
    Function[system,
      With[{candidate = $evaluate[system[[1]], system[[2]], $extendedMetrics, system[[3]]]},
        {
          candidate["ValidQ"],
          SubsetQ[Keys[candidate["Fitness"]], $extendedMetrics],
          NoneTrue[Values[candidate["Fitness"]], FailureQ]
        }
      ]
    ],
    {
      {$branchGrow, {{1, 2}}, <|"EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>},
      {$branchGrow, {{1, 2}}, <|"EdgeSymmetry" -> "Ordered", "EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>},
      {$confluentSet, $path2, <||>},
      {$contract, $cycle4, <||>},
      {$stuck, {{1, 2}}, <||>}
    }
  ],
  ConstantArray[{True, True, True}, 5],
  TestID -> "ExtendedMetrics-EveryMetricEvaluates"
]
