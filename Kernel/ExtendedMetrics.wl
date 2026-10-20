(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* Extended metric families for the strategy catalog, registered in the
   fitness-metric registry as "Diagnostic" metrics (promote one with the
   MetricOverrides option, for example <|"Stage" -> "Objective"|>):

     structural            -- over the canonical explored states and the
                              verified terminal states;
     branching/confluence  -- on the canonical states graph and the raw
                              rewrite events of the breadth-first search;
     causal and activity   -- on the event-level evolution (configured
                              UpdateOrder) and its causal multigraph;
     update orders         -- over the runs of the configured UpdateOrders;
     local persistence     -- edge-ID components and motif occurrences of the
                              event-level evolution;
     branchial             -- the BranchialGraphs artifact of the
                              generation-unrolled evolution graph;

   plus quantitative classification criteria (ClassifyCandidate).

   Missing-value policy: an undefined value is Missing["Reason"], never a
   silent 0; every Description states its aggregation and its Missing case.
   A metric whose input artifact is unavailable returns a Failure, which the
   evaluator reports as an invalid metric value. Private helpers carry the
   prefix xm so they cannot collide with other modules loaded into the same
   context. *)


(* ::Section:: *)
(*Generic helpers*)


(* Mean (maximum) of the numeric entries of a list; the given Missing when
   there are none. Non-numeric entries are undefined per-item values. *)
xmMean[values_List, missing_] :=
  With[{numeric = Select[values, NumericQ]},
    If[numeric === {}, missing, N @ Mean[numeric]]
  ]

xmMax[values_List, missing_] :=
  With[{numeric = Select[values, NumericQ]},
    If[numeric === {}, missing, Max[numeric]]
  ]


xmUnavailable[input_String, value_] :=
  Failure[
    "MetricInputUnavailable",
    <|
      "Message" -> "The metric input is not available.",
      "Input" -> input,
      "Value" -> Short[value]
    |>
  ]


(* ::Section:: *)
(*Structural metrics*)


(* Connected components of a hyperedge list as lists of edge positions:
   edges sharing a vertex are joined, transitively (the components of the
   spatial projection, restricted to edges); an edge without vertices is its
   own component. Used for the edge-ID components of local persistence. *)
xmEdgeComponents[edges_List] := Module[{incidence, links},
  If[edges === {}, Return[{}]];
  incidence = GroupBy[
    Catenate @ MapIndexed[
      Function[{edge, position}, {#, First[position]} & /@ DeleteDuplicates[edge]],
      edges
    ],
    First -> Last
  ];
  links = Catenate[UndirectedEdge @@@ Partition[#, 2, 1] & /@ Values[incidence]];
  ConnectedComponents @ Graph[Range @ Length[edges], links]
]


(* Vertex counts of the connected components of a state's spatial
   projection (ToSpatialGraph, the geometry policy, as in ComponentMetrics);
   {} for a state whose projection has no vertex. *)
xmComponentVertexCounts[state_List] :=
  If[Flatten[state] === {}, {}, Length /@ ConnectedComponents[ToSpatialGraph[state]]]


xmLargestComponentRatio[states_List] :=
  xmMean[
    Replace[
      xmComponentVertexCounts /@ states,
      {{} -> Missing["NoVertices"], sizes_List :> N[Max[sizes] / Total[sizes]]},
      {1}
    ],
    Missing["NoVertices"]
  ]

xmNumberOfConnectedComponents[states_List] :=
  xmMax[Length[xmComponentVertexCounts[#]] & /@ states, Missing["NoStates"]]

xmLargestConnectedComponentSize[states_List] :=
  xmMax[
    Replace[xmComponentVertexCounts /@ states, {{} -> Missing["NoVertices"], sizes_List :> Max[sizes]}, {1}],
    Missing["NoVertices"]
  ]


(* Mean of the per-state dimension estimates over the states that have one
   (EffectiveDimensionEstimate / DimensionVariance of a single state). *)
xmMeanDimensionEstimate[states_List] :=
  xmMean[EffectiveDimensionEstimate /@ states, Missing["InsufficientStructure"]]

xmMeanDimensionVariance[states_List] :=
  xmMean[DimensionVariance /@ states, Missing["InsufficientStructure"]]


(* Incidence-degree statistics of one state (DegreeMetrics conventions: a
   one-vertex state has variance 0.); Missing["NoVertices"] for a state
   without vertices. *)
xmDegreeStatistic[state_List, key_String] :=
  With[{degrees = hypergraphIncidenceDegreeValues[state]},
    If[degrees === {}, Missing["NoVertices"], degreeMetricsFromValues[degrees][key]]
  ]

xmMaxVertexDegree[states_List] :=
  xmMax[xmDegreeStatistic[#, "MaxVertexDegree"] & /@ states, Missing["NoVertices"]]

xmMeanVertexDegreeVariance[states_List] :=
  xmMean[xmDegreeStatistic[#, "VertexDegreeVariance"] & /@ states, Missing["NoVertices"]]

xmMaxVertexDegreeVariance[states_List] :=
  xmMax[xmDegreeStatistic[#, "VertexDegreeVariance"] & /@ states, Missing["NoVertices"]]


xmMeanEdgeToVertexRatio[states_List] :=
  xmMean[
    With[{vertices = HypergraphVertexCount[#]},
      If[vertices === 0, Missing["NoVertices"], N[HypergraphEdgeCount[#] / vertices]]
    ] & /@ states,
    Missing["NoVertices"]
  ]


(* Means over the verified terminal states. *)
xmTerminalMean[states_List, f_] :=
  If[states === {}, Missing["NoTerminalStates"], N @ Mean[f /@ states]]

xmTerminalDegreeStatistic[state_List, key_String] :=
  degreeMetricsFromValues[hypergraphIncidenceDegreeValues[state]][key]


(* ::Section:: *)
(*Branching and confluence on the states graph*)


(* BranchingUncertainty of the canonical states graph; its documented zero
   values when no explored state has a successor (an edgeless graph is not
   a directed graph). *)
xmBranching[graph_Graph, key_String] :=
  If[EdgeCount[graph] === 0, 0., BranchingUncertainty[graph][key]]

xmBranching[other_, _] := xmUnavailable["StatesGraph", other]


(* Branch pairs: unordered pairs of distinct successors of one explored
   state. *)
xmBranchPairs[graph_Graph] :=
  Catenate[
    Subsets[#, {2}] & /@ Values @ GroupBy[EdgeList[graph], First -> Last, DeleteDuplicates]
  ]


(* Future cones in the explored states graph: state -> vertex indices of the
   state and of every state reachable from it. A state that is not a vertex
   of the graph has an empty cone (nothing is known about its future). *)
xmFutureCones[graph_Graph, states_List] := Module[{indexGraph, index},
  indexGraph = IndexGraph[graph];
  index = AssociationThread[VertexList[graph], Range @ VertexCount[graph]];
  AssociationMap[
    Function[state,
      With[{i = Lookup[index, Key[state], None]},
        If[i === None, {}, Union[{i}, VertexOutComponent[indexGraph, i]]]
      ]
    ],
    DeleteDuplicates[states]
  ]
]


(* Reconvergence flag of every branch pair: do the future cones of its two
   successors intersect inside the explored states graph? *)
xmPairReconvergence[graph_Graph, pairs_List] :=
  If[
    pairs === {},
    {},
    With[{cones = xmFutureCones[graph, Catenate[pairs]]},
      IntersectingQ[cones[#[[1]]], cones[#[[2]]]] & /@ pairs
    ]
  ]


xmReconvergenceRatio[graph_Graph] :=
  With[{flags = xmPairReconvergence[graph, xmBranchPairs[graph]]},
    If[flags === {}, Missing["NoBranchPairs"], N @ Mean[Boole[flags]]]
  ]

xmReconvergenceRatio[other_] := xmUnavailable["StatesGraph", other]


(* Critical pairs of the recorded raw events: two raw events at one explored
   state whose matched edge positions intersect and whose canonical
   successors differ, as {successor1, successor2}. *)
xmCriticalPairs[records_List] :=
  Catenate @ Map[
    Function[record,
      With[
        {
          positions = Last /@ record["Matches"],
          successors = record["Successors"]
        },
        {successors[[#[[1]]]], successors[[#[[2]]]]} & /@ Select[
          Subsets[Range @ Length[positions], {2}],
          IntersectingQ[positions[[#[[1]]]], positions[[#[[2]]]]] &&
            successors[[#[[1]]]] =!= successors[[#[[2]]]] &
        ]
      ]
    ],
    records
  ]


xmResolvedBranchPairRatio[context_Association] := Module[{records, pairs, flags},
  records = Lookup[context, "EventRecords", Missing["NotRequested"]];
  If[!ListQ[records], Return @ xmUnavailable["EventRecords", records]];
  pairs = xmCriticalPairs[records];
  If[pairs === {}, Return @ Missing["NoCriticalPairs"]];
  flags = xmPairReconvergence[context["StatesGraph"], pairs];
  N @ Mean[Boole[flags]]
]


(* Halted (the explored states graph is the whole acyclic reachable canonical
   state space) and locally confluent (every branch pair reconverges), hence
   confluent with a unique terminal state by Newman's lemma. *)
xmCausalInvariantWithinCapQ[context_Association] :=
  context["Status"] === "Halted" &&
    AllTrue[xmPairReconvergence[context["StatesGraph"], xmBranchPairs[context["StatesGraph"]]], TrueQ]


(* ::Section:: *)
(*Causal and rewrite-activity metrics*)


xmCausalMergeEventsRatio[graph_Graph] :=
  If[
    VertexCount[graph] === 0,
    Missing["NoEvents"],
    N[Count[VertexInDegree[graph], degree_ /; degree >= 2] / VertexCount[graph]]
  ]

xmCausalMergeEventsRatio[other_] := xmUnavailable["CausalGraph", other]


xmCausalDependencyEntropy[graph_Graph] :=
  If[EdgeCount[graph] === 0, Missing["NoCausalEdges"], CausalDependencyEntropy[graph]]

xmCausalDependencyEntropy[other_] := xmUnavailable["CausalGraph", other]


(* Event counts of generations 1 .. largest event generation (a generation
   without events counts 0); {} when no event occurred. *)
xmGenerationCounts[evolution_Association] :=
  With[{generations = Lookup[Lookup[evolution, "Events", {}], "Generation", {}]},
    If[generations === {}, {}, Lookup[Counts[generations], Range @ Max[generations], 0]]
  ]


xmRewriteActivityMean[evolution_Association] :=
  With[{counts = xmGenerationCounts[evolution]},
    If[counts === {}, Missing["NoEvents"], N @ Mean[counts]]
  ]

xmRewriteActivityMean[other_] := xmUnavailable["EventEvolution", other]


(* The counts per generation are treated as a distribution. *)
xmRewriteActivityEntropy[evolution_Association] :=
  With[{counts = xmGenerationCounts[evolution]},
    If[
      counts === {},
      Missing["NoEvents"],
      With[{p = Select[N[counts / Total[counts]], Positive]},
        Chop[-Total[p Log2[p]]] + 0.
      ]
    ]
  ]

xmRewriteActivityEntropy[other_] := xmUnavailable["EventEvolution", other]


(* ::Section:: *)
(*Update-order metrics*)


(* Runs of the UpdateOrderRuns artifact that produced an evolution: neither
   a Failure nor Status "Invalid". *)
xmValidRuns[runs_Association] :=
  Select[Values[runs], AssociationQ[#] && Lookup[#, "Status", "Invalid"] =!= "Invalid" &]


xmCanonicalFinalState[run_Association] :=
  If[
    KeyExistsQ[run, "CanonicalFinalState"],
    run["CanonicalFinalState"],
    CanonicalStateForm[run["FinalState"]]
  ]


xmUpdateOrderSensitivity[runs_Association] :=
  With[{valid = xmValidRuns[runs]},
    If[
      Length[valid] < 2,
      0.,
      N @ Mean[Boole[UnsameQ @@@ Subsets[xmCanonicalFinalState /@ valid, {2}]]]
    ]
  ]

xmUpdateOrderSensitivity[other_] := xmUnavailable["UpdateOrderRuns", other]


(* Causal graphs are directed multigraphs, which IsomorphicGraphQ does not
   support (IsomorphicGraphQ::ngen). A directed multigraph is an
   ordered-universe multiset hypergraph (one unary edge per vertex keeps
   isolated vertices, one binary edge per causal edge keeps multiplicities),
   so its exact canonical labelling is a complete invariant: two causal
   graphs are isomorphic iff their signatures are equal. The labelling can
   be exponential on highly symmetric graphs (a 255-event binary causal tree
   did not finish in minutes), so it runs under a time limit; $Failed past
   the time limit or the labelling's leaf limit. *)
$xmSignatureTimeLimit = 10.;

xmCausalSignature[graph_Graph] :=
  TimeConstrained[
    Block[{$EdgeSymmetry = "Ordered"},
      exactCanonicalSides[{Join[List /@ VertexList[graph], List @@@ EdgeList[graph]]}]
    ],
    $xmSignatureTimeLimit,
    $Failed
  ]


(* Cheap necessary conditions for isomorphism, compared first: sizes, the
   multiset of (in-degree, out-degree) pairs and the edge multiplicities.
   Equal invariants imply that both graphs are simple or both are
   multigraphs. *)
xmCausalInvariants[graph_Graph] :=
  {
    VertexCount[graph],
    EdgeCount[graph],
    Sort @ Transpose[{VertexInDegree[graph], VertexOutDegree[graph]}],
    Sort @ Values @ Counts @ EdgeList[graph]
  }


(* Isomorphism of causal graphs: True, False, or Missing["CanonicalFormLimit"].
   Different invariants decide False; simple digraphs are decided exactly
   by IsomorphicGraphQ (the signature gives the same answer, much more
   slowly); multigraphs by the exact signature, computed with the given
   (possibly memoizing) signature function. *)
xmCausalGraphsIsomorphicQ[graph1_Graph, graph2_Graph] :=
  xmCausalGraphsIsomorphicQ[graph1, graph2, xmCausalSignature]

xmCausalGraphsIsomorphicQ[graph1_Graph, graph2_Graph, signature_] :=
  Which[
    xmCausalInvariants[graph1] =!= xmCausalInvariants[graph2],
    False,

    !MultigraphQ[graph1] && !MultigraphQ[graph2],
    TrueQ @ IsomorphicGraphQ[graph1, graph2],

    True,
    With[{signature1 = signature[graph1], signature2 = signature[graph2]},
      If[
        signature1 === $Failed || signature2 === $Failed,
        Missing["CanonicalFormLimit"],
        signature1 === signature2
      ]
    ]
  ]


xmCausalUpdateOrderSensitivity[runs_Association] := Module[{graphs, signature, outcomes},
  graphs = Lookup[xmValidRuns[runs], "CausalGraph", Missing["NotAvailable"]];
  If[Length[graphs] < 2, Return[0.]];
  If[!AllTrue[graphs, GraphQ], Return @ xmUnavailable["CausalGraph", graphs]];
  signature[graph_] := signature[graph] = xmCausalSignature[graph];
  outcomes = xmCausalGraphsIsomorphicQ[#[[1]], #[[2]], signature] & /@ Subsets[graphs, {2}];
  If[
    MemberQ[outcomes, _Missing],
    Missing["CanonicalFormLimit"],
    N @ Mean[Boole[Not /@ outcomes]]
  ]
]

xmCausalUpdateOrderSensitivity[other_] := xmUnavailable["UpdateOrderRuns", other]


xmUpdateOrderTerminalOutcomeCount[runs_Association] :=
  With[{terminated = Select[xmValidRuns[runs], #["Status"] === "Terminated" &]},
    If[
      terminated === {},
      Missing["NoTerminatedRuns"],
      Length @ DeleteDuplicates[xmCanonicalFinalState /@ terminated]
    ]
  ]

xmUpdateOrderTerminalOutcomeCount[other_] := xmUnavailable["UpdateOrderRuns", other]


(* ::Section:: *)
(*Local persistence*)


(* The local components of every recorded step: connected components of the
   live edges (spatial projection), each identified by its sorted edge IDs.
   "States" and "LiveEdges" of an event evolution are aligned edge by edge. *)
xmLocalComponents[evolution_Association] :=
  MapThread[
    Function[{state, live}, Sort[Sort[live[[#]]] & /@ xmEdgeComponents[state]]],
    {evolution["States"], evolution["LiveEdges"]}
  ]


(* Lengths of all component occurrences: maximal runs of consecutive steps
   in which one edge-ID set is exactly a component. Runs still present at
   the last recorded step are counted as observed. *)
xmComponentLifetimes[evolution_Association] := Module[{occurrences},
  occurrences = GroupBy[
    Catenate @ MapIndexed[
      Function[{components, position}, {#, First[position]} & /@ components],
      xmLocalComponents[evolution]
    ],
    First -> Last
  ];
  Catenate[Function[steps, Length /@ Split[Sort[steps], #2 === #1 + 1 &]] /@ Values[occurrences]]
]


xmLocalComponentLifetimeMean[evolution_Association] :=
  With[{lifetimes = xmComponentLifetimes[evolution]},
    If[lifetimes === {}, Missing["NoComponents"], N @ Mean[lifetimes]]
  ]

xmLocalComponentLifetimeMean[other_] := xmUnavailable["EventEvolution", other]


xmLocalComponentLifetimeMax[evolution_Association] :=
  With[{lifetimes = xmComponentLifetimes[evolution]},
    If[lifetimes === {}, Missing["NoComponents"], Max[lifetimes]]
  ]

xmLocalComponentLifetimeMax[other_] := xmUnavailable["EventEvolution", other]


xmValidMotifQ[motif_] := motif === Automatic || (hypergraphStateQ[motif] && motif =!= {})


(* Edge identity in the active universe: slot order is ignored in the
   unordered universe and reduced to the slot-symmetry orbit in the declared
   universe (the catalog operators' edge keys). *)
xmEdgeKey[edge_List] :=
  Switch[
    $EdgeSymmetry,
    "Unordered", Sort[edge],
    "Declared", declaredEdgeRepresentative[edge],
    _, edge
  ]


(* Edge lineages through the rewrite events. An event that consumes an edge
   and produces an edge with the same key (the rule writes the edge back
   unchanged, as part of the rewrite's interface) continues the consumed
   edge's lineage; every other produced edge starts a lineage of its own.
   Each consumed edge continues at most once, and the events of one step
   consume disjoint edges, so a lineage has at most one live edge at a time.
   Gives edge ID -> lineage ID (the ID of the lineage's first edge) for the
   edges that continue a lineage; every other edge is its own lineage. *)
xmEdgeLineages[evolution_Association] := Module[
  {records = evolution["EdgeRecords"], lineage = <||>},
  Scan[
    Function[event,
      Module[{pool = {#, xmEdgeKey[records[#]["Edge"]]} & /@ event["Inputs"], position},
        Scan[
          Function[output,
            position = FirstPosition[
              pool[[All, 2]], Verbatim[xmEdgeKey[records[output]["Edge"]]], None, {1}, Heads -> False
            ];
            If[
              position =!= None,
              lineage[output] = Lookup[lineage, pool[[First[position], 1]], pool[[First[position], 1]]];
              pool = Delete[pool, position]
            ]
          ],
          event["Outputs"]
        ]
      ]
    ],
    SortBy[evolution["Events"], #["EventID"] &]
  ];
  lineage
]


(* Occurrences of a motif pattern at every recorded step, as duplicate-free
   lists of sorted edge-ID sets: the pattern is matched as a rule left-hand
   side with the rule-matching machinery of the active universe (every match
   of its edges, whatever the variable binding). *)
xmMotifOccurrences[evolution_Association, motif_List] := Module[{compiled},
  compiled = applicationRuleSet[motif -> motif];
  Catch[
    MapThread[
      Function[{state, live},
        With[{raw = rawRewriteEvents[compiled, state]},
          If[
            raw === $Failed,
            Throw[
              Failure["MotifMatchingFailed", <|"Message" -> "Matching the motif failed.", "Motif" -> motif|>],
              "xmMotif"
            ]
          ];
          DeleteDuplicates[Sort[live[[Flatten[#["MatchEdgePositions"]]]]] & /@ raw]
        ]
      ],
      {evolution["States"], evolution["LiveEdges"]}
    ],
    "xmMotif"
  ]
]


(* The edges a rule keeps: its left-hand edges that the right-hand side
   writes back unchanged (same key in the active universe; each right-hand
   edge used once). *)
xmKeptEdges[lhs_List -> rhs_List] := Module[{pool = xmEdgeKey /@ rhs, position},
  Select[
    lhs,
    Function[edge,
      position = FirstPosition[pool, Verbatim[xmEdgeKey[edge]], None, {1}, Heads -> False];
      If[position === None, False, pool = Delete[pool, position]; True]
    ]
  ]
]


(* The rule's kept motif: its kept edges split into connected pieces by
   shared variables, over every member of a rule set, each isomorphism class
   once. PreserveMotif and AddStableSubstructure (catalog 10) create exactly
   such edges. *)
xmKeptPieces[rule : (_List -> _List)] :=
  With[{kept = xmKeptEdges[rule]}, Part[kept, #] & /@ xmEdgeComponents[kept]]

xmKeptPieces[rules : {__Rule}] := Catenate[xmKeptPieces /@ rules]

xmKeptPieces[_] := {}

xmKeptMotifs[rule_] := DeleteDuplicatesBy[xmKeptPieces[rule], CanonicalStateForm]


(* Mean over consecutive step pairs (t, t + 1) with an occurrence at t of the
   fraction of occurrences at t that persist to t + 1. An occurrence persists
   when every one of its edges continues its lineage to t + 1: lineage edges
   keep their keys, so the same edges still form the motif, and a motif that
   is destroyed and formed again from new edges does not persist. *)
xmMotifPersistence[evolution_Association, parameters_Association] := Module[
  {motif = Lookup[parameters, "Motif", Automatic], motifs, live, lineage, lineageOf, found, occurrences, fractions},

  If[
    !xmValidMotifQ[motif],
    Return @ Failure[
      "InvalidMotif",
      <|"Message" -> "The \"Motif\" parameter must be Automatic or a nonempty hyperedge list.", "Motif" -> motif|>
    ]
  ];
  motifs = If[motif === Automatic, xmKeptMotifs[Lookup[evolution, "Rule", None]], {motif}];
  If[motifs === {}, Return @ Missing["NoKeptMotif"]];

  live = evolution["LiveEdges"];
  If[Length[live] < 2, Return @ Missing["NoStepPairs"]];

  lineage = xmEdgeLineages[evolution];
  lineageOf[id_] := Lookup[lineage, id, id];

  (* Occurrences of every motif at every step but the last. *)
  found = xmMotifOccurrences[<|"States" -> Most[evolution["States"]], "LiveEdges" -> Most[live]|>, #] & /@ motifs;
  If[AnyTrue[found, FailureQ], Return @ SelectFirst[found, FailureQ]];
  occurrences = Table[
    DeleteDuplicates @ Catenate @ MapIndexed[
      Function[{steps, index}, {First[index], #} & /@ steps[[t]]],
      found
    ],
    {t, Length[live] - 1}
  ];

  fractions = MapThread[
    Function[{now, next},
      If[
        now === {},
        Nothing,
        With[{continuing = AssociationThread[(lineageOf /@ next) -> True]},
          N[Count[now, {_, ids_} /; AllTrue[ids, KeyExistsQ[continuing, lineageOf[#]] &]] / Length[now]]
        ]
      ]
    ],
    {occurrences, Rest[live]}
  ];
  If[fractions === {}, Missing["NoOccurrences"], N @ Mean[fractions]]
]

xmMotifPersistence[other_, _] := xmUnavailable["EventEvolution", other]


(* Hubs of a state: the vertices of incidence degree at least k (a hyperedge
   counted once per vertex, as in DegreeMetrics). *)
xmHubs[state_List, k_Integer] := Keys @ Select[Counts @ Flatten[DeleteDuplicates /@ state], # >= k &]


(* Mean over consecutive step pairs (t, t + 1) with a hub at t of the
   fraction of hubs at t that are still hubs at t + 1. A hub is followed by
   its vertex, whatever happens to its edges: the event-level evolution
   never reuses a vertex name. *)
xmHubPersistence[evolution_Association, parameters_Association] := Module[
  {k = Lookup[parameters, "HubDegree", 3], hubs, fractions},
  If[
    !(IntegerQ[k] && k >= 1),
    Return @ Failure[
      "InvalidHubDegree",
      <|"Message" -> "The \"HubDegree\" parameter must be a positive integer.", "HubDegree" -> k|>
    ]
  ];
  hubs = xmHubs[#, k] & /@ evolution["States"];
  If[Length[hubs] < 2, Return @ Missing["NoStepPairs"]];
  fractions = MapThread[
    Function[{now, next}, If[now === {}, Nothing, N[Length[Intersection[now, next]] / Length[now]]]],
    {Most[hubs], Rest[hubs]}
  ];
  If[fractions === {}, Missing["NoHubs"], N @ Mean[fractions]]
]

xmHubPersistence[other_, _] := xmUnavailable["EventEvolution", other]


(* Mean over consecutive step pairs (t, t + 1) with a live edge at t of the
   fraction of live edges at t still live at t + 1, by edge ID: the share of
   edges no event touches. *)
xmEdgeSurvivalRate[evolution_Association] := Module[{live = evolution["LiveEdges"], fractions},
  If[Length[live] < 2, Return @ Missing["NoStepPairs"]];
  fractions = MapThread[
    Function[{now, next}, If[now === {}, Nothing, N[Length[Intersection[now, next]] / Length[now]]]],
    {Most[live], Rest[live]}
  ];
  If[fractions === {}, Missing["NoEdges"], N @ Mean[fractions]]
]

xmEdgeSurvivalRate[other_] := xmUnavailable["EventEvolution", other]


(* ::Section:: *)
(*Branchial graphs*)


(* Branchial graph of every layer k of a generation-unrolled evolution graph
   (vertices {state, k}): the states of layer k, with an undirected edge
   between two states that share a parent in layer k - 1. *)
xmBranchialGraphsFromEvolutionGraph[graph_Graph] := Module[{layers, edges},
  layers = KeySort @ GroupBy[VertexList[graph], Last -> First];
  edges = GroupBy[
    Catenate @ Map[
      Function[children,
        Function[{a, b}, {Last[a], UndirectedEdge @@ Sort[{First[a], First[b]}]}] @@@
          Subsets[children, {2}]
      ],
      Values @ GroupBy[EdgeList[graph], First -> Last, DeleteDuplicates]
    ],
    First -> Last,
    DeleteDuplicates
  ];
  Association @ KeyValueMap[
    Function[{k, states}, k -> Graph[states, Lookup[edges, k, {}]]],
    layers
  ]
]


evolutionGraphQ[graph_Graph] := AllTrue[VertexList[graph], MatchQ[{_, _Integer}]]


BranchialGraphs[evolution_Association, depth : (_Integer?NonNegative | Automatic) : Automatic] /;
  KeyExistsQ[evolution, "StatesGraph"] && KeyExistsQ[evolution, "Generations"] :=
  Replace[
    MultiwayEvolutionGraph[evolution, depth],
    graph_Graph :> xmBranchialGraphsFromEvolutionGraph[graph]
  ]

BranchialGraphs[graph_Graph?evolutionGraphQ] := xmBranchialGraphsFromEvolutionGraph[graph]

BranchialGraphs[failure_Failure, ___] := failure

BranchialGraphs[other_, ___] :=
  Failure[
    "InvalidEvolution",
    <|
      "Message" -> "BranchialGraphs expects a CanonicalMultiwayEvolution result or a MultiwayEvolutionGraph.",
      "Value" -> Short[other]
    |>
  ]


BranchialGraph[evolution_, k_Integer] :=
  Replace[
    BranchialGraphs[evolution],
    graphs_Association :> Lookup[graphs, k, Missing["NoSuchLayer", k]]
  ]


(* The branchial graph of the "Slice" layer: Automatic is the first widest
   layer (most states, earliest on ties). *)
xmBranchialSlice[graphs_Association, slice_] :=
  Which[
    graphs === <||>, Missing["NoLayers"],
    slice === Automatic, First @ MaximalBy[Values @ KeySort[graphs], VertexCount],
    IntegerQ[slice], Lookup[graphs, slice, Missing["NoSuchSlice", slice]],
    True, Failure["InvalidSlice", <|"Message" -> "\"Slice\" must be Automatic or a layer index.", "Slice" -> slice|>]
  ]


xmBranchialMeanDegree[graphs_Association, parameters_Association] :=
  With[{graph = xmBranchialSlice[graphs, Lookup[parameters, "Slice", Automatic]]},
    If[GraphQ[graph], N @ Mean[VertexDegree[graph]], graph]
  ]

xmBranchialMeanDegree[other_, _] := xmUnavailable["BranchialGraphs", other]


xmMeanBranchialDistance[graphs_Association, parameters_Association] :=
  With[{graph = xmBranchialSlice[graphs, Lookup[parameters, "Slice", Automatic]]},
    Which[
      !GraphQ[graph], graph,
      VertexCount[graph] < 2, Missing["FewerThanTwoStates"],
      True,
        With[
          {
            distances = Select[
              Catenate @ With[{matrix = Normal @ GraphDistanceMatrix[graph], n = VertexCount[graph]},
                Table[matrix[[i, j]], {i, n - 1}, {j, i + 1, n}]
              ],
              NumericQ
            ]
          },
          If[distances === {}, Missing["NoConnectedPairs"], N @ Mean[distances]]
        ]
    ]
  ]

xmMeanBranchialDistance[other_, _] := xmUnavailable["BranchialGraphs", other]


registerArtifactBuilder[
  "BranchialGraphs",
  Function[{rule, state, evolution, config, built},
    Replace[
      Lookup[built, "EvolutionGraph", Missing["NotBuilt"]],
      {graph_Graph :> xmBranchialGraphsFromEvolutionGraph[graph], other_ :> other}
    ]
  ],
  {"EvolutionGraph"}
];


(* ::Section:: *)
(*Registration*)


$xmMetrics = <|

  (* Structural, over the canonical explored states. *)

  "LargestComponentRatio" -> <|
    "Input" -> "States",
    "Function" -> xmLargestComponentRatio,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over explored states with at least one vertex of the fraction of their vertices in the largest connected component of the spatial projection; Missing[\"NoVertices\"] when no explored state has a vertex."
  |>,

  "NumberOfConnectedComponents" -> <|
    "Input" -> "States",
    "Function" -> xmNumberOfConnectedComponents,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest number of connected components of the spatial projection over explored states (0 for the empty state)."
  |>,

  "LargestConnectedComponentSize" -> <|
    "Input" -> "States",
    "Function" -> xmLargestConnectedComponentSize,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest vertex count of a connected component of the spatial projection over explored states; Missing[\"NoVertices\"] when no explored state has a vertex."
  |>,

  "EffectiveDimensionEstimate" -> <|
    "Input" -> "States",
    "Function" -> xmMeanDimensionEstimate,
    "Direction" -> "Target",
    "Target" -> 2.,
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean of EffectiveDimensionEstimate over the explored states that have an estimate (target 2. when promoted); Missing[\"InsufficientStructure\"] when no explored state has one."
  |>,

  "DimensionVariance" -> <|
    "Input" -> "States",
    "Function" -> xmMeanDimensionVariance,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean of DimensionVariance (the variance of local dimension estimates) over the explored states that have one; Missing[\"InsufficientStructure\"] when no explored state has one."
  |>,

  "MaxVertexDegree" -> <|
    "Input" -> "States",
    "Function" -> xmMaxVertexDegree,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest vertex incidence degree (number of hyperedges containing the vertex) over explored states; Missing[\"NoVertices\"] when no explored state has a vertex."
  |>,

  "VertexDegreeVariance" -> <|
    "Input" -> "States",
    "Function" -> xmMeanVertexDegreeVariance,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over explored states with at least one vertex of the sample variance of vertex incidence degrees (0. for a one-vertex state, as in DegreeMetrics); Missing[\"NoVertices\"] when there is no such state."
  |>,

  "MaxVertexDegreeVariance" -> <|
    "Input" -> "States",
    "Function" -> xmMaxVertexDegreeVariance,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Largest sample variance of vertex incidence degrees over explored states with at least one vertex (0. for a one-vertex state); Missing[\"NoVertices\"] when there is no such state."
  |>,

  (* "Range" without a fixed "Range": resolved from the configuration's
     RatioRange when promoted, like HGMaxEdgeToVertexRatio. *)
  "HGMeanEdgeToVertexRatio" -> <|
    "Input" -> "States",
    "Function" -> xmMeanEdgeToVertexRatio,
    "Direction" -> "Range",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over explored states with at least one vertex of edge count divided by vertex count (multiplicity included in multiset universes), ranged by the configuration's RatioRange unless a \"Range\" override is given; Missing[\"NoVertices\"] when there is no such state."
  |>,

  (* Structural, over the verified terminal states. *)

  "FinalVertexCount" -> <|
    "Input" -> "FinalStates",
    "Function" -> Function[states, xmTerminalMean[states, HypergraphVertexCount]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean vertex count over verified terminal states; Missing[\"NoTerminalStates\"] when there are none."
  |>,

  "FinalEdgeCount" -> <|
    "Input" -> "FinalStates",
    "Function" -> Function[states, xmTerminalMean[states, HypergraphEdgeCount]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean edge count over verified terminal states (multiplicity included in multiset universes); Missing[\"NoTerminalStates\"] when there are none."
  |>,

  "FinalDensity" -> <|
    "Input" -> "FinalStates",
    "Function" -> Function[states, xmTerminalMean[states, HypergraphDensity]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean HypergraphDensity over verified terminal states (0. for the empty state); Missing[\"NoTerminalStates\"] when there are none."
  |>,

  "FinalMaxVertexDegree" -> <|
    "Input" -> "FinalStates",
    "Function" -> Function[states, xmTerminalMean[states, xmTerminalDegreeStatistic[#, "MaxVertexDegree"] &]],
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over verified terminal states of the largest vertex incidence degree (0 for the empty state); Missing[\"NoTerminalStates\"] when there are none."
  |>,

  "FinalVertexDegreeVariance" -> <|
    "Input" -> "FinalStates",
    "Function" -> Function[states, xmTerminalMean[states, xmTerminalDegreeStatistic[#, "VertexDegreeVariance"] &]],
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over verified terminal states of the sample variance of vertex incidence degrees (0. for states with fewer than two vertices); Missing[\"NoTerminalStates\"] when there are none."
  |>,

  (* Branching and confluence. *)

  "OutDegreeEntropy" -> <|
    "Input" -> "StatesGraph",
    "Function" -> Function[graph, xmBranching[graph, "OutDegreeEntropy"]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Base-2 entropy of the distribution of positive out-degrees over the explored states of the canonical states graph (BranchingUncertainty), 0. when no explored state has a successor."
  |>,

  "MeanBranchingStrength" -> <|
    "Input" -> "StatesGraph",
    "Function" -> Function[graph, xmBranching[graph, "MeanBranchingStrength"]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean of Log2 of the positive out-degrees over the explored states of the canonical states graph (BranchingUncertainty), 0. when no explored state has a successor."
  |>,

  "ReconvergenceRatio" -> <|
    "Input" -> "StatesGraph",
    "Function" -> xmReconvergenceRatio,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Fraction of branch pairs (pairs of distinct successors of one explored state) whose future cones intersect inside the explored states graph; Missing[\"NoBranchPairs\"] when there are none."
  |>,

  "ResolvedBranchPairRatio" -> <|
    "Input" -> "EvaluationContext",
    "Artifacts" -> {"EventRecords"},
    "Function" -> xmResolvedBranchPairRatio,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Fraction of critical pairs (pairs of raw events at one explored state whose matched edge positions intersect and whose canonical successors differ) whose successors' future cones intersect inside the explored states graph; Missing[\"NoCriticalPairs\"] when there are none."
  |>,

  "CausalInvariantWithinCapQ" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> xmCausalInvariantWithinCapQ,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> (MatchQ[#, True | False] &),
    "ValueType" -> "Boolean",
    "Description" -> "True when the exploration halted and every branch pair reconverges inside the explored states graph, which by Newman's lemma implies a unique terminal state of the canonical system; False otherwise."
  |>,

  (* Causal and rewrite activity of the event-level evolution. *)

  "CausalMergeEventsRatio" -> <|
    "Input" -> "CausalGraph",
    "Function" -> xmCausalMergeEventsRatio,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Fraction of the events of the event-level evolution (configured UpdateOrder) whose causal in-degree, counted with multiplicity, is at least 2; Missing[\"NoEvents\"] when no event occurred."
  |>,

  "CausalDependencyEntropy" -> <|
    "Input" -> "CausalGraph",
    "Function" -> xmCausalDependencyEntropy,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Base-2 entropy of the distribution of positive causal out-degrees (counted with multiplicity) over the events of the event-level causal graph; Missing[\"NoCausalEdges\"] when no event has a causal successor."
  |>,

  "RewriteActivityMean" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmRewriteActivityMean,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean number of events per generation of the event-level evolution (event Generation), i.e. the event count divided by the largest event generation; Missing[\"NoEvents\"] when no event occurred."
  |>,

  "RewriteActivityEntropy" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmRewriteActivityEntropy,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Base-2 Shannon entropy of the distribution of events over the generations of the event-level evolution, the event counts per generation normalized to probabilities; Missing[\"NoEvents\"] when no event occurred."
  |>,

  (* Update orders. *)

  "UpdateOrderSensitivity" -> <|
    "Input" -> "UpdateOrderRuns",
    "Function" -> xmUpdateOrderSensitivity,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "State outcomes: fraction of pairs of valid update-order runs (configured UpdateOrders) whose canonical final states, reached within the limits, differ; 0. when fewer than two runs are valid."
  |>,

  "CausalUpdateOrderSensitivity" -> <|
    "Input" -> "UpdateOrderRuns",
    "Function" -> xmCausalUpdateOrderSensitivity,
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Causal structure: fraction of pairs of valid update-order runs whose causal multigraphs are not isomorphic (exact canonical labelling, multiplicities included); 0. when fewer than two runs are valid, Missing[\"CanonicalFormLimit\"] when a labelling exceeds its search limit."
  |>,

  "UpdateOrderTerminalOutcomeCount" -> <|
    "Input" -> "UpdateOrderRuns",
    "Function" -> xmUpdateOrderTerminalOutcomeCount,
    "Direction" -> "Target",
    "Target" -> 1,
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Integer",
    "Description" -> "Number of distinct canonical final states among the update-order runs with Status \"Terminated\" (target 1 when promoted); Missing[\"NoTerminatedRuns\"] when no run terminated."
  |>,

  (* Local persistence of the event-level evolution. *)

  "LocalComponentLifetimeMean" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmLocalComponentLifetimeMean,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean length in steps over all occurrences of local components (maximal runs of consecutive steps in which one set of live edge IDs is exactly a connected component of the spatial projection; runs present at the last step count as observed); Missing[\"NoComponents\"] when no step has a live edge."
  |>,

  "LocalComponentLifetimeMax" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmLocalComponentLifetimeMax,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest length in steps over all occurrences of local components (maximal runs of consecutive steps in which one set of live edge IDs is exactly a connected component of the spatial projection); Missing[\"NoComponents\"] when no step has a live edge."
  |>,

  "MotifPersistence" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmMotifPersistence,
    "Parameters" -> <|"Motif" -> Automatic|>,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over consecutive step pairs (t, t + 1) with an occurrence at t of the fraction of motif occurrences at t that persist to t + 1. An occurrence is a set of edges matching the motif pattern (matched like a rule left-hand side); it persists when the same edges still form it, an edge that a rewrite writes back unchanged keeping its identity (its lineage continues), so a motif destroyed and formed again from new edges does not persist. \"Motif\" -> Automatic (default) follows the rule's kept motif: its left-hand edges that the right-hand side writes back unchanged, in connected pieces, over every member of a rule set. Missing[\"NoKeptMotif\"] when the rule keeps no edge; Missing[\"NoStepPairs\"] or Missing[\"NoOccurrences\"] when undefined."
  |>,

  "HubPersistence" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmHubPersistence,
    "Parameters" -> <|"HubDegree" -> 3|>,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over consecutive step pairs (t, t + 1) with a hub at t of the fraction of hubs at t that are still hubs at t + 1. A hub is a vertex of incidence degree at least \"HubDegree\" (default 3; a hyperedge counted once per vertex), followed by its vertex whatever happens to its edges (the event-level evolution never reuses a vertex name). Missing[\"NoStepPairs\"] or Missing[\"NoHubs\"] when undefined."
  |>,

  "EdgeSurvivalRate" -> <|
    "Input" -> "EventEvolution",
    "Function" -> xmEdgeSurvivalRate,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean over consecutive step pairs (t, t + 1) with a live edge at t of the fraction of live edges at t that are still live at t + 1, by edge ID (edges no event consumes); Missing[\"NoStepPairs\"] or Missing[\"NoEdges\"] when undefined."
  |>,

  (* Branchial. *)

  "BranchialMeanDegree" -> <|
    "Input" -> "BranchialGraphs",
    "Function" -> xmBranchialMeanDegree,
    "Parameters" -> <|"Slice" -> Automatic|>,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean vertex degree of the branchial graph of the \"Slice\" layer of the evolution graph (Automatic: the first widest layer), 0. for a one-state layer; Missing[\"NoSuchSlice\", k] when the layer does not exist."
  |>,

  "MeanBranchialDistance" -> <|
    "Input" -> "BranchialGraphs",
    "Function" -> xmMeanBranchialDistance,
    "Parameters" -> <|"Slice" -> Automatic|>,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Real",
    "Description" -> "Mean shortest-path distance over connected pairs of distinct states in the branchial graph of the \"Slice\" layer (Automatic: the first widest layer); Missing[\"FewerThanTwoStates\"] or Missing[\"NoConnectedPairs\"] when undefined."
  |>

|>;

registerFitnessMetrics[$xmMetrics];

$xmMetricNames = Keys[$xmMetrics];


(* ::Section:: *)
(*Classification*)


(* Thresholds of the default criteria (DefaultClassificationCriteria[params]
   overrides them by name). Owner decision: they ship as provisional
   defaults, to be revised by the owner; DefaultClassificationCriteria
   reports this in its top-level "Status" and every ClassifyCandidate label
   result based on an unmodified default criterion has "CriteriaStatus" ->
   "Provisional" ("UserSupplied" otherwise). *)
$xmCriteriaStatus = "Provisional (owner review pending)";

$xmClassificationParameters = <|
  "MinNonIsomorphicTerminalStates" -> 3,
  "MinMeanTerminalVertexCount" -> 5,
  "TargetDimension" -> 2.,
  "DimensionTolerance" -> 0.5,
  "SpaceLikeMaxDimensionVariance" -> 0.25,
  "MinLargestComponentRatio" -> 0.9,
  "HomogeneousMaxDimensionVariance" -> 0.1,
  "HomogeneousMaxVertexDegreeVariance" -> 1.,
  "MinLocalComponentLifetimeMax" -> 3,
  "MinMotifPersistence" -> 0.5,
  "Motif" -> Automatic
|>;


$xmConditionTests = {"AtLeast", "AtMost", "Equals", "Within"};


xmCondition[metric_String, test_String, value_] :=
  <|"Metric" -> metric, "Test" -> test, "Value" -> value|>

xmCondition[metric_String, "Within", value_, tolerance_] :=
  <|"Metric" -> metric, "Test" -> "Within", "Value" -> value, "Tolerance" -> tolerance|>


DefaultClassificationCriteria[] := DefaultClassificationCriteria[<||>]

DefaultClassificationCriteria[parameters_Association] := Module[{unknown, p, motifCondition},
  unknown = Complement[Keys[parameters], Keys[$xmClassificationParameters]];
  If[
    unknown =!= {},
    Return @ Failure[
      "UnknownClassificationParameter",
      <|"Message" -> "Unknown classification parameters.", "Parameters" -> unknown, "Known" -> Keys[$xmClassificationParameters]|>
    ]
  ];
  p = Join[$xmClassificationParameters, parameters];
  If[
    !xmValidMotifQ[p["Motif"]],
    Return @ Failure["InvalidMotif", <|"Message" -> "\"Motif\" must be Automatic or a nonempty hyperedge list.", "Motif" -> p["Motif"]|>]
  ];

  motifCondition = xmCondition["MotifPersistence", "AtLeast", p["MinMotifPersistence"]];
  If[p["Motif"] =!= Automatic, motifCondition["Parameters"] = <|"Motif" -> p["Motif"]|>];

  <|
    "Status" -> $xmCriteriaStatus,

    "RichTerminalStates" -> <|
      "Description" -> "The exploration halted with several non-isomorphic verified terminal states of substantial mean size.",
      "AllOf" -> {
        xmCondition["HaltedWithinCapQ", "Equals", True],
        xmCondition["NonIsomorphicTerminalStateCount", "AtLeast", p["MinNonIsomorphicTerminalStates"]],
        xmCondition["FinalVertexCount", "AtLeast", p["MinMeanTerminalVertexCount"]]
      }
    |>,

    "SpaceLike" -> <|
      "Description" -> "The explored states have a mean effective dimension estimate near the target, little variation of local dimension estimates and one dominant connected component.",
      "AllOf" -> {
        xmCondition["EffectiveDimensionEstimate", "Within", p["TargetDimension"], p["DimensionTolerance"]],
        xmCondition["DimensionVariance", "AtMost", p["SpaceLikeMaxDimensionVariance"]],
        xmCondition["LargestComponentRatio", "AtLeast", p["MinLargestComponentRatio"]]
      }
    |>,

    "Homogeneous" -> <|
      "Description" -> "Local dimension estimates and vertex incidence degrees vary little across the explored states.",
      "AllOf" -> {
        xmCondition["DimensionVariance", "AtMost", p["HomogeneousMaxDimensionVariance"]],
        xmCondition["VertexDegreeVariance", "AtMost", p["HomogeneousMaxVertexDegreeVariance"]]
      }
    |>,

    "LocallyStable" -> <|
      "Description" -> "In the event-level evolution some local component persists unchanged over several steps and occurrences of the rule's kept motif (or of the given \"Motif\") mostly persist from step to step.",
      "AllOf" -> {
        xmCondition["LocalComponentLifetimeMax", "AtLeast", p["MinLocalComponentLifetimeMax"]],
        motifCondition
      }
    |>,

    "CausalInvariant" -> <|
      "Description" -> "Either the exploration halted and every branch pair reconverges (by Newman's lemma the canonical system then has a unique terminal state), or every tested update order that terminated reached the same canonical final state and no two update-order runs differ in final state.",
      "AnyOf" -> {
        {xmCondition["CausalInvariantWithinCapQ", "Equals", True]},
        {
          xmCondition["UpdateOrderTerminalOutcomeCount", "Equals", 1],
          xmCondition["UpdateOrderSensitivity", "Equals", 0.]
        }
      }
    |>
  |>
]

DefaultClassificationCriteria[other_] :=
  Failure["InvalidClassificationParameters", <|"Message" -> "Parameters must be an Association.", "Value" -> other|>]


xmValidConditionQ[condition_Association] :=
  StringQ[Lookup[condition, "Metric", None]] &&
    MemberQ[$xmConditionTests, Lookup[condition, "Test", None]] &&
    KeyExistsQ[condition, "Value"] &&
    (condition["Test"] === "Equals" || NumericQ[condition["Value"]]) &&
    (condition["Test"] =!= "Within" || NumericQ[Lookup[condition, "Tolerance", None]]) &&
    AssociationQ[Lookup[condition, "Parameters", <||>]]

xmValidConditionQ[_] := False


xmValidCriterionQ[criterion_Association] :=
  Which[
    KeyExistsQ[criterion, "AllOf"], MatchQ[criterion["AllOf"], {__?xmValidConditionQ}],
    KeyExistsQ[criterion, "AnyOf"], MatchQ[criterion["AnyOf"], {{__?xmValidConditionQ} ..}],
    True, False
  ]

xmValidCriterionQ[_] := False


(* Lists of conditions, one list per alternative (a single list for AllOf). *)
xmAlternatives[criterion_Association] :=
  If[KeyExistsQ[criterion, "AllOf"], {criterion["AllOf"]}, criterion["AnyOf"]]


(* Label -> criterion; a top-level string "Status" (as returned by
   DefaultClassificationCriteria) is metadata, not a label. *)
xmDefaultCriteria[] := KeyDrop[DefaultClassificationCriteria[], "Status"]

xmResolveCriteria[Automatic] := xmDefaultCriteria[]

xmResolveCriteria[label_String] := xmResolveCriteria[{label}]

xmResolveCriteria[labels : {__String}] :=
  With[{defaults = xmDefaultCriteria[]},
    If[
      SubsetQ[Keys[defaults], labels],
      KeyTake[defaults, labels],
      Failure[
        "UnknownClassificationLabel",
        <|"Message" -> "Unknown default classification labels.", "Labels" -> Complement[labels, Keys[defaults]]|>
      ]
    ]
  ]

xmResolveCriteria[criteria_Association] :=
  With[{labels = If[StringQ[Lookup[criteria, "Status", None]], KeyDrop[criteria, "Status"], criteria]},
    If[
      labels =!= <||> && AllTrue[Keys[labels], StringQ] && AllTrue[Values[labels], xmValidCriterionQ],
      labels,
      Failure[
        "InvalidClassificationCriteria",
        <|
          "Message" -> "Criteria must be an Association label -> <|\"AllOf\" -> {condition, ...}|> or <|\"AnyOf\" -> {{condition, ...}, ...}|>, each condition <|\"Metric\" -> name, \"Test\" -> \"AtLeast\" | \"AtMost\" | \"Equals\" | \"Within\", \"Value\" -> value|> (\"Within\" also needs a numeric \"Tolerance\").",
          "Criteria" -> criteria
        |>
      ]
    ]
  ]

xmResolveCriteria[other_] :=
  Failure["InvalidClassificationCriteria", <|"Message" -> "Criteria must be Automatic, label names or an Association.", "Criteria" -> other|>]


(* A normalized configuration, such as a run's stored "Configuration", is
   used as given, not validated again: the stored "ResumeFrom" of a resumed
   run keeps only the resumed run's ID, which the validator rejects. *)
xmNormalizedConfigurationQ[configuration_Association] :=
  KeyExistsQ[configuration, "RecommendedMutationStrategies"] &&
    ListQ[Lookup[configuration, "FitnessMetrics", None]] &&
    ListQ[Lookup[configuration, "UpdateOrders", None]] &&
    AssociationQ[Lookup[configuration, "EvolutionLimits", None]]

xmResolveConfiguration[Automatic] := ValidateEvolutionConfiguration[<||>]

xmResolveConfiguration[configuration_Association] :=
  If[
    xmNormalizedConfigurationQ[configuration],
    configuration,
    ValidateEvolutionConfiguration[configuration]
  ]

xmResolveConfiguration[other_] :=
  Failure["InvalidConfiguration", <|"Message" -> "The configuration must be Automatic or an Association.", "Value" -> other|>]


(* Metric values for the requested {metric, parameters} pairs: values in the
   candidate's "Fitness" are reused for parameterless requests; the others
   are evaluated with EvaluateCandidate under the configuration (one call for
   the parameterless metrics, one per parameterized request). Returns
   {values (request -> value), status}. *)
xmRequest[condition_Association] := xmRequest[condition["Metric"], Lookup[condition, "Parameters", None]]

xmMetricValues[candidate_Association, requests_List, configuration_Association] := Module[
  {
    fitness = Lookup[candidate, "Fitness", <||>], values = <||>, pending, known,
    evaluableQ, status = Lookup[candidate, "Status", Missing["NotEvaluated"]], evaluate
  },

  If[!AssociationQ[fitness], fitness = <||>];

  Scan[
    Function[request,
      If[
        request[[2]] === None && KeyExistsQ[fitness, request[[1]]] && !FailureQ[fitness[request[[1]]]],
        AssociateTo[values, request -> fitness[request[[1]]]]
      ]
    ],
    requests
  ];

  pending = Select[requests, !KeyExistsQ[values, #] &];
  known = Join[Keys[$FitnessMetricRegistry], Keys[Lookup[configuration, "CustomFitnessMetrics", <||>]]];
  Scan[
    If[!MemberQ[known, #[[1]]], AssociateTo[values, # -> Missing["UnknownMetric", #[[1]]]]] &,
    pending
  ];
  pending = Select[pending, !KeyExistsQ[values, #] &];

  evaluableQ = KeyExistsQ[candidate, "Rule"] && KeyExistsQ[candidate, "InitialState"];
  If[
    !evaluableQ,
    Scan[AssociateTo[values, # -> Missing["NotEvaluated"]] &, pending];
    Return[{values, status}]
  ];

  (* One evaluation of the given metrics with optional parameter overrides. *)
  evaluate[names_List, overrides_Association] := Module[{result},
    result = EvaluateCandidate[
      <|"Rule" -> candidate["Rule"], "InitialState" -> candidate["InitialState"]|>,
      Join[
        configuration,
        <|
          "FitnessMetrics" -> names,
          "MetricOverrides" -> Join[Lookup[configuration, "MetricOverrides", <||>], overrides]
        |>
      ]
    ];
    If[MissingQ[status], status = Lookup[result, "Status", Missing["NotEvaluated"]]];
    Lookup[Lookup[result, "Fitness", <||>], names, Missing["EvaluationFailed"]]
  ];

  With[{plain = Select[pending, #[[2]] === None &]},
    If[
      plain =!= {},
      MapThread[
        AssociateTo[values, #1 -> #2] &,
        {plain, evaluate[plain[[All, 1]], <||>]}
      ]
    ]
  ];

  Scan[
    Function[request,
      AssociateTo[
        values,
        request -> First @ evaluate[
          {request[[1]]},
          <|
            request[[1]] -> Append[
              Lookup[Lookup[configuration, "MetricOverrides", <||>], request[[1]], <||>],
              "Parameters" -> request[[2]]
            ]
          |>
        ]
      ]
    ],
    Select[pending, #[[2]] =!= None &]
  ];

  {values, status}
]


(* Three-valued outcomes (Kleene logic): a Missing or failed value leaves a
   condition Undetermined. *)
xmConditionOutcome[condition_Association, value_] :=
  Which[
    MissingQ[value] || FailureQ[value], Undetermined,
    condition["Test"] === "Equals",
      Which[
        BooleanQ[condition["Value"]] || BooleanQ[value], value === condition["Value"],
        NumericQ[value] && NumericQ[condition["Value"]], TrueQ[value == condition["Value"]],
        True, value === condition["Value"]
      ],
    !NumericQ[value], Undetermined,
    condition["Test"] === "AtLeast", TrueQ[value >= condition["Value"]],
    condition["Test"] === "AtMost", TrueQ[value <= condition["Value"]],
    condition["Test"] === "Within", TrueQ[Abs[value - condition["Value"]] <= condition["Tolerance"]],
    True, Undetermined
  ]

xmAllOf[outcomes_List] :=
  Which[MemberQ[outcomes, False], False, MemberQ[outcomes, Undetermined], Undetermined, True, True]

xmAnyOf[outcomes_List] :=
  Which[MemberQ[outcomes, True], True, MemberQ[outcomes, Undetermined], Undetermined, True, False]


xmFormatValue[value_Real] := ToString[NumberForm[value, 4]]
xmFormatValue[value_Integer] := ToString[value]
xmFormatValue[value : True | False] := ToString[value]
xmFormatValue[value_Missing] := ToString[value, InputForm]
xmFormatValue[_Failure] := "a failed evaluation"
xmFormatValue[value_] := ToString[Short[value], InputForm]

xmRequirementText[condition_Association] :=
  Switch[
    condition["Test"],
    "AtLeast", ">= " <> xmFormatValue[condition["Value"]],
    "AtMost", "<= " <> xmFormatValue[condition["Value"]],
    "Equals", "= " <> xmFormatValue[condition["Value"]],
    "Within", "within " <> xmFormatValue[condition["Tolerance"]] <> " of " <> xmFormatValue[condition["Value"]]
  ]

xmConditionText[result_Association] :=
  result["Metric"] <> " = " <> xmFormatValue[result["Value"]] <> " (required " <> xmRequirementText[result["Condition"]] <> ")"


xmEvidenceText[status_] :=
  Switch[
    status,
    "Halted", "status \"Halted\": the reachable canonical state space was exhausted and is acyclic",
    "CycleDetected", "status \"CycleDetected\": the reachable canonical state space was exhausted but contains a cycle",
    "GenerationCap" | "EventCap" | "StateCap" | "TimedOut",
      "status \"" <> status <> "\": exploration stopped at a limit, so the values describe only the explored part",
    _, "exploration status " <> xmFormatValue[status]
  ]


xmClaim[label_String, satisfied_, results_List, status_] := Module[{prefix, selected},
  prefix = "Within the explored limits (" <> xmEvidenceText[status] <> "), ";
  Switch[
    satisfied,
    True,
      selected = First @ Select[results, xmAllOf[Lookup[#, "Outcome"]] === True &];
      prefix <> "the " <> label <> " criteria are met: " <> StringRiffle[xmConditionText /@ selected, "; "] <> ".",
    False,
      selected = Select[Catenate[results], #["Outcome"] === False &];
      prefix <> "the " <> label <> " criteria are not met: " <> StringRiffle[xmConditionText /@ selected, "; "] <> ".",
    _,
      selected = Select[Catenate[results], #["Outcome"] === Undetermined &];
      prefix <> "the " <> label <> " criteria are undetermined because these values are undefined: " <>
        StringRiffle[xmConditionText /@ selected, "; "] <> "."
  ]
]


xmClassifyLabel[label_String, criterion_Association, values_Association, status_, criteriaStatus_String] := Module[
  {results, satisfied},

  results = Map[
    Function[condition,
      With[{value = Lookup[values, Key[xmRequest[condition]], Missing["NotEvaluated"]]},
        <|
          "Metric" -> condition["Metric"],
          "Value" -> value,
          "Condition" -> condition,
          "Outcome" -> xmConditionOutcome[condition, value]
        |>
      ]
    ],
    xmAlternatives[criterion],
    {2}
  ];
  satisfied = xmAnyOf[xmAllOf[Lookup[#, "Outcome"]] & /@ results];

  <|
    "Label" -> label,
    "Satisfied" -> satisfied,
    "Evidence" -> Association[(#["Metric"] -> #["Value"]) & /@ Catenate[results]],
    "Criteria" -> criterion,
    "CriteriaStatus" -> criteriaStatus,
    "Claim" -> xmClaim[label, satisfied, results, status],
    "Status" -> status,
    "ConditionResults" -> results
  |>
]


ClassifyCandidate[candidate_Association] := ClassifyCandidate[candidate, Automatic, Automatic]

ClassifyCandidate[candidate_Association, criteria_] := ClassifyCandidate[candidate, criteria, Automatic]

ClassifyCandidate[candidate_Association, criteriaSpec_, configurationSpec_] := Module[
  {criteria, configuration, requests, values, status, defaults},

  criteria = xmResolveCriteria[criteriaSpec];
  If[FailureQ[criteria], Return[criteria]];
  configuration = xmResolveConfiguration[configurationSpec];
  If[FailureQ[configuration], Return[configuration]];

  requests = DeleteDuplicates[
    xmRequest /@ Catenate[Catenate[xmAlternatives /@ Values[criteria]]]
  ];
  {values, status} = xmMetricValues[candidate, requests, configuration];

  (* A label judged by an unmodified default criterion inherits the
     provisional status of the default thresholds. *)
  defaults = xmDefaultCriteria[];
  AssociationMap[
    xmClassifyLabel[
      #,
      criteria[#],
      values,
      status,
      If[criteria[#] === Lookup[defaults, #, None], "Provisional", "UserSupplied"]
    ] &,
    Keys[criteria]
  ]
]

ClassifyCandidate[other_, ___] :=
  Failure["InvalidCandidate", <|"Message" -> "ClassifyCandidate expects a candidate Association.", "Value" -> Short[other]|>]
