(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Type checks*)


hypergraphStateQ[hg_List] := AllTrue[hg, MatchQ[#, {___?AtomQ}] &]
hypergraphStateQ[_] := False


(* Validator for metrics that report Missing[...] when a value is undefined
   (for example insufficient structure, or no finite longest derivation). *)
numericOrMissingQ[value_] := NumericQ[value] || MissingQ[value]


(* ::Section:: *)
(*Helper functions*)


(* ::Subsection:: *)
(*Update-order helpers*)


FinalState[evo_] := If[ListQ[evo], Last[evo], evo["FinalState"]]

(* Compares canonical final states in the active universe, so fresh vertex
   names created by different update orders do not count as differences. *)
FinalStatesDifferentQ[evo1_, evo2_] :=
  CanonicalStateForm[FinalState[evo1]] =!= CanonicalStateForm[FinalState[evo2]]


CausalGraphsDifferentQ[evo1_, evo2_] :=
  ! IsomorphicGraphQ[
    evo1["CausalGraph"],
    evo2["CausalGraph"]
  ]


(* ::Subsection:: *)
(*Dimension calculations*)


(* Geometry policy: every universe uses the same unordered, undirected simple
   projection of a state (slot order and edge multiplicity ignored). The
   geometry metrics built on it measure spatial structure, not edge order. *)
ToSpatialGraph[hg_] :=
  With[{edges = DeleteDuplicates[Sort /@ hg]},
    (* The explicit vertex list keeps vertices that occur only in one-vertex
       hyperedges, which the projection's edge list cannot carry. *)
    SimpleGraph @ UndirectedGraph @ Graph[
      DeleteDuplicates @ Flatten[edges],
      EdgeList @ ResourceFunction["HypergraphToGraph"][edges]
    ]
  ]


DetermineDimension[g_Graph, v_, radii_List] := Module[
  {data},

  data =
    Table[
      {
        Log[r],
        Log[VertexCount @ NeighborhoodGraph[g, v, r]]
      },
      {r, radii}
    ];

  (* Need at least some nonconstant growth to estimate dimension. *)
  If[
    Length[DeleteDuplicates[data[[All, 2]]]] < 2,
    Nothing,
    (* Least-squares slope in closed form: the slope LinearModelFit[data,
       {1, x}, x] returns, without fitting a model per vertex. *)
    With[{numeric = N[data]},
      Covariance[numeric[[All, 1]], numeric[[All, 2]]] / Variance[numeric[[All, 1]]]
    ]
  ]
]


LocalDimensionValues[hg_] := Module[
  {g, vertices, radii},

  g = ToSpatialGraph[hg];

  If[VertexCount[g] < 4, Return[{}]];

  (* GraphDiameter can fail or be infinite for disconnected graphs. *)
  If[! ConnectedGraphQ[g],
    g = Subgraph[g, First @ MaximalBy[ConnectedComponents[g], Length]]
  ];

  vertices = VertexList[g];

  If[Length[vertices] < 4, Return[{}]];

  radii = Range[1, Max[2, Floor[GraphDiameter[g]/2]]];

  DetermineDimension[g, #, radii] & /@ vertices
]


(* ::Subsection:: *)
(*Hypergraph size*)


(* Unordered mode: simple-hypergraph convention (sorted edges, duplicates
   removed). Ordered and declared modes: multiset convention -- edges are
   taken as given, multiplicity included. *)
HypergraphEdges[hg_] :=
  If[multisetUniverseQ[], hg, DeleteDuplicates[Sort /@ hg]]

HypergraphVertices[hg_] := DeleteDuplicates @ Flatten[hg]

HypergraphEdgeCount[hg_] := Length @ HypergraphEdges[hg]
HypergraphVertexCount[hg_] := Length @ HypergraphVertices[hg]


(* Distinct edge classes of a state in the active universe: sorted tuples
   (unordered), tuples (ordered) or least orbit tuples (declared). *)
distinctEdgeClasses[hg_] :=
  DeleteDuplicates @ Switch[
    $EdgeSymmetry,
    "Ordered", hg,
    "Declared", declaredEdgeRepresentative /@ hg,
    _, Sort /@ hg
  ]


(* Number of possible edge classes of arity k over n vertices in the active
   universe: the orbits of the slot-symmetry group on all k-tuples of
   vertices, repeated vertices allowed (Burnside's lemma). Unordered gives the
   multisets Binomial[n + k - 1, k]; ordered gives the tuples n^k. *)
possibleEdgeClassCount[n_Integer, k_Integer] :=
  Switch[
    $EdgeSymmetry,
    "Ordered", n^k,
    "Declared",
      With[{permutations = slotPermutations[k]},
        Total[
          n^(Length[First @ PermutationCycles[#]] + Count[# - Range[k], 0]) & /@ permutations
        ] / Length[permutations]
      ],
    _, Binomial[n + k - 1, k]
  ]


(* Density policy (every universe): the number of distinct edge classes
   divided by the number of possible edge classes of the arities that occur,
   over the state's vertices. It lies in [0, 1]; edge multiplicity is
   reported separately (EdgeMultiplicityMax). *)
HypergraphDensity[hg_] := Module[
  {edges, n, arities, possibleEdges},

  edges = distinctEdgeClasses[hg];
  n = HypergraphVertexCount[hg];

  arities = DeleteDuplicates[Length /@ edges];
  possibleEdges = Total[possibleEdgeClassCount[n, #] & /@ arities];

  If[
    edges === {} || possibleEdges === 0,
    0.,
    N[Length[edges] / possibleEdges]
  ]
]

OrderedHypergraphDensity[hg_] := Block[{$EdgeSymmetry = "Ordered"}, HypergraphDensity[hg]]


(* Largest number of copies of one edge class (1 for duplicate-free states;
   always 1 in the unordered universe). *)
EdgeMultiplicityMax[hg_] :=
  If[
    hg === {},
    0,
    Max @ Values @ Counts @ Switch[
      $EdgeSymmetry,
      "Ordered", hg,
      "Declared", declaredEdgeRepresentative /@ hg,
      _, DeleteDuplicates[Sort /@ hg]
    ]
  ]


(* ::Subsection:: *)
(*Regular graph size*)


GraphAltDensity[g_] := N[GraphDensity[g]]
GraphSafeAltDensity[g_] := If[VertexCount[g] < 2, "-", NumberForm[N[GraphDensity[g]], {3, 2}]]


EdgeToVertexRatio[g_Graph] := Module[
  {edgeCount, vertexCount},

  edgeCount = EdgeCount[g];
  vertexCount = VertexCount[g];

  If[
    vertexCount == 0,
    0.,
    N[edgeCount / vertexCount]
  ]
]


(* ::Subsection:: *)
(*Terminal states of a directed graph*)


(* Sink vertices only; genuine rule inapplicability is verified by the evaluator. *)
TerminalStates[g_Graph?DirectedGraphQ] := Pick[VertexList[g], VertexOutDegree[g], 0]

TerminalStateCount[g_Graph?DirectedGraphQ] := Length @ TerminalStates[g]


(* ::Subsection:: *)
(*Vertex degree*)


hypergraphIncidenceDegreeValues[hg_] := Values @ Counts @ Flatten[DeleteDuplicates /@ hg]

degreeMetricsFromValues[d_List] := <|
  "MaxVertexDegree" -> If[d === {}, 0, Max[d]],
  "VertexDegreeVariance" -> If[Length[d] <= 1, 0., N @ Variance[d]]
|>


(* ::Subsection:: *)
(*Multiway lifetime*)


MWHypergraphLifetime[mhg_Graph] := Module[
  {distances, terminals, initVertex},

  initVertex = First @ Pick[VertexList[mhg], VertexInDegree[mhg], 0];
  terminals = TerminalStates[mhg];

  distances = If[
    terminals === {},
    GraphDistance[mhg, initVertex, #] & /@ VertexList[mhg],

    (* We assume that wherever we terminate, one of those will be longest *)
    GraphDistance[mhg, initVertex, #] & /@ terminals
  ];

  Max[DeleteCases[distances, Infinity]]
]


(* Longest derivation of an evolution: exact when the evolution halted, the
   longest derivation within the limits for a capped acyclic exploration,
   Missing["CyclicStatesGraph"] when a cycle makes derivations unbounded. *)
MultiwayLongestDerivation[evolution_Association] :=
  Which[
    KeyExistsQ[evolution, "LongestDerivation"],
    evolution["LongestDerivation"],

    KeyExistsQ[evolution, "StatesGraph"] && KeyExistsQ[evolution, "Generations"],
    With[{graph = evolution["StatesGraph"]},
      If[
        !AcyclicGraphQ[graph] || !LoopFreeGraphQ[graph],
        Missing["CyclicStatesGraph"],
        longestPathLength[graph, First @ First @ evolution["Generations"]]
      ]
    ],

    True,
    Missing["NotAvailable"]
  ]

MultiwayLongestDerivation[rule_, state_, limits_Association : <||>] :=
  Replace[
    CanonicalMultiwayEvolution[rule, state, limits],
    evolution_Association :> evolution["LongestDerivation"]
  ]


(* ::Subsection:: *)
(*Graph components*)


ComponentMetrics[g_Graph] := Module[
	{comps = WeaklyConnectedComponents[g], compSizes},

	compSizes = Length /@ comps;

	If[compSizes === {},
		<|"NumberOfConnectedComponents" -> 0,
		  "LargestConnectedComponentSize" -> 0,
		  "LargestComponentRatio" -> 0.|>,

		<|"NumberOfConnectedComponents" -> Length[comps],
		  "LargestConnectedComponentSize" -> Max[compSizes],
		  "LargestComponentRatio" -> N[Max[compSizes] / Total[compSizes]]|>
	]
]


(* ::Subsection:: *)
(*Update-order sensitivity*)


(* Expects {evoOrder1, evoOrder2, ...} from different update orders *)
UpdateOrderSensitivity[runs_List] := Module[
  {pairs, stateDiffs, causalDiffs},

  pairs = Subsets[runs, {2}];

  If[pairs === {}, Return[0.]];

  stateDiffs =
    Boole[FinalStatesDifferentQ @@ #] & /@ pairs;

  causalDiffs =
    Boole[CausalGraphsDifferentQ @@ #] & /@ pairs;

  N @ Mean[
    Mean /@ Transpose[{stateDiffs, causalDiffs}]
  ]
]


(* Expects a list of final-state carriers (state lists or event evolutions) *)
UpdateOrderSensitivityStateOnly[runs_List] := Module[{pairs},

  If[Length[runs] < 2, Return[0.]];

  pairs = Subsets[runs, {2}];

  If[pairs === {}, 0.,
    N @ Mean[
      Boole[FinalStatesDifferentQ @@ #] & /@ pairs
    ]
  ]
]


(* ::Section:: *)
(*Hypergraph metrics*)


(* ::Subsection:: *)
(*Basic size*)


(* The type argument defaults to the active edge-symmetry universe; explicit
   "Unordered"/"Ordered" overrides remain supported. *)

resolveMetricsType[Automatic] := $EdgeSymmetry
resolveMetricsType[type_String] := type


(* Evolution Object -> extract states and pass recursively *)
HypergraphBasicSizeMetrics[evo_WolframModelEvolutionObject, type : (_String | Automatic) : Automatic] :=
	HypergraphBasicSizeMetrics[evo["StatesList", resolveMetricsType[type]]]

(* List of states (each state = separate hypergraph as hyperedges) -> aggregate *)
HypergraphBasicSizeMetrics[states : {__List} /; AllTrue[states, MatchQ[#, {___List}] &], type : (_String | Automatic) : Automatic] :=
	HypergraphStatesMetrics[states, resolveMetricsType[type]]

(* Single hypergraph -> per-state metrics *)
HypergraphBasicSizeMetrics[hg : {___List}, type : (_String | Automatic) : Automatic] :=
	HypergraphSizeMetrics[hg, resolveMetricsType[type]]


HypergraphSizeMetrics[hg_, type : (_String | Automatic) : Automatic] :=
  Block[{$EdgeSymmetry = resolveMetricsType[type]},
    Module[
	{edgesCount, verticesCount},

	edgesCount = HypergraphEdgeCount[hg];
	verticesCount = HypergraphVertexCount[hg];

	<|
	"HypergraphEdgesCount" -> edgesCount,
	"HypergraphVerticesCount" -> verticesCount,
	"HypergraphEdgeToVertexRatio" ->
		If[verticesCount === 0, 0., N[edgesCount / verticesCount]],
	"HypergraphDensity" -> HypergraphDensity[hg]
	|>
    ]
  ]

HypergraphStatesMetrics[states_List, type : (_String | Automatic) : Automatic] := Module[{statesMetrics},
	statesMetrics = HypergraphSizeMetrics[#, resolveMetricsType[type]] & /@ states;

	<|
	"RawStatesMetrics" -> statesMetrics,
	"HGMaxEdgesCount" -> Max @ statesMetrics[[All, "HypergraphEdgesCount"]],
	"HGMaxVerticesCount" -> Max @ statesMetrics[[All, "HypergraphVerticesCount"]],
	"HGMaxDensity" -> Max @ statesMetrics[[All, "HypergraphDensity"]],
	"HGMaxEdgeToVertexRatio" -> Max @ statesMetrics[[All, "HypergraphEdgeToVertexRatio"]],
	"HGMeanEdgesCount" -> N @ Mean @ statesMetrics[[All, "HypergraphEdgesCount"]],
	"HGMeanVerticesCount" -> N @ Mean @ statesMetrics[[All, "HypergraphVerticesCount"]],
	"HGMeanEdgeToVertexRatio" -> N @ Mean @ statesMetrics[[All, "HypergraphEdgeToVertexRatio"]],
	"HGMeanDensity" -> N @ Mean @ statesMetrics[[All, "HypergraphDensity"]]
	|>
]


(* ::Subsection:: *)
(*Final size*)


FinalStateSizeMetrics[evo_WolframModelEvolutionObject] := FinalStateSizeMetrics[evo["StatesList"]]


MultiwayFinalStateSizeMetrics[mhg_Graph?DirectedGraphQ] :=
	FinalStateSizeMetrics[{#}] & /@ TerminalStates[mhg]


FinalStateSizeMetrics[states_List] := Module[
	{lastState, edgesCount, vertexCount},
	lastState = Last[states];
	edgesCount = HypergraphEdgeCount[lastState];
	vertexCount = HypergraphVertexCount[lastState];

	<|
	"FinalVertices" -> HypergraphVertices[lastState],
	"FinalEdges" -> HypergraphEdges[lastState],
	"FinalVertexCount" -> vertexCount,
	"FinalEdgeCount" -> edgesCount,
	"FinalEdgeToVertexRatio" -> If[vertexCount <= 1, 0., N[edgesCount / vertexCount]],
	"FinalDensity" -> HypergraphDensity[lastState],
	"FinalAltDensity" -> If[lastState === {}, "-", GraphSafeAltDensity[ToSpatialGraph[lastState]]]
	|>
]


(* ::Subsection:: *)
(*Dimensions*)


(* Missing-value policy: a state too small for a dimension estimate (fewer
   than four vertices in its largest component, or no nonconstant
   neighborhood growth) gives Missing["InsufficientStructure"], never 0. *)

(* Base case: single hypergraph *)
EffectiveDimensionEstimate[hg : {___List}] := Module[
  {dims = LocalDimensionValues[hg]},
  If[dims === {}, Missing["InsufficientStructure"], N @ Mean[dims]]
]

(* StatesList -> final state *)
EffectiveDimensionEstimate[states : {__?hypergraphStateQ}] :=
  EffectiveDimensionEstimate[Last[states]]


(* Base case: single hypergraph *)
DimensionVariance[hg : {___List}] := Module[
  {dims = LocalDimensionValues[hg]},
  If[Length[dims] <= 1, Missing["InsufficientStructure"], N @ Variance[dims]]
]

(* StatesList -> final state *)
DimensionVariance[states : {__?hypergraphStateQ}] :=
  DimensionVariance[Last[states]]


(* ::Subsection:: *)
(*Vertex degree and variance*)


(* Single hypergraph *)
DegreeMetrics[hg_?hypergraphStateQ] :=
	degreeMetricsFromValues[hypergraphIncidenceDegreeValues[hg]]

(* StatesList *)
DegreeMetrics[states : {__?hypergraphStateQ}] := Module[
	{metrics, degreeMaxes, degreeVars},

	metrics = DegreeMetrics /@ states;
	degreeMaxes = metrics[[All, "MaxVertexDegree"]];
	degreeVars = metrics[[All, "VertexDegreeVariance"]];

	<|
	"MaxVertexDegree" -> Max[degreeMaxes],
	"FinalMaxVertexDegree" -> Last[degreeMaxes],
	"VertexDegreeVariance" -> N @ Mean[degreeVars],
	"MaxVertexDegreeVariance" -> Max[degreeVars],
	"FinalVertexDegreeVariance" -> Last[degreeVars]
	|>
]


(* ::Subsection:: *)
(*Runtime and lifetime*)


HypergraphRuntimeAndLifetime[rule_Rule, initState_, maxGens_Integer] := Module[
	{runtime, evolution, lifetime},

	{runtime, evolution} = AbsoluteTiming[
		CanonicalMultiwayEvolution[
			rule,
			initState,
			<|$DefaultEvolutionLimits, "MaxGenerations" -> maxGens|>
		]
	];

	lifetime = Max[0, Length[DeleteCases[evolution["Generations"], {}]] - 1];

	<|
	"Runtime" -> runtime,
	"Lifetime" -> lifetime,
	"HaltedWithinCapQ" -> evolution["Status"] === "Halted"
	|>
]


MWHypergraphRuntimeAndLifetime[rule_Rule, initState_] := Module[
	{runtime, evolution},

	{runtime, evolution} = AbsoluteTiming[
		CanonicalMultiwayEvolution[rule, initState, $DefaultEvolutionLimits]
	];

	<|
	"MultiwayRuntime" -> runtime,
	"MultiwayLifetime" -> Max[0, Length[DeleteCases[evolution["Generations"], {}]] - 1]
	|>
]


(* ::Subsection:: *)
(*Evolution and single-state branching*)


(* EvolutionObject: single-way evolution -- branching lives in the causal graph *)
BranchingUncertainty[evo_WolframModelEvolutionObject] :=
	BranchingUncertainty[evo["CausalGraph"]]

(* StatesList: linear sequence -- no branching by construction; report growth proxy *)
BranchingUncertainty[states : {__?hypergraphStateQ}] := <|
	"OutDegreeEntropy" -> 0.,
	"MeanBranchingStrength" -> 0.,
	"GrowthRatePerStep" -> If[Length[states] <= 1, 0.,
		N @ Mean[Ratios[Length /@ states] // Log2]]
|>

(* Single hypergraph: no process -- structural analog only *)
BranchingUncertainty[hg_?hypergraphStateQ] := <|
	"OutDegreeEntropy" -> Missing["NotApplicable"],
	"MeanBranchingStrength" -> Missing["NotApplicable"],
	"IncidenceDegreeEntropy" -> With[
		{d = Values @ Counts @ Flatten[DeleteDuplicates /@ hg]},
		If[d === {}, 0., N @ Entropy[2, d]]]
|>


(* ::Subsection:: *)
(*Causal dependencies and events*)


CausalDependencyEntropy[evo_WolframModelEvolutionObject] :=
	CausalDependencyEntropy[evo["CausalGraph"]]

CausalMergeEvents[evo_WolframModelEvolutionObject] :=
	CausalMergeEvents[evo["CausalGraph"]]


(* ::Subsection:: *)
(*Component analysis*)


(* Single hypergraph -> convert, recurse *)
ComponentMetrics[hg_?hypergraphStateQ] :=
	ComponentMetrics[ToSpatialGraph[hg]]


(* StatesList -> per-state metrics + temporal aggregates *)
ComponentMetrics[states : {__?hypergraphStateQ}] := Module[
	{metrics = ComponentMetrics /@ states, compCounts, ratios},
	compCounts = metrics[[All, "NumberOfConnectedComponents"]];
	ratios = metrics[[All, "LargestComponentRatio"]];
	<|
	"PerStateMetrics" -> metrics,
	"MaxComponentCount" -> Max[compCounts],
	"FinalComponentCount" -> Last[compCounts],
	"MeanLargestComponentRatio" -> N @ Mean[ratios],
	"FinalLargestComponentRatio" -> Last[ratios]
	|>
]


(* EvolutionObject -> its StatesList *)
ComponentMetrics[evo_WolframModelEvolutionObject] :=
	ComponentMetrics[evo["StatesList"]]


(* ::Section:: *)
(*Multiway hypergraph metrics*)


(* ::Subsection:: *)
(*Dimensions*)


(* Multiway graph -> mean over the state-vertices that have an estimate *)
EffectiveDimensionEstimate[g_Graph?DirectedGraphQ] := Module[
  {vals = Select[EffectiveDimensionEstimate /@ Select[VertexList[g], hypergraphStateQ], NumericQ]},
  If[vals === {}, Missing["InsufficientStructure"], N @ Mean[vals]]
]


DimensionVariance[g_Graph?DirectedGraphQ] := Module[
  {vals = Select[DimensionVariance /@ Select[VertexList[g], hypergraphStateQ], NumericQ]},
  If[vals === {}, Missing["InsufficientStructure"], N @ Mean[vals]]
]


(* ::Subsection:: *)
(*Vertex degree and variance*)


DegreeMetrics[g_Graph?DirectedGraphQ] :=
	DegreeMetrics[Select[VertexList[g], hypergraphStateQ]]


(* ::Subsection:: *)
(*Global and local branching*)


BranchingUncertainty[g_Graph?DirectedGraphQ] := Module[
	{outDegrees = Select[VertexOutDegree[g], Positive]},
	If[outDegrees === {},
		<|"OutDegreeEntropy" -> 0., "MeanBranchingStrength" -> 0.,
		  "BranchingVertexFraction" -> 0.|>,
		<|
		"OutDegreeEntropy" -> N @ Entropy[2, outDegrees],
		"MeanBranchingStrength" -> N @ Mean[Log2[outDegrees]],
		(* fraction of non-terminal states that actually branch (out-degree > 1) *)
		"BranchingVertexFraction" -> N[Count[outDegrees, _?(# > 1 &)] / Length[outDegrees]]
		|>
	]
]


(* ::Subsection:: *)
(*State reconvergence*)


ReconvergenceMetrics[g_Graph?DirectedGraphQ, state_ : All] := Module[
	{children, branchPoints, futureCones, makeRow},

	children = GroupBy[List @@@ EdgeRules[g], First -> Last, DeleteDuplicates];

	branchPoints =
	If[
		state === All,
		Keys @ Select[children, Length[#] >= 2 &],
		If[Length @ Lookup[children, Key[state], {}] >= 2, {state}, {}]
	];

	futureCones = AssociationMap[
		Union[{#}, VertexOutComponent[g, #]] &, VertexList[g]];

	makeRow[branchPoint_, pair_] := Module[
		{candidates, score, earliest, distances},

		candidates = Intersection @@ Lookup[futureCones, Key /@ pair, {}];

		If[
			candidates === {},
			<|"BranchPoint" -> branchPoint,
			"BranchChildren" -> pair,
			"ReconvergesQ" -> False,
			"ReconvergenceStates" -> {},
			"EarliestReconvergenceState" -> Missing["None"],
			"StepsAfterBranch" -> Missing["None"]
			|>,

			score[c_] := Max[GraphDistance[g, #, c] & /@ pair];
			earliest = First @ MinimalBy[candidates, score];
			distances = GraphDistance[g, #, earliest] & /@ pair;

			<|"BranchPoint" -> branchPoint,
			"BranchChildren" -> pair,
			"ReconvergesQ" -> True,
			"ReconvergenceStates" -> candidates,
			"EarliestReconvergenceState" -> earliest,
			"BranchDistancesToEarliest" -> distances,
			"StepsAfterBranch" -> Max[distances]
			|>
		]
	];
	Flatten[Table[makeRow[branchPoint, #] & /@
		Subsets[children[branchPoint], {2}], {branchPoint, branchPoints}], 1]
]


ReconvergenceReport[g_Graph?DirectedGraphQ, state_ : All] := Module[
	{locations, flags},

	locations = ReconvergenceMetrics[g, state];
	flags = Lookup[locations, "ReconvergesQ", {}];

	<|
	"ReconvergenceRatio" -> If[flags === {}, 0., N @ Mean[Boole /@ flags]],
	"BranchPairCount" -> Length[flags],
	"ReconvergingBranchPairCount" -> Count[flags, True],
	"ReconvergenceLocations" -> locations
	|>
]


(* ::Subsection:: *)
(*Causal dependencies and events*)


CausalDependencyEntropy[g_Graph?DirectedGraphQ] := Module[
	{dependencies = Select[VertexOutDegree[g], Positive]},
	If[dependencies === {}, 0., N @ Entropy[2, dependencies]]
]


CausalMergeEvents[g_Graph?DirectedGraphQ] := Module[
	{dependencies = VertexInDegree[g], mergedCount},
	mergedCount = Count[dependencies, _?(# >= 2 &)];
	<|
	"CausalMergeEventsCount" -> mergedCount,
	"CausalMergeEventsRatio" ->
		If[dependencies === {}, 0., N[mergedCount / Length[dependencies]]]
	|>
]


(* ::Subsection:: *)
(*Component analysis*)


(* Multiway graph -> graph-level + per-state aggregates *)
ComponentMetrics[g_Graph?DirectedGraphQ] /;
	AnyTrue[VertexList[g], hypergraphStateQ] := Module[
	{states = Select[VertexList[g], hypergraphStateQ],
		stateMetrics, compCounts},

	stateMetrics = ComponentMetrics /@ states;

	compCounts = stateMetrics[[All, "NumberOfConnectedComponents"]];

	<|
	"MultiwayGraphMetrics" -> ComponentMetrics[UndirectedGraph[g]],  (* forces core case *)
	"PerStateMetrics" -> stateMetrics,
	"MaxStateComponentCount" -> Max[compCounts],
	"MeanStateLargestComponentRatio" ->
		N @ Mean[stateMetrics[[All, "LargestComponentRatio"]]]
	|>
]


(* ::Section:: *)
(*Registry variables and functions*)


(* Aggregate helpers used by the registry; guard the empty-states case. *)
statesMaxVertexCount[states_List] :=
  If[states === {}, 0, Max[HypergraphVertexCount /@ states]]

statesMaxEdgeCount[states_List] :=
  If[states === {}, 0, Max[HypergraphEdgeCount /@ states]]

statesMaxEdgeToVertexRatio[states_List] :=
  If[states === {}, 0.,
    Max[
      With[{v = HypergraphVertexCount[#], e = HypergraphEdgeCount[#]},
        If[v === 0, 0., N[e/v]]
      ] & /@ states
    ]
  ]

statesMaxDensity[states_List] :=
  If[states === {}, 0., Max[HypergraphDensity /@ states]]

statesMaxEdgeMultiplicity[states_List] :=
  If[states === {}, 0, Max[EdgeMultiplicityMax /@ states]]


(* Registry specification fields:
     "Input"      -- evaluation input level (see $AllowedMetricInputs);
     "Function"   -- the metric (a second argument receives "Parameters");
     "Direction"  -- "Maximize" | "Minimize" | "Target" | "Range";
     "Stage"      -- "Objective" (Pareto coordinate), "Constraint" (solution
                     feasibility) or "Diagnostic" (reported only);
     "Validator"  -- predicate for an admissible value;
     "ValueType"  -- "Boolean" | "Integer" | "Real" (informational; Boolean
                     constraints need no "Threshold");
     optional "Artifacts", "Parameters", "Target", "Tolerance", "Range",
     "Threshold", "Description". *)
$FitnessMetricRegistry = <|

  "HaltedWithinCapQ" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> Function[TrueQ[#["HaltedWithinCapQ"]]],
    "Direction" -> "Maximize",
    "Stage" -> "Constraint",
    "Validator" -> (MatchQ[#, True | False] &),
    "ValueType" -> "Boolean",
    "Description" -> "True when the exploration halted: the frontier was exhausted and the explored states graph is acyclic."
  |>,

  "MultiwayStateCount" -> <|
    "Input" -> "StatesGraph",
    "Function" -> VertexCount,
    "Direction" -> "Maximize",
    "Stage" -> "Objective",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Number of distinct canonical states explored."
  |>,

  "MultiwayTransitionCount" -> <|
    "Input" -> "StatesGraph",
    "Function" -> EdgeCount,
    "Direction" -> "Maximize",
    "Stage" -> "Objective",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Number of distinct canonical state transitions explored."
  |>,

  "MaxMultiwayFrontierSize" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> Function[Max[Length /@ #["Generations"]]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest number of newly discovered states in one breadth-first generation."
  |>,

  "MultiwayLongestDerivation" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> Function[#["LongestDerivation"]],
    "Direction" -> "Maximize",
    "Stage" -> "Objective",
    "Validator" -> numericOrMissingQ,
    "ValueType" -> "Integer",
    "Description" -> "Length of the longest derivation from the initial state: exact when the system halted, the longest found within the limits otherwise, Missing[\"CyclicStatesGraph\"] when a cycle makes derivations unbounded."
  |>,

  "MultiwayLifetime" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> Function[Max[0, Length[DeleteCases[#["Generations"], {}]] - 1]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Breadth-first discovery depth (non-empty generations minus one); not the longest derivation."
  |>,

  "TerminalStateCount" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> Function[Length[#["FinalStates"]]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Number of verified terminal states (expanded states without successors)."
  |>,

  "NonIsomorphicTerminalStateCount" -> <|
    "Input" -> "EvaluationContext",
    (* FinalStates are already canonical, so distinct means non-isomorphic. *)
    "Function" -> Function[Length[DeleteDuplicates[#["FinalStates"]]]],
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Number of isomorphism classes of verified terminal states."
  |>,

  "HGMaxVerticesCount" -> <|
    "Input" -> "States",
    "Function" -> statesMaxVertexCount,
    "Direction" -> "Maximize",
    "Stage" -> "Objective",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest vertex count over explored states."
  |>,

  "HGMaxEdgesCount" -> <|
    "Input" -> "States",
    "Function" -> statesMaxEdgeCount,
    "Direction" -> "Maximize",
    "Stage" -> "Objective",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest edge count over explored states (multiplicity included in multiset universes)."
  |>,

  "HGMaxEdgeToVertexRatio" -> <|
    "Input" -> "States",
    "Function" -> statesMaxEdgeToVertexRatio,
    (* Range resolved from the configuration's RatioRange at selection time. *)
    "Direction" -> "Range",
    "Stage" -> "Constraint",
    "Validator" -> NumericQ,
    "ValueType" -> "Real",
    "Description" -> "Largest edge-to-vertex ratio over explored states; constrained to RatioRange."
  |>,

  "HGMaxDensity" -> <|
    "Input" -> "States",
    "Function" -> statesMaxDensity,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Real",
    "Description" -> "Largest HypergraphDensity over explored states (distinct edge classes over possible edge classes)."
  |>,

  "HGMaxEdgeMultiplicity" -> <|
    "Input" -> "States",
    "Function" -> statesMaxEdgeMultiplicity,
    "Direction" -> "Maximize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Integer",
    "Description" -> "Largest number of copies of one edge class in an explored state (always 1 in the unordered universe)."
  |>,

  "Runtime" -> <|
    "Input" -> "EvaluationContext",
    "Function" -> Function[#["Runtime"]],
    "Direction" -> "Minimize",
    "Stage" -> "Diagnostic",
    "Validator" -> NumericQ,
    "ValueType" -> "Real",
    "Description" -> "Wall-clock seconds of the multiway evaluation (machine-dependent)."
  |>

|>;


$AllowedMetricInputs = {
  "State",
  "States",
  "FinalStates",
  "StatesGraph",
  "EvolutionGraph",
  "CausalGraph",
  "EventEvolution",
  "UpdateOrderRuns",
  "EvaluationContext"
};


$RequiredMetricSpecificationKeys = {"Input", "Function", "Direction", "Stage", "Validator"};


(* Registration entry point for modules that add metrics. A malformed or
   duplicate registration is a programming error and is thrown at load. *)
registerFitnessMetrics[metrics_Association] := (
  KeyValueMap[
    Function[{name, specification},
      If[
        !StringQ[name] || !AssociationQ[specification] ||
          !SubsetQ[Keys[specification], $RequiredMetricSpecificationKeys] ||
          KeyExistsQ[$FitnessMetricRegistry, name],
        Throw[
          Failure["InvalidMetricRegistration", <|"Metric" -> name|>],
          "registration"
        ]
      ]
    ],
    metrics
  ];
  $FitnessMetricRegistry = Join[$FitnessMetricRegistry, metrics];
)


ValidateFitnessMetricResult[
  name_String,
  specification_Association,
  value_
] := Module[{validator},

  validator = Lookup[specification, "Validator", NumericQ];

  If[
    TrueQ[validator[value]],

    value,

    Failure[
      "InvalidFitnessMetricResult",
      <|
        "Message" ->
          "The fitness metric did not return a value of its declared type.",
        "Metric" -> name,
        "Value" -> value
      |>
    ]
  ]
]
