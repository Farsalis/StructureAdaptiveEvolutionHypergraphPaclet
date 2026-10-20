(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Helpers*)


mutationFailure[strategy_String, rule_, message_String] :=
  Failure[
    "MutationNotApplicable",
    <|
      "Message" -> message,
      "Strategy" -> strategy,
      "Rule" -> rule
    |>
  ]


(* ::Subsection:: *)
(*Multiway evolutions*)


MultiwayEvolutionStates[evolution_List] :=
  Catenate @ DeleteCases[evolution, {}]


MultiwayEvolutionFitness[evolution_List] := Module[
  {states, metrics, vertexCounts, edgeCounts},

  states = MultiwayEvolutionStates[evolution];

  If[states === {},
    Return @ <|
      "HGMaxVerticesCount" -> 0,
      "HGMaxEdgesCount" -> 0,
      "MultiwayStateCount" -> 0,
      "MaxMultiwayFrontierSize" -> 0,
      "MultiwayLifetime" -> 0,
      "HaltedWithinCapQ" -> True
    |>
  ];

  metrics = HypergraphSizeMetrics /@ states;

  vertexCounts =
    Lookup[metrics, "HypergraphVerticesCount"];

  edgeCounts =
    Lookup[metrics, "HypergraphEdgesCount"];

  <|
    "HGMaxVerticesCount" -> Max[vertexCounts],
    "HGMaxEdgesCount" -> Max[edgeCounts],

    "MultiwayStateCount" ->
      Length @ DeleteDuplicates[states],

    "MaxMultiwayFrontierSize" ->
      Max[Length /@ evolution],

    "MultiwayLifetime" ->
      Max[0, Length[DeleteCases[evolution, {}]] - 1],

    "HaltedWithinCapQ" ->
      Last[evolution] === {}
  |>
]


(* ::Section:: *)
(*Growth-budget mutation*)


(* Proposal operator: add one RHS-only variable and 1-2 RHS hyperedges. *)

GrowthBudgetMutation[
  rule_Rule,
  addedEdgesRange_ : {1, 2}
] := Module[
  {lhs, rhs, vars, newVar, arity, addedEdgeCount, newEdges},

  lhs = rule[[1]];
  rhs = rule[[2]];

  vars = DeleteDuplicates @ Flatten[{lhs, rhs}];

  If[
    vars === {} || Join[lhs, rhs] === {},
    Return @ mutationFailure[
      "GrowthBudget",
      rule,
      "The rule has no hyperedges or variables to extend."
    ]
  ];

  newVar = Unique["v"];

  arity = First @ Commonest[Length /@ Join[lhs, rhs]];
  addedEdgeCount = RandomInteger[addedEdgesRange];

  newEdges = DeleteDuplicates @ Table[
    Module[
      {
        (* Sampling with replacement covers rules with fewer distinct
           variables than the target arity. *)
        base = If[Length[vars] >= arity - 1,
          RandomSample[vars, arity - 1],
          RandomChoice[vars, arity - 1]
        ]
      },
      (* Ordered universe: slot positions are semantic, so the fresh
         variable lands in a random slot instead of a sorted tuple. *)
      If[
        $EdgeSymmetry === "Ordered",
        Insert[base, newVar, RandomInteger[{1, Length[base] + 1}]],
        Sort @ Append[base, newVar]
      ]
    ],
    addedEdgeCount
  ];

  lhs -> Join[rhs, newEdges]
];


GrowthBudgetFitness[states_List] := Module[
  {metrics, vertexCounts, edgeCounts, edgeVertexRatios, finalMetrics},

  metrics = HypergraphSizeMetrics /@ states;

  vertexCounts = Lookup[metrics, "HypergraphVerticesCount"];
  edgeCounts = Lookup[metrics, "HypergraphEdgesCount"];
  edgeVertexRatios = Lookup[metrics, "HypergraphEdgeToVertexRatio"];

  finalMetrics = Last[metrics];

  <|
    (* Primary fitness metrics *)
    "HGMaxVerticesCount" -> Max[vertexCounts],
    "HGMaxEdgesCount" -> Max[edgeCounts],
    "HGMaxEdgeToVertexRatio" -> Max[edgeVertexRatios],

    (* Supplemental diagnostics *)
    "FinalVertexCount" -> finalMetrics["HypergraphVerticesCount"],

    "FinalEdgeCount" -> finalMetrics["HypergraphEdgesCount"],

    "FinalDensity" -> finalMetrics["HypergraphDensity"]
  |>
];


(* Optional strategy-local acceptance check; global Pareto selection decides. *)
AcceptGrowthBudgetMutationQ[
  oldFitness_Association,
  newFitness_Association,
  ratioRange_ : {0., Infinity}
] :=
  Between[
    newFitness["HGMaxEdgeToVertexRatio"],
    ratioRange
  ] &&

  newFitness["HGMaxVerticesCount"] >=
    oldFitness["HGMaxVerticesCount"] &&

  newFitness["HGMaxEdgesCount"] >=
    oldFitness["HGMaxEdgesCount"] &&

  (
    newFitness["HGMaxVerticesCount"] >
      oldFitness["HGMaxVerticesCount"] ||

    newFitness["HGMaxEdgesCount"] >
      oldFitness["HGMaxEdgesCount"]
  );


(* Standalone proof-of-concept loop retained for reference/manual use. *)
GrowthBudgetStep[
  rule_Rule,
  evolveFunction_,
  ratioRange_ : {0., Infinity}] := Module[
  {
    candidateRule,
    oldRuntime,
    newRuntime,
    oldStates,
    newStates,
    oldFitness,
    newFitness,
    acceptedQ
  },

  candidateRule = GrowthBudgetMutation[rule];

  If[FailureQ[candidateRule], Return[candidateRule]];

  {oldRuntime, oldStates} =
    AbsoluteTiming[evolveFunction[rule]];

  {newRuntime, newStates} =
    AbsoluteTiming[evolveFunction[candidateRule]];

  oldFitness = Append[
    GrowthBudgetFitness[oldStates],
    "Runtime" -> oldRuntime
  ];

  newFitness = Append[
    GrowthBudgetFitness[newStates],
    "Runtime" -> newRuntime
  ];

  acceptedQ = AcceptGrowthBudgetMutationQ[oldFitness, newFitness, ratioRange];

  <|
    "AcceptedQ" -> acceptedQ,

    "Rule" -> If[acceptedQ, candidateRule, rule],
    "CandidateRule" -> candidateRule,

    "OldFitness" -> oldFitness,
    "NewFitness" -> newFitness
  |>
]


RunGrowthBudgetMutations[
  initialRule_Rule,
  evolveFunction_,
  iterations_Integer : 10,
  tolerance_ : 0.2] := Module[
  {rule = initialRule, baseRatio, ratioRange, result},

  Table[
	  baseRatio = GrowthBudgetFitness[evolveFunction[rule]]["HGMaxEdgeToVertexRatio"];
	  ratioRange =
	      If[baseRatio == 0,
	        {0., 1.},
	        {
	          (1 - tolerance) baseRatio,
	          (1 + tolerance) baseRatio
	        }
	      ];

	  result = GrowthBudgetStep[rule, evolveFunction, ratioRange];
	  rule = result["Rule"];

	    Join[
	      result,
	      <|
	        "Iteration" -> i,
	        "RatioRange" -> ratioRange
	      |>
	    ],
	    {i, iterations}
  ]
];


(* ::Section:: *)
(*Shared proposal operators*)


(* Proposal operator: delete one RHS hyperedge, or a vertex from the last
   remaining edge. Shared by the constrain phase and runtime throttling. *)
deleteRHSEdgeMutation[rule_Rule, strategy_String] := Module[
  {lhs, rhs, edgeIndex, vertexIndex},

  lhs = rule[[1]];
  rhs = rule[[2]];

  Which[
    Length[rhs] > 1,

      lhs -> Delete[
        rhs,
        RandomChoice @ Range @ Length[rhs]
      ],

    Length[rhs] == 1 && Length[First[rhs]] > 1,

      edgeIndex = 1;
      vertexIndex =
        RandomChoice @ Range @ Length[rhs[[edgeIndex]]];

      lhs ->
        ReplacePart[
          rhs,
          edgeIndex ->
            Delete[rhs[[edgeIndex]], vertexIndex]
        ],

    Length[rhs] == 1,

      lhs -> {},

    True,
      mutationFailure[
        strategy,
        rule,
        "The rule right-hand side cannot be reduced further."
      ]
  ]
]


(* Proposal operator: add one LHS hyperedge over existing LHS variables, so the
   match becomes strictly more specific and can starve as the motif gets rarer
   (handoff strategies 2 and 9). *)
AddLHSConditionMutation[rule_Rule] := Module[
  {lhs, rhs, vars, arity, existing, newEdge, attempt},

  lhs = rule[[1]];
  rhs = rule[[2]];

  vars = DeleteDuplicates @ Flatten[lhs];

  If[
    lhs === {} || vars === {},
    Return @ mutationFailure[
      "AddLHSCondition",
      rule,
      "The rule left-hand side has no variables to constrain."
    ]
  ];

  arity = First @ Commonest[Length /@ Join[lhs, rhs]];

  (* Ordered universe: duplicate LHS edges are semantic under multiset
     matching (they demand multiplicity), so any sampled tuple is a genuine
     condition and no duplicate-rejection retry is needed. *)
  If[
    $EdgeSymmetry === "Ordered",
    newEdge = If[
      Length[vars] >= arity,
      RandomSample[vars, arity],
      RandomChoice[vars, arity]
    ];
    Return[Append[lhs, newEdge] -> rhs]
  ];

  existing = Sort /@ lhs;

  (* A duplicate of an existing LHS edge would canonicalize away, so retry a
     few times before giving up. *)
  Do[
    attempt = Sort @ If[
      Length[vars] >= arity,
      RandomSample[vars, arity],
      RandomChoice[vars, arity]
    ];
    If[!MemberQ[existing, attempt], newEdge = attempt; Break[]],
    {5}
  ];

  If[
    !ValueQ[newEdge],
    Return @ mutationFailure[
      "AddLHSCondition",
      rule,
      "No new left-hand-side condition edge could be constructed."
    ]
  ];

  Append[lhs, newEdge] -> rhs
]


(* Try a randomly chosen proposal operator first; fall back to the other one
   when the first is inapplicable to the rule. *)
mixedProposal[rule_Rule, operators : {_, _}] := Module[
  {ordered = RandomSample[operators], result},

  result = First[ordered][rule];
  If[FailureQ[result], Last[ordered][rule], result]
]


(* ::Section:: *)
(*Grow-constrain mutation*)


(* Proposal operator: random phase when none is supplied. *)
GrowThenConstrainMutation[rule_Rule] :=
  GrowThenConstrainMutation[rule, RandomChoice[{"Grow", "Constrain"}]]


GrowThenConstrainMutation[
  rule_Rule,
  "Grow"
] :=
  GrowthBudgetMutation[rule]


(* Constraint phase: shrink the RHS or make the LHS more specific, mixed
   50/50 with fallback when one operator is inapplicable. *)

GrowThenConstrainMutation[
  rule_Rule,
  "Constrain"
] :=
  mixedProposal[
    rule,
    {
      deleteRHSEdgeMutation[#, "GrowThenConstrain"] &,
      AddLHSConditionMutation
    }
  ]


GrowThenConstrainFitness[evolution_List] :=
  MultiwayEvolutionFitness[evolution]


AcceptGrowThenConstrainMutationQ[
  oldFitness_Association,
  newFitness_Association,
  phase_,
  targetVertices_,
  targetEdges_
] :=
  Switch[
    phase,

    "Grow",
      newFitness["HGMaxVerticesCount"] >=
        oldFitness["HGMaxVerticesCount"] &&

      newFitness["HGMaxEdgesCount"] >=
        oldFitness["HGMaxEdgesCount"] &&

      (
        newFitness["HGMaxVerticesCount"] >
          oldFitness["HGMaxVerticesCount"] ||

        newFitness["HGMaxEdgesCount"] >
          oldFitness["HGMaxEdgesCount"]
      ),

    "Constrain",
      TrueQ[newFitness["HaltedWithinCapQ"]] &&

      newFitness["HGMaxVerticesCount"] >= targetVertices &&

      newFitness["HGMaxEdgesCount"] >= targetEdges
      ]


GrowThenConstrainStep[
  rule_Rule,
  evolveFunction_,
  targetVertices_Integer : 20,
  targetEdges_Integer : 20
] := Module[
  {
    phase,
    candidateRule,
    oldRuntime,
    newRuntime,
    oldEvolution,
    newEvolution,
    oldFitness,
    newFitness,
    acceptedQ
  },

  {oldRuntime, oldEvolution} =
    AbsoluteTiming[evolveFunction[rule]];

  oldFitness = Append[
    GrowThenConstrainFitness[oldEvolution],
    "Runtime" -> oldRuntime
  ];

  phase =
    If[
      oldFitness["HGMaxVerticesCount"] < targetVertices ||
      oldFitness["HGMaxEdgesCount"] < targetEdges,
      "Grow",
      "Constrain"
    ];

  candidateRule =
    GrowThenConstrainMutation[rule, phase];

  If[FailureQ[candidateRule], Return[candidateRule]];

  {newRuntime, newEvolution} =
    AbsoluteTiming[evolveFunction[candidateRule]];

  newFitness = Append[
    GrowThenConstrainFitness[newEvolution],
    "Runtime" -> newRuntime
  ];

  acceptedQ =
    AcceptGrowThenConstrainMutationQ[
      oldFitness,
      newFitness,
      phase,
      targetVertices,
      targetEdges
    ];

  <|
    "AcceptedQ" -> acceptedQ,
    "Phase" -> phase,
    "Rule" -> If[acceptedQ, candidateRule, rule],
    "CandidateRule" -> candidateRule,
    "OldFitness" -> oldFitness,
    "NewFitness" -> newFitness
  |>
]


RunGrowThenConstrainMutations[
  initialRule_Rule,
  evolveFunction_,
  iterations_Integer : 10,
  targetVertices_Integer : 20,
  targetEdges_Integer : 20
] := Module[
  {rule = initialRule, result},

  Table[
    result =
      GrowThenConstrainStep[
        rule,
        evolveFunction,
        targetVertices,
        targetEdges
      ];

    rule = result["Rule"];

    Join[
      result,
      <|"Iteration" -> i|>
    ],
    {i, iterations}
  ]
]


(* ::Section:: *)
(*Overlapping-match mutation*)


(* Proposal operator: make the LHS less restrictive, producing more possible matches. *)

OverlappingMatchMutation[rule_Rule] := Module[
  {lhs, rhs, edgeIndex, vertexIndex},

  lhs = rule[[1]];
  rhs = rule[[2]];

  Which[
    Length[lhs] > 1,

	  Delete[
	    lhs,
	    RandomChoice @ Range @ Length[lhs]
	  ] -> rhs,

    lhs =!= {} && Length[First[lhs]] > 1,

      edgeIndex = 1;
      vertexIndex =
        RandomChoice @ Range @ Length[lhs[[edgeIndex]]];

      ReplacePart[
        lhs,
        edgeIndex ->
          Delete[lhs[[edgeIndex]], vertexIndex]
      ] -> rhs,

    True,
      mutationFailure[
        "OverlappingMatch",
        rule,
        "The rule left-hand side cannot be made less restrictive."
      ]
  ]
]


OverlappingMatchFitness[evolution_List] :=
  KeyTake[
    MultiwayEvolutionFitness[evolution],
    {
      "MultiwayStateCount",
      "MaxMultiwayFrontierSize",
      "MultiwayLifetime",
      "HaltedWithinCapQ"
    }
  ]


AcceptOverlappingMatchMutationQ[
  oldFitness_Association,
  newFitness_Association
] :=
  newFitness["MultiwayStateCount"] >=
    oldFitness["MultiwayStateCount"] &&

  newFitness["MaxMultiwayFrontierSize"] >=
    oldFitness["MaxMultiwayFrontierSize"] &&

  (
    newFitness["MultiwayStateCount"] >
      oldFitness["MultiwayStateCount"] ||

    newFitness["MaxMultiwayFrontierSize"] >
      oldFitness["MaxMultiwayFrontierSize"]
  )


OverlappingMatchStep[
  rule_Rule,
  evolveFunction_
] := Module[
  {
    candidateRule,
    oldRuntime,
    newRuntime,
    oldEvolution,
    newEvolution,
    oldFitness,
    newFitness,
    acceptedQ
  },

  candidateRule = OverlappingMatchMutation[rule];

  If[FailureQ[candidateRule], Return[candidateRule]];

  {oldRuntime, oldEvolution} =
    AbsoluteTiming[evolveFunction[rule]];

  {newRuntime, newEvolution} =
    AbsoluteTiming[evolveFunction[candidateRule]];

  oldFitness = Append[
    OverlappingMatchFitness[oldEvolution],
    "Runtime" -> oldRuntime
  ];

  newFitness = Append[
    OverlappingMatchFitness[newEvolution],
    "Runtime" -> newRuntime
  ];

  acceptedQ =
    AcceptOverlappingMatchMutationQ[
      oldFitness,
      newFitness
    ];

  <|
    "AcceptedQ" -> acceptedQ,
    "Rule" -> If[acceptedQ, candidateRule, rule],
    "CandidateRule" -> candidateRule,
    "OldFitness" -> oldFitness,
    "NewFitness" -> newFitness
  |>
]


RunOverlappingMatchMutations[
  initialRule_Rule,
  evolveFunction_,
  iterations_Integer : 10
] := Module[
  {rule = initialRule, result},

  Table[
    result =
      OverlappingMatchStep[rule, evolveFunction];

    rule = result["Rule"];

    Join[
      result,
      <|"Iteration" -> i|>
    ],
    {i, iterations}
  ]
]


(* ::Section:: *)
(*Delayed-termination mutation*)


(* Proposal operator: one small RHS growth mutation. The fitness test decides
   whether it actually increases lifetime while still terminating. *)

(* Small RHS growth or a new LHS condition, mixed 50/50 with fallback, so the
   strategy can also propose termination by match starvation. *)
DelayedTerminationMutation[rule_Rule] :=
  mixedProposal[
    rule,
    {
      GrowthBudgetMutation[#, {1, 1}] &,
      AddLHSConditionMutation
    }
  ]


DelayedTerminationFitness[evolution_List] :=
  KeyTake[
    MultiwayEvolutionFitness[evolution],
    {
      "MultiwayLifetime",
      "MultiwayStateCount",
      "HGMaxVerticesCount",
      "HGMaxEdgesCount",
      "HaltedWithinCapQ"
    }
  ]


AcceptDelayedTerminationMutationQ[
  oldFitness_Association,
  newFitness_Association
] :=
  TrueQ[newFitness["HaltedWithinCapQ"]] &&

  newFitness["MultiwayLifetime"] >
    oldFitness["MultiwayLifetime"] &&

  newFitness["MultiwayStateCount"] >=
    oldFitness["MultiwayStateCount"]


DelayedTerminationStep[
  rule_Rule,
  evolveFunction_
] := Module[
  {
    candidateRule,
    oldRuntime,
    newRuntime,
    oldEvolution,
    newEvolution,
    oldFitness,
    newFitness,
    acceptedQ
  },

  candidateRule =
    DelayedTerminationMutation[rule];

  If[FailureQ[candidateRule], Return[candidateRule]];

  {oldRuntime, oldEvolution} =
    AbsoluteTiming[evolveFunction[rule]];

  {newRuntime, newEvolution} =
    AbsoluteTiming[evolveFunction[candidateRule]];

  oldFitness = Append[
    DelayedTerminationFitness[oldEvolution],
    "Runtime" -> oldRuntime
  ];

  newFitness = Append[
    DelayedTerminationFitness[newEvolution],
    "Runtime" -> newRuntime
  ];

  acceptedQ =
    AcceptDelayedTerminationMutationQ[
      oldFitness,
      newFitness
    ];

  <|
    "AcceptedQ" -> acceptedQ,
    "Rule" -> If[acceptedQ, candidateRule, rule],
    "CandidateRule" -> candidateRule,
    "OldFitness" -> oldFitness,
    "NewFitness" -> newFitness
  |>
]


RunDelayedTerminationMutations[
  initialRule_Rule,
  evolveFunction_,
  iterations_Integer : 10
] := Module[
  {rule = initialRule, result},

  Table[
    result =
      DelayedTerminationStep[rule, evolveFunction];

    rule = result["Rule"];

    Join[
      result,
      <|"Iteration" -> i|>
    ],
    {i, iterations}
  ]
]


(* ::Section:: *)
(*Runtime-throttling mutation*)


(* Proposal operator: reduce RHS structure to lower growth and matching cost. *)

RuntimeThrottlingMutation[rule_Rule] :=
  deleteRHSEdgeMutation[rule, "RuntimeThrottling"]


RuntimeThrottlingFitness[evolution_List] :=
  KeyTake[
    MultiwayEvolutionFitness[evolution],
    {
      "MultiwayStateCount",
      "MultiwayLifetime",
      "HGMaxVerticesCount",
      "HGMaxEdgesCount",
      "HaltedWithinCapQ"
    }
  ]


AcceptRuntimeThrottlingMutationQ[
  oldFitness_Association,
  newFitness_Association,
  retainedStateFraction_ : 0.5
] :=
  newFitness["Runtime"] <
    oldFitness["Runtime"] &&

  newFitness["MultiwayStateCount"] >=
    retainedStateFraction oldFitness["MultiwayStateCount"] &&

  (
    !TrueQ[oldFitness["HaltedWithinCapQ"]] ||
    TrueQ[newFitness["HaltedWithinCapQ"]]
  );


RuntimeThrottlingStep[
  rule_Rule,
  evolveFunction_,
  retainedStateFraction_ : 0.5
] := Module[
  {
    candidateRule,
    oldRuntime,
    newRuntime,
    oldEvolution,
    newEvolution,
    oldFitness,
    newFitness,
    acceptedQ
  },

  candidateRule =
    RuntimeThrottlingMutation[rule];

  If[FailureQ[candidateRule], Return[candidateRule]];

  {oldRuntime, oldEvolution} =
    AbsoluteTiming[evolveFunction[rule]];

  {newRuntime, newEvolution} =
    AbsoluteTiming[evolveFunction[candidateRule]];

  oldFitness = Append[
    RuntimeThrottlingFitness[oldEvolution],
    "Runtime" -> oldRuntime
  ];

  newFitness = Append[
    RuntimeThrottlingFitness[newEvolution],
    "Runtime" -> newRuntime
  ];

  acceptedQ =
    AcceptRuntimeThrottlingMutationQ[
      oldFitness,
      newFitness,
      retainedStateFraction
    ];

  <|
    "AcceptedQ" -> acceptedQ,
    "Rule" -> If[acceptedQ, candidateRule, rule],
    "CandidateRule" -> candidateRule,
    "OldFitness" -> oldFitness,
    "NewFitness" -> newFitness
  |>
]


RunRuntimeThrottlingMutations[
  initialRule_Rule,
  evolveFunction_,
  iterations_Integer : 10,
  retainedStateFraction_ : 0.5
] := Module[
  {rule = initialRule, result},

  Table[
    result =
      RuntimeThrottlingStep[
        rule,
        evolveFunction,
        retainedStateFraction
      ];

    rule = result["Rule"];

    Join[
      result,
      <|
        "Iteration" -> i,
        "RetainedStateFraction" -> retainedStateFraction
      |>
    ],
    {i, iterations}
  ]
]


(* ::Section:: *)
(*Variable-rewiring mutation*)


(* Point mutation: merge two distinct variables everywhere in the rule. *)
IdentifyVariablesMutation[rule_Rule] := Module[
  {vars, pair},

  vars = DeleteDuplicates @ Flatten[Join[rule[[1]], rule[[2]]]];

  If[
    Length[vars] < 2,
    Return @ mutationFailure[
      "VariableRewiring",
      rule,
      "The rule has fewer than two distinct variables to identify."
    ]
  ];

  pair = RandomSample[vars, 2];
  rule /. pair[[2]] -> pair[[1]]
]


(* Point mutation: replace one occurrence of a repeated variable with a fresh
   variable. *)
SplitVariableMutation[rule_Rule] := Module[
  {sides, counts, splittable, var, positions, target},

  sides = {rule[[1]], rule[[2]]};

  counts = Counts @ Flatten[sides];
  splittable = Keys @ Select[counts, # >= 2 &];

  If[
    splittable === {},
    Return @ mutationFailure[
      "VariableRewiring",
      rule,
      "No variable occurs more than once, so none can be split."
    ]
  ];

  var = RandomChoice[splittable];
  positions = Position[sides, var, {3}, Heads -> False];
  target = RandomChoice[positions];

  sides = ReplacePart[sides, target -> Unique["v"]];
  sides[[1]] -> sides[[2]]
]


(* Proposal operator: the fine-grained rewiring move -- identify or split a
   variable, keeping the rule's edge counts and arities fixed. *)
VariableRewiringMutation[rule_Rule] :=
  mixedProposal[
    rule,
    {IdentifyVariablesMutation, SplitVariableMutation}
  ]


(* ::Section:: *)
(*Ordered edge permutation mutation*)


(* Proposal operator: permute vertex positions inside one ordered rule edge
   (ordered-hypergraph addendum, section 3). Only positions in the selected
   edge change; edge counts, arities, and the vertex-occurrence multiset are
   conserved. Returns the mutated rule together with provenance details. *)
OrderedEdgePermutationMutation[rule_Rule] :=
  OrderedEdgePermutationMutation[rule, Automatic]

OrderedEdgePermutationMutation[
  rule_Rule,
  sideSpec : "Left" | "Right" | Automatic
] := Module[
  {sides, targetSides, eligible, side, index, edge, permutation, newEdge, mutated, result = None},

  If[
    $EdgeSymmetry =!= "Ordered",
    Return @ mutationFailure[
      "OrderedEdgePermutation",
      rule,
      "Ordered edge permutation requires the ordered universe (\"EdgeSymmetry\" -> \"Ordered\")."
    ]
  ];

  sides = <|"Left" -> rule[[1]], "Right" -> rule[[2]]|>;
  targetSides = If[sideSpec === Automatic, {"Left", "Right"}, {sideSpec}];

  (* Permutable: arity >= 2 and at least two distinct symbols, otherwise no
     nonidentity permutation can change the tuple. *)
  eligible = Join @@ Map[
    Function[targetSide,
      {targetSide, #} & /@ Select[
        Range @ Length @ sides[targetSide],
        Length[sides[targetSide][[#]]] >= 2 &&
          Length[DeleteDuplicates @ sides[targetSide][[#]]] >= 2 &
      ]
    ],
    targetSides
  ];

  If[
    eligible === {},
    Return @ mutationFailure[
      "OrderedEdgePermutation",
      rule,
      "The rule has no permutable edge on the requested side."
    ]
  ];

  Do[
    {side, index} = RandomChoice[eligible];
    edge = sides[side][[index]];

    (* Draw a nonidentity syntactic permutation of the slot positions. *)
    newEdge = edge;
    Do[
      permutation = RandomSample @ Range @ Length[edge];
      newEdge = edge[[permutation]];
      If[newEdge =!= edge, Break[]],
      {5}
    ];

    If[
      newEdge =!= edge,
      mutated = If[
        side === "Left",
        ReplacePart[rule[[1]], index -> newEdge] -> rule[[2]],
        rule[[1]] -> ReplacePart[rule[[2]], index -> newEdge]
      ];
      (* Reject canonical no-ops, e.g. permutations that amount to a global
         relabeling; retry with a fresh draw. *)
      If[
        CanonicalRuleForm[mutated] =!= CanonicalRuleForm[rule],
        result = <|
          "Rule" -> mutated,
          "Details" -> <|
            "Side" -> side,
            "EdgeIndex" -> index,
            "OldEdge" -> edge,
            "NewEdge" -> newEdge,
            "Permutation" -> permutation
          |>
        |>;
        Break[]
      ]
    ],
    {5}
  ];

  If[
    AssociationQ[result],
    result,
    mutationFailure[
      "OrderedEdgePermutation",
      rule,
      "No canonically distinct edge permutation was found."
    ]
  ]
]


(* ::Section:: *)
(*Registry variables and functions*)


$MutationStrategyRegistry = <|

  "GrowthBudget" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> GrowthBudgetMutation,
    "Operators" -> {"AddRHSVariable", "AddRHSEdge"},
    "DefaultOptions" -> <|"AddedEdgesRange" -> {1, 2}|>,
    "RequiredMetrics" -> {
      "HGMaxVerticesCount",
      "HGMaxEdgesCount",
      "HGMaxEdgeToVertexRatio"
    }
  |>,

  "OverlappingMatch" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> OverlappingMatchMutation,
    "Operators" -> {"DeleteLHSCondition"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {
      "MultiwayStateCount"
    }
  |>,

  "GrowThenConstrain" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> GrowThenConstrainMutation,
    "Operators" -> {"AddRHSVariable", "AddRHSEdge", "DeleteRHSEdge", "AddLHSCondition"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {
      "HaltedWithinCapQ",
      "MultiwayStateCount",
      "HGMaxVerticesCount",
      "HGMaxEdgesCount"
    }
  |>,

  "DelayedTermination" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> DelayedTerminationMutation,
    "Operators" -> {"AddRHSVariable", "AddRHSEdge", "AddLHSCondition"},
    "DefaultOptions" -> <|"AddedEdgesRange" -> {1, 1}|>,
    "RequiredMetrics" -> {
      "HaltedWithinCapQ"
    }
  |>,

  "RuntimeThrottling" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> RuntimeThrottlingMutation,
    "Operators" -> {"DeleteRHSEdge", "ReduceArity"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {
      "Runtime",
      "MultiwayStateCount"
    }
  |>,

  "VariableRewiring" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> VariableRewiringMutation,
    "Operators" -> {"IdentifyVariables", "SplitVariable"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {}
  |>,

  "OrderedEdgePermutation" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> OrderedEdgePermutationMutation,
    "Operators" -> {"PermuteEdge"},
    "DefaultOptions" -> <|"Side" -> Automatic|>,
    "RequiredMetrics" -> {},
    "RequiredEdgeSymmetry" -> "Ordered"
  |>
|>;
