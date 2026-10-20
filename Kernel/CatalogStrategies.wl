(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context, after
   MutationStrategies.wl (mutationFailure, recordOperator, the strategy
   registry and the core operators), Configurations.wl (registerGoalPresets),
   SeedCanonicalization.wl (universes, rule sets, CanonicalRuleForm) and
   ExtendedMetrics.wl (the metrics named by the strategies below).

   The ten FUTURE strategies of the approved fifteen-strategy catalog
   (handoff section 22: catalog numbers 3, 4, 5, 7, 8, 10, 12, 13, 14, 15)
   with their proposal operators. The strategies are opt-in: no default goal
   preset recommends them; each strategy has its own goal preset of the same
   name (see the end of this file). *)


(* ::Section:: *)
(*Helpers*)


(* Universe-aware identity of one edge: sorted slots (unordered), the least
   tuple of the slot orbit (declared), the tuple itself (ordered). *)
catalogEdgeKey[edge_List] :=
  Switch[
    $EdgeSymmetry,
    "Unordered", Sort[edge],
    "Declared", declaredEdgeRepresentative[edge],
    _, edge
  ]


(* A side as its edge keys: a set in the unordered universe (duplicate edges
   are dropped there), a sorted multiset in the ordered and declared ones. *)
catalogSideKeys[edges_List] :=
  If[
    $EdgeSymmetry === "Unordered",
    Union[catalogEdgeKey /@ edges],
    Sort[catalogEdgeKey /@ edges]
  ]


(* Multiset difference by edge key: the edges of the first list that are not
   matched one-to-one by an edge of the second. *)
catalogEdgeComplement[edges_List, remove_List] := Module[
  {pool = catalogEdgeKey /@ remove, position},
  Select[
    edges,
    Function[edge,
      position = FirstPosition[pool, Verbatim[catalogEdgeKey[edge]], None, {1}, Heads -> False];
      If[position === None, True, pool = Delete[pool, position]; False]
    ]
  ]
]


catalogVariables[lhs_List, rhs_List] := DeleteDuplicates @ Flatten[{lhs, rhs}]


(* Commonest edge arity (2 for an edgeless rule). *)
catalogArity[edges_List] := If[edges === {}, 2, First @ Commonest[Length /@ edges]]


(* Incidence degree on one side: the number of edges containing a variable. *)
catalogDegrees[edges_List] := Counts @ Catenate[DeleteDuplicates /@ edges]

catalogMaxDegree[edges_List] := Max[0, Values @ catalogDegrees[edges]]


(* The most reused variables of one side; empty when no variable lies in at
   least `minimum` edges. *)
catalogHubs[edges_List, minimum_Integer : 1] :=
  With[{degrees = catalogDegrees[edges]},
    If[
      degrees === <||> || Max[degrees] < minimum,
      {},
      Keys @ Select[degrees, # === Max[degrees] &]
    ]
  ]


(* Variables are adjacent when they share an edge of the side. *)
catalogGraph[edges_List] :=
  Graph[
    DeleteDuplicates @ Flatten[edges],
    DeleteDuplicates @ Catenate[UndirectedEdge @@@ Subsets[DeleteDuplicates[#], {2}] & /@ edges]
  ]

catalogComponents[edges_List] :=
  If[Flatten[edges] === {}, {}, ConnectedComponents @ catalogGraph[edges]]


catalogFresh[] := Unique["v"]


(* An edge of the given arity that begins with the anchors; missing slots are
   filled from the pool (with replacement), or with fresh variables when the
   pool is empty. *)
catalogEdge[anchors_List, arity_Integer, pool_List : {}] :=
  Which[
    Length[anchors] >= arity, Take[anchors, arity],
    pool === {}, Join[anchors, Table[catalogFresh[], arity - Length[anchors]]],
    True, Join[anchors, RandomChoice[pool, arity - Length[anchors]]]
  ]


(* Exchange two variables throughout a side. *)
catalogSwap[edges_List, a_, b_] := Replace[edges, {a -> b, b -> a}, {2}]


(* A copy of a rule over fresh variables: rule-set members keep their own
   variables. *)
catalogRenameApart[lhs_ -> rhs_] :=
  With[{renaming = Map[# -> catalogFresh[] &, catalogVariables[lhs, rhs]]},
    Replace[lhs, renaming, {2}] -> Replace[rhs, renaming, {2}]
  ]


catalogProposalRule[proposal_Association] := Lookup[proposal, "Rule", $Failed]
catalogProposalRule[proposal_] := proposal


catalogFailureMessage[Failure[_, data_Association]] :=
  Lookup[data, "Message", "The operator is not applicable."]
catalogFailureMessage[_] := "The operator is not applicable."


(* Identity used for novelty checks: the canonical rule (set) form, after
   dropping duplicate RHS edges in the unordered universe. States are simple
   hypergraphs there, so a duplicated RHS edge changes no evolution, while
   CanonicalRuleForm keeps rule-edge multiplicity. (A duplicated LHS edge is
   kept: it can change whether the rule matches at all.) *)
catalogSimpleRule[lhs_List -> rhs_List] :=
  If[
    $EdgeSymmetry === "Unordered",
    lhs -> DeleteDuplicatesBy[rhs, Sort],
    lhs -> rhs
  ]

catalogIdentity[rule_Rule] := CanonicalRuleForm[catalogSimpleRule[rule]]
catalogIdentity[rules : {__Rule}] := CanonicalRuleForm[catalogSimpleRule /@ rules]
catalogIdentity[_] := $Failed


(* Run a randomized operator draw up to `attempts` times and keep the first
   proposal that is a valid rule specification, differs from the input in
   catalogIdentity and passes acceptQ. Each draw records its operators in an
   isolated trace; only the accepted draw's records reach the proposal's
   AppliedOperators, so a failed or rejected attempt records nothing. *)
catalogRetry[strategy_String, spec_, draw_, attempts_Integer, acceptQ_, message_String] := Module[
  {reference = catalogIdentity[spec], failure = None, result = None, attempt, trace, proposed, form},
  Do[
    {attempt, trace} = Block[
      {$operatorTrace = If[ListQ[$operatorTrace], {}, None]},
      {draw[spec], $operatorTrace}
    ];
    If[
      FailureQ[attempt],
      failure = attempt,
      proposed = catalogProposalRule[attempt];
      form = If[validRuleSpecQ[proposed], catalogIdentity[proposed], $Failed];
      If[
        !FailureQ[form] && form =!= reference && TrueQ[acceptQ[proposed]],
        If[ListQ[$operatorTrace] && ListQ[trace], $operatorTrace = Join[$operatorTrace, trace]];
        result = attempt;
        Break[]
      ]
    ],
    {attempts}
  ];
  Which[
    result =!= None, result,
    failure =!= None, mutationFailure[strategy, spec, catalogFailureMessage[failure]],
    True, mutationFailure[strategy, spec, message]
  ]
]


(* An operator: a draw run through catalogRetry. *)
catalogOperator[strategy_String, draw_, attempts_Integer, acceptQ_ : (True &)][spec_] :=
  catalogRetry[
    strategy, spec, draw, attempts, acceptQ,
    "No valid, canonically new proposal was found."
  ]


(* A core operator (IdentifyVariablesMutation, SplitVariableMutation) used by
   a catalog strategy: validated, checked for canonical novelty, and its
   failures reported under the catalog strategy's name. *)
catalogCoreOperator[strategy_String, function_][rule_Rule] :=
  catalogOperator[strategy, function, 3][rule]


(* Slot permutation of one edge through the core OrderedEdgePermutation
   operator, recorded under the catalog operator name. Only ordered and
   declared universes have slot order to permute. *)
catalogPermutationOperator[strategy_String, operator_String, side_][rule_Rule] := Module[
  {result},
  result = Block[{$operatorTrace = None}, OrderedEdgePermutationMutation[rule, side]];
  If[
    AssociationQ[result] && validHypergraphRuleQ[Lookup[result, "Rule"]],
    recordOperator[operator, result["Details"]];
    result["Rule"],
    mutationFailure[strategy, rule, catalogFailureMessage[result]]
  ]
]


(* A single-rule operator applied to one member of a rule set (members tried
   in random order); the member index goes into the proposal details. *)
catalogOnMember[operator_][rule_Rule] := operator[rule]

catalogOnMember[operator_][rules : {__Rule}] := Module[{result = None},
  Do[
    result = operator[rules[[index]]];
    If[
      !FailureQ[result],
      Return[
        <|
          "Rule" -> ReplacePart[rules, index -> catalogProposalRule[result]],
          "Details" -> <|"RuleSetMember" -> index|>
        |>,
        Module
      ]
    ],
    {index, RandomSample @ Range @ Length[rules]}
  ];
  result
]


(* Strategy-level mixing: operators in random order, the first applicable one
   wins. *)
catalogFirstApplicable[strategy_String, spec_, operators_List] := Module[
  {messages = {}, result},
  Do[
    result = operator[spec];
    If[!FailureQ[result], Return[result, Module]];
    AppendTo[messages, catalogFailureMessage[result]],
    {operator, RandomSample[operators]}
  ];
  mutationFailure[
    strategy,
    spec,
    "No operator of the strategy applies: " <> StringRiffle[DeleteDuplicates[messages], " "]
  ]
]


(* ::Section:: *)
(*Operators*)


(* ::Subsection:: *)
(*SymmetrizeRHS (catalog 3, 8, 15)*)


(* Close the RHS under the exchange of two interchangeable variables: two
   LHS variables whose exchange maps the LHS onto itself (so different
   matches of the same edges produce the same result), or two RHS-only
   variables; the exchange must not already fix the RHS. The images of the
   RHS edges that are missing are added, so the exchange becomes a symmetry
   of the RHS. Without such a pair, an RHS-only variable gets a fresh twin
   that repeats its neighbourhood (a repeated local template). *)
symmetrizeRHSDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {lhsVars, rhsOnly, pairs, pair, twin = False, added},
  lhsVars = DeleteDuplicates @ Flatten[lhs];
  rhsOnly = Select[DeleteDuplicates @ Flatten[rhs], !MemberQ[lhsVars, #] &];
  pairs = Select[
    Join[Subsets[lhsVars, {2}], Subsets[rhsOnly, {2}]],
    catalogSideKeys[catalogSwap[lhs, #[[1]], #[[2]]]] === catalogSideKeys[lhs] &&
      catalogSideKeys[catalogSwap[rhs, #[[1]], #[[2]]]] =!= catalogSideKeys[rhs] &
  ];
  Which[
    pairs =!= {},
      pair = RandomChoice[pairs],
    rhsOnly =!= {},
      pair = {RandomChoice[rhsOnly], catalogFresh[]};
      twin = True,
    True,
      Return[
        mutationFailure[
          strategy,
          lhs -> rhs,
          "No exchange of interchangeable variables changes the right-hand side, and no right-hand-side-only variable can be twinned."
        ],
        Module
      ]
  ];
  added = catalogEdgeComplement[catalogSwap[rhs, pair[[1]], pair[[2]]], rhs];
  If[$EdgeSymmetry === "Unordered", added = DeleteDuplicatesBy[added, catalogEdgeKey]];
  recordOperator["SymmetrizeRHS", <|"Exchange" -> pair, "Twin" -> twin, "AddedEdges" -> added|>];
  lhs -> Join[rhs, added]
]


(* ::Subsection:: *)
(*BoundaryPreserveRHS, DeleteDisconnectedRHS (catalog 4, 8, 15)*)


(* Make every RHS component contain an LHS variable and every LHS variable
   survive on the RHS: each floating component is attached by one edge to a
   boundary variable (preferring dropped ones), then every still-dropped LHS
   variable is joined to an RHS variable. Fragment-free rewriting: the new
   structure stays connected to the matched boundary. *)
boundaryPreserveRHSDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {lhsVars, rhsVars, floating, missing, restored, arity, added = {}, anchor, pool, partner},
  lhsVars = DeleteDuplicates @ Flatten[lhs];
  If[
    lhsVars === {},
    Return[mutationFailure[strategy, lhs -> rhs, "The rule has no left-hand-side variables to preserve."], Module]
  ];
  rhsVars = DeleteDuplicates @ Flatten[rhs];
  floating = Select[catalogComponents[rhs], Intersection[#, lhsVars] === {} &];
  missing = Select[lhsVars, !MemberQ[rhsVars, #] &];
  If[
    floating === {} && missing === {},
    Return[
      mutationFailure[
        strategy,
        lhs -> rhs,
        "Every right-hand-side component contains a left-hand-side variable and every left-hand-side variable survives."
      ],
      Module
    ]
  ];
  restored = missing;
  arity = Max[2, catalogArity[Join[lhs, rhs]]];
  Do[
    If[
      missing =!= {},
      anchor = RandomChoice[missing];
      missing = DeleteCases[missing, anchor],
      anchor = RandomChoice[lhsVars]
    ];
    AppendTo[added, catalogEdge[{anchor, RandomChoice[component]}, arity, Append[component, anchor]]],
    {component, floating}
  ];
  Do[
    rhsVars = DeleteDuplicates @ Flatten[{rhs, added}];
    If[
      !MemberQ[rhsVars, var],
      pool = DeleteCases[rhsVars, var];
      If[pool === {}, pool = DeleteCases[lhsVars, var]];
      partner = If[pool === {}, var, RandomChoice[pool]];
      AppendTo[added, catalogEdge[{var, partner}, arity, {var, partner}]]
    ],
    {var, missing}
  ];
  recordOperator[
    "BoundaryPreserveRHS",
    <|"AttachedComponents" -> floating, "RestoredVariables" -> restored, "AddedEdges" -> added|>
  ];
  lhs -> Join[rhs, added]
]


(* Delete every RHS edge of a component that contains no LHS variable. *)
deleteDisconnectedRHSDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {lhsVars, floatingVertices, removed},
  lhsVars = DeleteDuplicates @ Flatten[lhs];
  If[
    lhsVars === {},
    Return[mutationFailure[strategy, lhs -> rhs, "The rule has no left-hand-side variables."], Module]
  ];
  floatingVertices = Catenate @ Select[catalogComponents[rhs], Intersection[#, lhsVars] === {} &];
  If[
    floatingVertices === {},
    Return[
      mutationFailure[strategy, lhs -> rhs, "The right-hand side has no component without a left-hand-side variable."],
      Module
    ]
  ];
  removed = Select[rhs, Intersection[#, floatingVertices] =!= {} &];
  recordOperator["DeleteDisconnectedRHS", <|"RemovedEdges" -> removed|>];
  lhs -> Select[rhs, Intersection[#, floatingVertices] === {} &]
]


(* ::Subsection:: *)
(*AddMotif (catalog 5)*)


(* Attach an asymmetric terminal motif at one variable: a pendant edge, a
   pendant path of two edges, or a loop. *)
addMotifDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {vars, anchor, arity, motif, fresh, edges},
  vars = catalogVariables[lhs, rhs];
  If[
    vars === {},
    Return[mutationFailure[strategy, lhs -> rhs, "The rule has no variable to attach a motif to."], Module]
  ];
  anchor = RandomChoice[vars];
  arity = Max[2, catalogArity[Join[lhs, rhs]]];
  motif = RandomChoice[{"Pendant", "PendantPath", "Loop"}];
  edges = Switch[
    motif,
    "Pendant", {catalogEdge[{anchor}, arity]},
    "PendantPath",
      fresh = catalogFresh[];
      {catalogEdge[{anchor, fresh}, arity], catalogEdge[{fresh}, arity]},
    "Loop", {ConstantArray[anchor, arity]}
  ];
  recordOperator["AddMotif", <|"Motif" -> motif, "Anchor" -> anchor, "Edges" -> edges|>];
  lhs -> Join[rhs, edges]
]


(* ::Subsection:: *)
(*AddCycleMotif, AddChainMotif, ConservationMutate (catalog 7)*)


(* Close a 3- or 4-cycle: an edge between two RHS variables at RHS distance
   2 or 3, oriented against the path (x -> z -> y gives y -> x). Without such
   a pair, a fresh triangle through one variable. *)
addCycleMotifDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {arity, vertices, graph, pairs, pair, edges, anchor, first, second},
  arity = Max[2, catalogArity[Join[lhs, rhs]]];
  vertices = DeleteDuplicates @ Flatten[rhs];
  pairs = If[
    Length[vertices] < 3,
    {},
    graph = catalogGraph[rhs];
    Select[Subsets[vertices, {2}], MemberQ[{2, 3}, GraphDistance[graph, #[[1]], #[[2]]]] &]
  ];
  If[
    pairs =!= {},
    pair = RandomChoice[pairs];
    edges = {catalogEdge[Reverse[pair], arity, vertices]};
    recordOperator["AddCycleMotif", <|"Closes" -> pair, "Edges" -> edges|>],

    vertices = catalogVariables[lhs, rhs];
    If[
      vertices === {},
      Return[mutationFailure[strategy, lhs -> rhs, "The rule has no variable to anchor a cycle at."], Module]
    ];
    anchor = RandomChoice[vertices];
    {first, second} = {catalogFresh[], catalogFresh[]};
    edges = {
      catalogEdge[{anchor, first}, arity],
      catalogEdge[{first, second}, arity],
      catalogEdge[{second, anchor}, arity]
    };
    recordOperator["AddCycleMotif", <|"Anchor" -> anchor, "Edges" -> edges|>]
  ];
  lhs -> Join[rhs, edges]
]


(* Grow a chain: subdivide one RHS edge at its last slot through a fresh
   vertex ({a, b} becomes {a, f}, {f, b}; degrees of a and b unchanged).
   Without an RHS edge to subdivide, a two-edge chain through a fresh vertex
   between two variables. *)
addChainMotifDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {arity, candidates, index, edge, fresh, edges, vars, ends},
  arity = Max[2, catalogArity[Join[lhs, rhs]]];
  candidates = Select[Range @ Length[rhs], Length[rhs[[#]]] >= 2 &];
  fresh = catalogFresh[];
  If[
    candidates =!= {},
    index = RandomChoice[candidates];
    edge = rhs[[index]];
    edges = {ReplacePart[edge, -1 -> fresh], catalogEdge[{fresh, Last[edge]}, arity, Most[edge]]};
    recordOperator["AddChainMotif", <|"Subdivided" -> edge, "Vertex" -> fresh, "Edges" -> edges|>];
    lhs -> Join[Delete[rhs, index], edges],

    vars = catalogVariables[lhs, rhs];
    If[
      vars === {},
      Return[mutationFailure[strategy, lhs -> rhs, "The rule has no variable to grow a chain from."], Module]
    ];
    ends = If[Length[vars] >= 2, RandomSample[vars, 2], {First[vars], First[vars]}];
    edges = {catalogEdge[{ends[[1]], fresh}, arity], catalogEdge[{fresh, ends[[2]]}, arity]};
    recordOperator["AddChainMotif", <|"Ends" -> ends, "Vertex" -> fresh, "Edges" -> edges|>];
    lhs -> Join[rhs, edges]
  ]
]


(* Rewire one RHS slot to another existing variable while conserving the
   per-event growth budget: the LHS, the RHS edge count (no duplicate edge in
   the unordered universe) and the number of RHS-only (created) variables are
   unchanged, so the edges and vertices created per event stay the same. *)
conservationMutateDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {lhsVars, vars, occurrences, slots, slot, old, new, newRHS},
  lhsVars = DeleteDuplicates @ Flatten[lhs];
  vars = catalogVariables[lhs, rhs];
  occurrences = Counts @ Flatten[rhs];
  (* The only occurrence of an RHS-only variable cannot move: that would
     lower the number of created vertices. *)
  slots = Select[
    Position[rhs, _, {2}, Heads -> False],
    With[{var = Extract[rhs, #]}, MemberQ[lhsVars, var] || occurrences[var] >= 2] &
  ];
  If[
    slots === {} || Length[vars] < 2,
    Return[
      mutationFailure[strategy, lhs -> rhs, "No right-hand-side slot can be rewired without changing the growth budget."],
      Module
    ]
  ];
  slot = RandomChoice[slots];
  old = Extract[rhs, slot];
  new = RandomChoice @ DeleteCases[vars, old];
  newRHS = ReplacePart[rhs, slot -> new];
  If[
    Length[catalogSideKeys[newRHS]] =!= Length[catalogSideKeys[rhs]],
    Return[mutationFailure[strategy, lhs -> rhs, "The rewired edge duplicates an existing edge."], Module]
  ];
  recordOperator["ConservationMutate", <|"Position" -> Prepend[slot, 2], "OldVariable" -> old, "NewVariable" -> new|>];
  lhs -> newRHS
]


(* Mesh guard: no proposal may raise the largest RHS incidence degree above
   the cap (or above the parent's, when the parent already exceeds it). *)
catalogDegreeCapQ[rule_Rule, cap_][proposal_Rule] :=
  catalogMaxDegree[proposal[[2]]] <= Max[cap, catalogMaxDegree[rule[[2]]]]

catalogDegreeCapQ[_, _][_] := False


(* ::Subsection:: *)
(*PreserveMotif, AddStableSubstructure (catalog 10)*)


(* Keep one consumed LHS edge on the RHS, so the matched motif persists. *)
preserveMotifDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {consumed, edge},
  consumed = catalogEdgeComplement[lhs, rhs];
  If[
    consumed === {},
    Return[mutationFailure[strategy, lhs -> rhs, "Every left-hand-side edge already survives on the right-hand side."], Module]
  ];
  edge = RandomChoice[consumed];
  recordOperator["PreserveMotif", <|"Edge" -> edge|>];
  lhs -> Append[rhs, edge]
]


(* Require a new edge over LHS variables (loops allowed) and write it back
   unchanged: a stable substructure next to the rewritten region. *)
addStableSubstructureDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {vars, edge},
  vars = DeleteDuplicates @ Flatten[lhs];
  If[
    vars === {},
    Return[mutationFailure[strategy, lhs -> rhs, "The rule left-hand side has no variables to build a substructure over."], Module]
  ];
  edge = RandomChoice[vars, catalogArity[Join[lhs, rhs]]];
  If[
    $EdgeSymmetry === "Unordered" && MemberQ[catalogSideKeys[lhs], catalogEdgeKey[edge]],
    Return[mutationFailure[strategy, lhs -> rhs, "The drawn substructure edge is already required by the left-hand side."], Module]
  ];
  recordOperator["AddStableSubstructure", <|"Edge" -> edge|>];
  Append[lhs, edge] -> Append[rhs, edge]
]


(* ::Subsection:: *)
(*Hub-biased SplitVariable, ReduceVariableReuse (catalog 12)*)


(* SplitVariable at the most reused RHS variable: one of its RHS occurrences
   becomes a fresh variable. *)
splitHubDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {hubs, hub, position, fresh},
  hubs = catalogHubs[rhs, 2];
  If[
    hubs === {},
    Return[mutationFailure[strategy, lhs -> rhs, "No right-hand-side variable lies in two or more right-hand-side edges."], Module]
  ];
  hub = RandomChoice[hubs];
  position = RandomChoice @ Position[rhs, hub, {2}, Heads -> False];
  fresh = catalogFresh[];
  recordOperator["SplitVariable", <|"Variable" -> hub, "Position" -> Prepend[position, 2], "NewVariable" -> fresh|>];
  lhs -> ReplacePart[rhs, position -> fresh]
]


(* Reroute one RHS edge away from the most reused RHS variable to a least-used
   variable that is not already in the edge; no variable is created. *)
reduceVariableReuseDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {degrees, hubs, hub, position, edge, candidates, least, replacement, newRHS},
  degrees = catalogDegrees[rhs];
  hubs = catalogHubs[rhs, 2];
  If[
    hubs === {},
    Return[mutationFailure[strategy, lhs -> rhs, "No right-hand-side variable lies in two or more right-hand-side edges."], Module]
  ];
  hub = RandomChoice[hubs];
  position = RandomChoice @ Position[rhs, hub, {2}, Heads -> False];
  edge = rhs[[First[position]]];
  candidates = Select[catalogVariables[lhs, rhs], # =!= hub && !MemberQ[edge, #] &];
  If[
    candidates === {},
    Return[mutationFailure[strategy, lhs -> rhs, "No variable outside the hub's edge can take over the hub's slot."], Module]
  ];
  least = Min[Lookup[degrees, candidates, 0]];
  replacement = RandomChoice @ Select[candidates, Lookup[degrees, #, 0] === least &];
  newRHS = ReplacePart[rhs, position -> replacement];
  If[
    Length[catalogSideKeys[newRHS]] =!= Length[catalogSideKeys[rhs]],
    Return[mutationFailure[strategy, lhs -> rhs, "The rerouted edge duplicates an existing edge."], Module]
  ];
  recordOperator[
    "ReduceVariableReuse",
    <|"Variable" -> hub, "Position" -> Prepend[position, 2], "Replacement" -> replacement|>
  ];
  lhs -> newRHS
]


(* ::Subsection:: *)
(*Hub-biased IdentifyVariables, AddStarMotif (catalog 13)*)


(* IdentifyVariables into the most reused RHS variable. Merging two LHS
   variables would change the match pattern, so at most one of the pair is an
   LHS variable and the LHS is unchanged up to renaming. *)
identifyIntoHubDraw[strategy_String][lhs_List -> rhs_List] := Module[
  {lhsVars, hubs, hub, candidates, merged},
  lhsVars = DeleteDuplicates @ Flatten[lhs];
  hubs = catalogHubs[rhs];
  If[
    hubs === {},
    Return[mutationFailure[strategy, lhs -> rhs, "The right-hand side has no variable to grow into a hub."], Module]
  ];
  hub = RandomChoice[hubs];
  candidates = Select[
    catalogVariables[lhs, rhs],
    # =!= hub && !(MemberQ[lhsVars, #] && MemberQ[lhsVars, hub]) &
  ];
  If[
    candidates === {},
    Return[mutationFailure[strategy, lhs -> rhs, "No variable can be merged into the hub without changing the left-hand-side pattern."], Module]
  ];
  merged = RandomChoice[candidates];
  recordOperator["IdentifyVariables", <|"Kept" -> hub, "Merged" -> merged|>];
  Replace[lhs, merged -> hub, {2}] -> Replace[rhs, merged -> hub, {2}]
]


(* Attach new edges to fresh variables at the most reused RHS variable (an
   LHS variable when the RHS is empty). *)
addStarMotifDraw[strategy_String, range_][lhs_List -> rhs_List] := Module[
  {hubs, hub, arity, edges},
  hubs = catalogHubs[rhs];
  If[hubs === {}, hubs = DeleteDuplicates @ Flatten[lhs]];
  If[
    hubs === {},
    Return[mutationFailure[strategy, lhs -> rhs, "The rule has no variable to centre a star on."], Module]
  ];
  hub = RandomChoice[hubs];
  arity = Max[2, catalogArity[Join[lhs, rhs]]];
  edges = Table[catalogEdge[{hub}, arity], RandomInteger[range]];
  recordOperator["AddStarMotif", <|"Hub" -> hub, "Edges" -> edges|>];
  lhs -> Join[rhs, edges]
]


(* ::Subsection:: *)
(*ContractionRule, AddRule, DeleteRule, AddInverseRule (catalog 14, 15)*)


(* Cleanup rule for a hub neighbourhood: a star of `degree` edges at one
   centre is rewritten to a path over its leaves (the centre is no longer
   mentioned). For arity a > 2 every star edge carries a - 2 extra
   variables, which its path edge keeps. Degree 3, arity 2 gives the catalog
   rule {{x, y}, {x, z}, {x, u}} -> {{y, z}, {z, u}}. *)
catalogContractionRule[degree_Integer?(# >= 2 &), arity_Integer?(# >= 2 &)] := Module[
  {center = catalogFresh[], leaves, extras},
  leaves = Table[catalogFresh[], degree];
  extras = Table[catalogFresh[], degree, arity - 2];
  Table[Join[{center, leaves[[i]]}, extras[[i]]], {i, degree}] ->
    Table[Join[{leaves[[i]], leaves[[i + 1]]}, extras[[i]]], {i, degree - 1}]
]


(* ContractionRule builds the cleanup rule, AddRule adds it to the rule set.
   The degree comes from the largest RHS incidence degree of the members
   (clipped to 2..4) unless the "ContractionDegree" option fixes it; degrees
   whose rule is already a member are skipped. *)
addContractionRuleDraw[strategy_String, options_Association][spec_] := Module[
  {rules = ruleList[spec], arity, hubDegree, degrees, existing, cleanup = None, degree},
  arity = catalogArity[Catenate[Join[#[[1]], #[[2]]] & /@ rules]];
  If[
    arity < 2,
    Return[mutationFailure[strategy, spec, "A contraction rule needs edges of arity at least two."], Module]
  ];
  hubDegree = Max[2, Max[catalogMaxDegree[#[[2]]] & /@ rules]];
  degrees = Replace[
    Lookup[options, "ContractionDegree", Automatic],
    {Automatic :> DeleteDuplicates[{Min[hubDegree, 4], 3, 2, 4}], k_Integer :> {k}}
  ];
  existing = CanonicalRuleForm /@ rules;
  Do[
    Module[{candidate = catalogContractionRule[k, arity], form},
      form = CanonicalRuleForm[candidate];
      If[NoneTrue[existing, # === form &], cleanup = candidate; degree = k; Break[]]
    ],
    {k, degrees}
  ];
  If[
    cleanup === None,
    Return[mutationFailure[strategy, spec, "Every candidate contraction rule is already a member of the rule set."], Module]
  ];
  recordOperator["ContractionRule", <|"Degree" -> degree, "Arity" -> arity, "Rule" -> cleanup|>];
  recordOperator["AddRule", <|"Rule" -> cleanup, "RuleCount" -> Length[rules] + 1|>];
  Append[rules, cleanup]
]


(* Delete one member of a rule set; a set is never emptied, and a set reduced
   to one member is returned as that rule. *)
deleteRuleDraw[strategy_String][spec_] := Module[
  {rules = ruleList[spec], reference, remaining},
  If[
    Length[rules] < 2,
    Return[
      mutationFailure[strategy, spec, "DeleteRule needs a rule set with at least two member rules; a rule set is never emptied."],
      Module
    ]
  ];
  reference = CanonicalRuleForm[rules];
  Do[
    remaining = Delete[rules, index];
    If[
      CanonicalRuleForm[remaining] =!= reference,
      recordOperator["DeleteRule", <|"RuleIndex" -> index, "Rule" -> rules[[index]], "RuleCount" -> Length[remaining]|>];
      Return[If[Length[remaining] === 1, First[remaining], remaining], Module]
    ],
    {index, RandomSample @ Range @ Length[rules]}
  ];
  mutationFailure[strategy, spec, "Deleting any member leaves the canonical rule set unchanged."]
]


(* Add the inverse rhs -> lhs of a member (over fresh variables) as a new
   member, so the member's updates can be undone. *)
addInverseRuleDraw[strategy_String][spec_] := Module[
  {rules = ruleList[spec], existing, inverse, form},
  existing = CanonicalRuleForm /@ rules;
  Do[
    If[
      rules[[index, 1]] =!= {} && rules[[index, 2]] =!= {},
      inverse = catalogRenameApart[rules[[index, 2]] -> rules[[index, 1]]];
      form = CanonicalRuleForm[inverse];
      If[
        !FailureQ[form] && NoneTrue[existing, # === form &],
        recordOperator["AddInverseRule", <|"RuleIndex" -> index, "InverseRule" -> inverse, "RuleCount" -> Length[rules] + 1|>];
        Return[Append[rules, inverse], Module]
      ]
    ],
    {index, RandomSample @ Range @ Length[rules]}
  ];
  mutationFailure[strategy, spec, "No member rule has an inverse that is new to the rule set."]
]


(* ::Section:: *)
(*Strategy mutation functions*)


$catalogStrategyInputMessage = "Expected a valid hypergraph rewrite rule lhs -> rhs.";
$catalogRuleSetInputMessage = "Expected a valid hypergraph rewrite rule or a nonempty list of rules.";


(* Catalog 3. *)
SymmetryConfluenceMutation[rule_?validHypergraphRuleQ] :=
  catalogFirstApplicable[
    "SymmetryConfluence",
    rule,
    Join[
      {
        catalogCoreOperator["SymmetryConfluence", IdentifyVariablesMutation],
        catalogOperator["SymmetryConfluence", symmetrizeRHSDraw["SymmetryConfluence"], 2]
      },
      If[
        multisetUniverseQ[],
        {catalogPermutationOperator["SymmetryConfluence", "PermuteRHS", "Right"]},
        {}
      ]
    ]
  ]

SymmetryConfluenceMutation[other_, ___] :=
  mutationFailure["SymmetryConfluence", other, $catalogStrategyInputMessage]


(* Catalog 4. *)
BoundaryPreservationMutation[rule_?validHypergraphRuleQ] :=
  catalogFirstApplicable[
    "BoundaryPreservation",
    rule,
    {
      catalogOperator["BoundaryPreservation", boundaryPreserveRHSDraw["BoundaryPreservation"], 2],
      catalogOperator["BoundaryPreservation", deleteDisconnectedRHSDraw["BoundaryPreservation"], 1]
    }
  ]

BoundaryPreservationMutation[other_, ___] :=
  mutationFailure["BoundaryPreservation", other, $catalogStrategyInputMessage]


(* Catalog 5. Reordering the edge list is a canonical no-op, so
   PermuteEdgeOrder permutes the slot order inside one edge, which only
   exists in the ordered and declared universes. *)
TerminalDiversityMutation[rule_?validHypergraphRuleQ] :=
  catalogFirstApplicable[
    "TerminalDiversity",
    rule,
    Join[
      {
        catalogCoreOperator["TerminalDiversity", SplitVariableMutation],
        catalogOperator["TerminalDiversity", addMotifDraw["TerminalDiversity"], 4]
      },
      If[
        multisetUniverseQ[],
        {catalogPermutationOperator["TerminalDiversity", "PermuteEdgeOrder", Automatic]},
        {}
      ]
    ]
  ]

TerminalDiversityMutation[other_, ___] :=
  mutationFailure["TerminalDiversity", other, $catalogStrategyInputMessage]


(* Catalog 7. *)
MeshDensityMutation[rule_?validHypergraphRuleQ] := MeshDensityMutation[rule, <||>]

MeshDensityMutation[rule_?validHypergraphRuleQ, options_Association] :=
  With[{accept = catalogDegreeCapQ[rule, Lookup[options, "MaxRHSDegree", 4]]},
    catalogFirstApplicable[
      "MeshDensity",
      rule,
      {
        catalogOperator["MeshDensity", addCycleMotifDraw["MeshDensity"], 6, accept],
        catalogOperator["MeshDensity", addChainMotifDraw["MeshDensity"], 6, accept],
        catalogOperator["MeshDensity", conservationMutateDraw["MeshDensity"], 8, accept]
      }
    ]
  ]

MeshDensityMutation[other_, ___] :=
  mutationFailure["MeshDensity", other, $catalogStrategyInputMessage]

meshDensityProposal[rule_, context_Association] :=
  MeshDensityMutation[rule, Lookup[context, "Options", <||>]]


(* Catalog 8. *)
HomogenizingMutation[rule_?validHypergraphRuleQ] :=
  catalogFirstApplicable[
    "Homogenizing",
    rule,
    {
      catalogOperator["Homogenizing", symmetrizeRHSDraw["Homogenizing"], 2],
      catalogOperator["Homogenizing", boundaryPreserveRHSDraw["Homogenizing"], 2]
    }
  ]

HomogenizingMutation[other_, ___] :=
  mutationFailure["Homogenizing", other, $catalogStrategyInputMessage]


(* Catalog 10. *)
LocalStabilityMutation[rule_?validHypergraphRuleQ] :=
  catalogFirstApplicable[
    "LocalStability",
    rule,
    {
      catalogOperator["LocalStability", preserveMotifDraw["LocalStability"], 2],
      catalogOperator["LocalStability", addStableSubstructureDraw["LocalStability"], 6]
    }
  ]

LocalStabilityMutation[other_, ___] :=
  mutationFailure["LocalStability", other, $catalogStrategyInputMessage]


(* Catalog 12. *)
DegreeBalancingMutation[rule_?validHypergraphRuleQ] :=
  catalogFirstApplicable[
    "DegreeBalancing",
    rule,
    {
      catalogOperator["DegreeBalancing", splitHubDraw["DegreeBalancing"], 3],
      catalogOperator["DegreeBalancing", reduceVariableReuseDraw["DegreeBalancing"], 6]
    }
  ]

DegreeBalancingMutation[other_, ___] :=
  mutationFailure["DegreeBalancing", other, $catalogStrategyInputMessage]


(* Catalog 13. *)
HubSeedingMutation[rule_?validHypergraphRuleQ] := HubSeedingMutation[rule, <||>]

HubSeedingMutation[rule_?validHypergraphRuleQ, options_Association] :=
  catalogFirstApplicable[
    "HubSeeding",
    rule,
    {
      catalogOperator["HubSeeding", identifyIntoHubDraw["HubSeeding"], 3],
      catalogOperator["HubSeeding", addStarMotifDraw["HubSeeding", Lookup[options, "StarEdges", {1, 2}]], 2]
    }
  ]

HubSeedingMutation[other_, ___] :=
  mutationFailure["HubSeeding", other, $catalogStrategyInputMessage]

hubSeedingProposal[rule_, context_Association] :=
  HubSeedingMutation[rule, Lookup[context, "Options", <||>]]


(* Catalog 14. Rule-set aware: a single rule becomes a rule set by AddRule. *)
HubPruningMutation[spec_?validRuleSpecQ] := HubPruningMutation[spec, <||>]

HubPruningMutation[spec_?validRuleSpecQ, options_Association] :=
  catalogFirstApplicable[
    "HubPruning",
    spec,
    {
      catalogOperator["HubPruning", addContractionRuleDraw["HubPruning", options], 1],
      catalogOperator["HubPruning", deleteRuleDraw["HubPruning"], 1]
    }
  ]

HubPruningMutation[other_, ___] :=
  mutationFailure["HubPruning", other, $catalogRuleSetInputMessage]

hubPruningProposal[spec_, context_Association] :=
  HubPruningMutation[spec, Lookup[context, "Options", <||>]]


(* Catalog 15. Rule-set aware: RHS operators act on one member rule. *)
CausalInvarianceStyleMutation[spec_?validRuleSpecQ] :=
  catalogFirstApplicable[
    "CausalInvarianceStyle",
    spec,
    {
      catalogOnMember[catalogOperator["CausalInvarianceStyle", symmetrizeRHSDraw["CausalInvarianceStyle"], 2]],
      catalogOnMember[catalogOperator["CausalInvarianceStyle", boundaryPreserveRHSDraw["CausalInvarianceStyle"], 2]],
      catalogOperator["CausalInvarianceStyle", addInverseRuleDraw["CausalInvarianceStyle"], 1]
    }
  ]

CausalInvarianceStyleMutation[other_, ___] :=
  mutationFailure["CausalInvarianceStyle", other, $catalogRuleSetInputMessage]


(* ::Section:: *)
(*Registration*)


(* "PrimaryObjectives" map the catalog's primary objectives to registered
   metrics (all registered by ExtendedMetrics.wl or the core; every quantity
   the catalog marks * has a registered counterpart). "SupplementalObjectives"
   records the catalog's supplemental objectives the same way (documentation
   only). RequiredMetrics are the primary objectives: selecting a strategy
   computes them, as Diagnostic metrics unless promoted. *)
$catalogStrategies = <|

  "SymmetryConfluence" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> SymmetryConfluenceMutation,
    "Operators" -> {"IdentifyVariables", "SymmetrizeRHS", "PermuteRHS"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {"ReconvergenceRatio", "OutDegreeEntropy"},
    "Catalog" -> 3,
    "PrimaryObjectives" -> <|"ReconvergenceRatio" -> "Maximize", "OutDegreeEntropy" -> "Maximize"|>,
    "SupplementalObjectives" -> <|"MeanBranchingStrength" -> "Target", "CausalMergeEventsRatio" -> "Maximize"|>,
    "Description" -> "Identify two variables, close the RHS under an exchange of interchangeable variables, or (ordered/declared universes) permute the slots of one RHS edge: nontrivial branches that often merge into equivalent states."
  |>,

  "BoundaryPreservation" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> BoundaryPreservationMutation,
    "Operators" -> {"BoundaryPreserveRHS", "DeleteDisconnectedRHS"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {"LargestComponentRatio"},
    "Catalog" -> 4,
    "PrimaryObjectives" -> <|"LargestComponentRatio" -> "Maximize"|>,
    "SupplementalObjectives" -> <|
      "NumberOfConnectedComponents" -> "Minimize",
      "LargestConnectedComponentSize" -> "Maximize",
      "HGMaxVerticesCount" -> "Maximize",
      "FinalVertexCount" -> "Maximize"
    |>,
    "Description" -> "Attach every RHS component without an LHS variable to the boundary and restore dropped LHS variables, or delete such components: large but cohesive connected structures."
  |>,

  "TerminalDiversity" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> TerminalDiversityMutation,
    "Operators" -> {"SplitVariable", "AddMotif", "PermuteEdgeOrder"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {"NonIsomorphicTerminalStateCount"},
    "Catalog" -> 5,
    "PrimaryObjectives" -> <|"NonIsomorphicTerminalStateCount" -> "Maximize"|>,
    "SupplementalObjectives" -> <|
      "TerminalStateCount" -> "Maximize",
      "OutDegreeEntropy" -> "Maximize",
      "MultiwayStateCount" -> "Maximize"
    |>,
    "Description" -> "Split a repeated variable, attach an asymmetric pendant, pendant-path or loop motif, or (ordered/declared universes) permute the slots of one edge -- reordering the edge list itself is a canonical no-op: many genuinely different halting outcomes."
  |>,

  "MeshDensity" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> MeshDensityMutation,
    "ContextMutationFunction" -> meshDensityProposal,
    "Operators" -> {"AddCycleMotif", "AddChainMotif", "ConservationMutate"},
    "DefaultOptions" -> <|"MaxRHSDegree" -> 4|>,
    "OptionSpecs" -> <|"MaxRHSDegree" -> (# === Infinity || (IntegerQ[#] && Positive[#]) &)|>,
    "RequiredMetrics" -> {"EffectiveDimensionEstimate", "HGMeanEdgeToVertexRatio"},
    "Catalog" -> 7,
    "PrimaryObjectives" -> <|"EffectiveDimensionEstimate" -> "Target", "HGMeanEdgeToVertexRatio" -> "Target"|>,
    "SupplementalObjectives" -> <|
      "DimensionVariance" -> "Minimize",
      "LargestComponentRatio" -> "Maximize",
      "FinalDensity" -> "Target",
      "MaxVertexDegree" -> "Minimize"
    |>,
    "Description" -> "Close a 3- or 4-cycle (or add a fresh triangle), subdivide an RHS edge, or rewire one RHS slot conserving the per-event growth budget; proposals that raise the largest RHS degree above MaxRHSDegree are rejected: space-like growth without star-like hubs."
  |>,

  "Homogenizing" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> HomogenizingMutation,
    "Operators" -> {"SymmetrizeRHS", "BoundaryPreserveRHS"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {"DimensionVariance"},
    "Catalog" -> 8,
    "PrimaryObjectives" -> <|"DimensionVariance" -> "Minimize"|>,
    "SupplementalObjectives" -> <|
      "VertexDegreeVariance" -> "Minimize",
      "LargestComponentRatio" -> "Maximize",
      "NumberOfConnectedComponents" -> "Minimize",
      "EffectiveDimensionEstimate" -> "Target"
    |>,
    "Description" -> "Repeat local RHS templates (close the RHS under an exchange of interchangeable variables, or twin an RHS-only variable) and preserve the boundary uniformly: coherent hypergraphs with similar local geometry."
  |>,

  "LocalStability" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> LocalStabilityMutation,
    "Operators" -> {"PreserveMotif", "AddStableSubstructure"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {"LocalComponentLifetimeMean", "LocalComponentLifetimeMax", "MotifPersistence"},
    "Catalog" -> 10,
    "PrimaryObjectives" -> <|
      "LocalComponentLifetimeMean" -> "Maximize",
      "LocalComponentLifetimeMax" -> "Maximize",
      "MotifPersistence" -> "Maximize"
    |>,
    "SupplementalObjectives" -> <|
      "RewriteActivityEntropy" -> "Target",
      "CausalDependencyEntropy" -> "Target",
      "LargestComponentRatio" -> "Maximize"
    |>,
    "Description" -> "Keep a consumed LHS edge on the RHS, or require and rewrite unchanged a new edge over LHS variables: persistent local regions alongside continued activity."
  |>,

  "DegreeBalancing" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> DegreeBalancingMutation,
    "Operators" -> {"SplitVariable", "ReduceVariableReuse"},
    "DefaultOptions" -> <||>,
    "RequiredMetrics" -> {"VertexDegreeVariance", "MaxVertexDegree"},
    "Catalog" -> 12,
    "PrimaryObjectives" -> <|"VertexDegreeVariance" -> "Minimize", "MaxVertexDegree" -> "Minimize"|>,
    "SupplementalObjectives" -> <|
      "MaxVertexDegreeVariance" -> "Minimize",
      "FinalVertexDegreeVariance" -> "Minimize",
      "FinalMaxVertexDegree" -> "Minimize",
      "LargestComponentRatio" -> "Maximize"
    |>,
    "Description" -> "Split an RHS occurrence of the most reused RHS variable, or reroute one of its RHS edges to a least-used variable: connected structures without giant hubs."
  |>,

  "HubSeeding" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> HubSeedingMutation,
    "ContextMutationFunction" -> hubSeedingProposal,
    "Operators" -> {"IdentifyVariables", "AddStarMotif"},
    "DefaultOptions" -> <|"StarEdges" -> {1, 2}|>,
    "OptionSpecs" -> <|"StarEdges" -> (MatchQ[#, {a_Integer, b_Integer} /; 1 <= a <= b] &)|>,
    "RequiredMetrics" -> {"MaxVertexDegree", "HubPersistence"},
    "Catalog" -> 13,
    (* The catalog names motif persistence for hub-seeding; its aim, persistent
       hub-like centres, is measured by HubPersistence, which follows the hub
       vertex rather than its exact edges. *)
    "PrimaryObjectives" -> <|"MaxVertexDegree" -> "Maximize", "HubPersistence" -> "Maximize"|>,
    "SupplementalObjectives" -> <|
      "VertexDegreeVariance" -> "Maximize",
      "FinalMaxVertexDegree" -> "Maximize",
      "MaxVertexDegreeVariance" -> "Maximize",
      "LargestComponentRatio" -> "Maximize"
    |>,
    "Description" -> "Merge a variable into the most reused RHS variable, or attach new edges to it: persistent hub-like local centres."
  |>,

  "HubPruning" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> HubPruningMutation,
    "ContextMutationFunction" -> hubPruningProposal,
    "Operators" -> {"AddRule", "ContractionRule", "DeleteRule"},
    "DefaultOptions" -> <|"ContractionDegree" -> Automatic|>,
    "OptionSpecs" -> <|"ContractionDegree" -> (# === Automatic || (IntegerQ[#] && # >= 2) &)|>,
    "RuleSetAware" -> True,
    "RequiredMetrics" -> {"MaxVertexDegree", "VertexDegreeVariance"},
    "Catalog" -> 14,
    "PrimaryObjectives" -> <|"MaxVertexDegree" -> "Minimize", "VertexDegreeVariance" -> "Minimize"|>,
    "SupplementalObjectives" -> <|
      "MaxVertexDegreeVariance" -> "Minimize",
      "Runtime" -> "Minimize",
      "LargestComponentRatio" -> "Maximize"
    |>,
    "Description" -> "Rule-set aware: add a contraction rule that rewrites a star of k edges into a path over its leaves (k from the largest RHS degree), or delete a member of a rule set with at least two members: hubs removed without fragmenting the structure."
  |>,

  "CausalInvarianceStyle" -> <|
    "ImplementedQ" -> True,
    "MutationFunction" -> CausalInvarianceStyleMutation,
    "Operators" -> {"SymmetrizeRHS", "BoundaryPreserveRHS", "AddInverseRule"},
    "DefaultOptions" -> <||>,
    "RuleSetAware" -> True,
    "RequiredMetrics" -> {"UpdateOrderSensitivity", "ReconvergenceRatio"},
    "Catalog" -> 15,
    "PrimaryObjectives" -> <|"UpdateOrderSensitivity" -> "Minimize", "ReconvergenceRatio" -> "Maximize"|>,
    "SupplementalObjectives" -> <|
      "CausalMergeEventsRatio" -> "Maximize",
      "CausalDependencyEntropy" -> "Target",
      "UpdateOrderTerminalOutcomeCount" -> "Target",
      "DimensionVariance" -> "Minimize",
      "CausalUpdateOrderSensitivity" -> "Minimize"
    |>,
    "Description" -> "Rule-set aware: symmetrize the RHS or preserve the LHS boundary of one member rule, or add the inverse of a member as a new rule: overlapping updates that commute more often."
  |>

|>;

registerMutationStrategies[$catalogStrategies];


(* ::Section:: *)
(*Goal presets*)


(* One opt-in goal preset per catalog strategy, named like the strategy: the
   strategy alone, its primary objectives plus HaltedWithinCapQ and
   MultiwayStateCount. The primary objectives are Diagnostic metrics in the
   registry; "MetricOverrides" holds the overrides that make them Pareto
   objectives in the catalog's direction. ValidateEvolutionConfiguration does
   not read preset overrides yet, so until it does they must be passed
   explicitly as the "MetricOverrides" option. "Target" objectives use the
   targets below unless overridden. *)
$catalogObjectiveTargets = <|"EffectiveDimensionEstimate" -> 2., "HGMeanEdgeToVertexRatio" -> 1.5|>;

catalogObjectiveOverrides[objectives_Association] :=
  Association @ KeyValueMap[
    Function[{metric, direction},
      metric -> Join[
        <|"Stage" -> "Objective", "Direction" -> direction|>,
        If[direction === "Target", <|"Target" -> Lookup[$catalogObjectiveTargets, metric, 1]|>, <||>]
      ]
    ],
    objectives
  ]

catalogPresetDescription[name_String, specification_Association] :=
  StringJoin[
    "Opt-in goal for catalog strategy ", ToString[specification["Catalog"]], " (", name, "): ",
    specification["Description"],
    " Primary objectives: ",
    StringRiffle[KeyValueMap[#1 <> " (" <> ToLowerCase[#2] <> ")" &, specification["PrimaryObjectives"]], ", "],
    ". They are Diagnostic metrics in the registry: pass \"MetricOverrides\" -> ",
    ToString[catalogObjectiveOverrides[specification["PrimaryObjectives"]], InputForm],
    " to make them Pareto objectives."
  ]

registerGoalPresets @ Association @ KeyValueMap[
  Function[{name, specification},
    name -> <|
      "Description" -> catalogPresetDescription[name, specification],
      "MutationStrategies" -> {name},
      "FitnessMetrics" -> DeleteDuplicates @ Join[
        Keys[specification["PrimaryObjectives"]],
        {"HaltedWithinCapQ", "MultiwayStateCount"}
      ],
      "MetricOverrides" -> catalogObjectiveOverrides[specification["PrimaryObjectives"]],
      "Catalog" -> specification["Catalog"]
    |>
  ],
  $catalogStrategies
];


(* ::Section:: *)
(*GrowthBudget (catalog 1): ConservationMutate*)


(* The catalog lists ConservationMutate as GrowthBudget's third operator. It
   lives here with the other catalog operators and extends the core
   GrowthBudget strategy: with probability "ConservationProbability"
   (default 1/3) the strategy rewires one RHS slot while conserving the
   per-event growth budget, otherwise it applies the growth recipe with the
   strategy's "AddedEdgesRange". When the chosen operator has no valid,
   canonically new proposal the other one is tried; a failed attempt leaves
   no operator in the provenance trace. *)
growthBudgetProposal[rule_Rule, context_Association] := Module[
  {options = Lookup[context, "Options", <||>], grow, conserve, attempt, operators, result = None},
  grow = Function[r, GrowthBudgetMutation[r, Lookup[options, "AddedEdgesRange", {1, 2}]]];
  conserve = catalogOperator["GrowthBudget", conservationMutateDraw["GrowthBudget"], 8];
  attempt[operator_] := Module[{saved = $operatorTrace, proposal},
    proposal = operator[rule];
    If[FailureQ[proposal] && ListQ[saved], $operatorTrace = saved];
    proposal
  ];
  operators = If[
    RandomReal[] < Lookup[options, "ConservationProbability", 1/3],
    {conserve, grow},
    {grow, conserve}
  ];
  Do[
    result = attempt[operator];
    If[!FailureQ[result], Break[]],
    {operator, operators}
  ];
  result
]


$MutationStrategyRegistry["GrowthBudget"] = Join[
  $MutationStrategyRegistry["GrowthBudget"],
  <|
    "ContextMutationFunction" -> growthBudgetProposal,
    "Operators" -> {"AddRHSVariable", "AddRHSEdge", "ConservationMutate"},
    "DefaultOptions" -> <|"AddedEdgesRange" -> {1, 2}, "ConservationProbability" -> 1/3|>,
    "OptionSpecs" -> <|
      "AddedEdgesRange" -> (MatchQ[#, {a_Integer?Positive, b_Integer} /; a <= b] &),
      "ConservationProbability" -> (NumericQ[#] && 0 <= # <= 1 &)
    |>,
    "Description" -> "Add an RHS-only variable and one or two RHS edges, or (with probability ConservationProbability, default 1/3) rewire one RHS slot while conserving the per-event growth budget (ConservationMutate): larger states without density blowup."
  |>
];
