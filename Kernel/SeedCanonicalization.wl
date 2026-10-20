(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Universes*)


(* Edge-symmetry universe. Dynamically scoped: config-taking entry points
   Block this from config["EdgeSymmetry"], so direct calls default to the
   project's original unordered convention.
     "Unordered" -- simple hypergraphs: an edge is identified with its sorted
                    slot tuple and duplicate edges are removed.
     "Ordered"   -- ordered multiset hypergraphs: slot positions and edge
                    multiplicity are semantic.
     "Declared"  -- ordered ports with a declared slot-symmetry group per
                    arity ($SymmetryGroups). An edge is the orbit of its slot
                    tuple under the group; multiplicity is semantic, exactly
                    as in "Ordered". *)
$EdgeSymmetry = "Unordered";


(* Declared slot-symmetry groups for the "Declared" universe: an Association
   arity -> list of permutation lists (all group elements, identity
   included), optionally with "Default" -> a named group applied to arities
   that are not listed. Arities without an entry use the trivial group
   (ordered ports). Dynamically scoped exactly like $EdgeSymmetry. *)
$SymmetryGroups = <||>;


(* Rewrite semantics for vertices the RHS drops. "EdgeToken" (the project
   default) follows the SetReplace/WolframModel convention: untouched edges
   keep their vertices, and a dropped vertex simply stops being mentioned.
   "VertexDeletion" opts into the WolframInstitute/Hypergraph native
   behavior, which removes a dropped vertex from every edge of the state.
   Dynamically scoped exactly like $EdgeSymmetry. *)
$RewriteSemantics = "EdgeToken";


multisetUniverseQ[] := MatchQ[$EdgeSymmetry, "Ordered" | "Declared"]


(* The WolframInstitute/Hypergraph symmetry used for matching. The declared
   universe matches ordered patterns expanded over the slot orbits. *)
nativeEdgeSymmetry[] := If[$EdgeSymmetry === "Unordered", "Unordered", "Ordered"]


(* Identity tag of the active universe, used in cache keys and run logs. *)
universeTag[] :=
  Switch[
    $EdgeSymmetry,
    "Ordered", If[$CanonicalBackend === "Exact", {"OrderedMultiset", "ExactCanonical"}, "OrderedMultiset"],
    "Declared", {"DeclaredMultiset", Normal @ KeySort @ $SymmetryGroups, "ExactCanonical"},
    _, If[$CanonicalBackend === "Exact", {"UnorderedSimple", "ExactCanonical"}, "UnorderedSimple"]
  ]


(* Evaluate expr in the universe of a configuration. *)
SetAttributes[withConfigUniverse, HoldRest];

withConfigUniverse[config_Association, expr_] :=
  Block[
    {
      $EdgeSymmetry = Lookup[config, "EdgeSymmetry", "Unordered"],
      $SymmetryGroups = Replace[Lookup[config, "SymmetryGroups", <||>], Automatic -> <||>],
      $RewriteSemantics = Lookup[config, "RewriteSemantics", "EdgeToken"],
      $CanonicalBackend = Lookup[config, "CanonicalForm", "Exact"]
    },
    expr
  ]


slotPermutations[k_Integer] :=
  Which[
    KeyExistsQ[$SymmetryGroups, k], $SymmetryGroups[k],
    KeyExistsQ[$SymmetryGroups, "Default"],
      Replace[symmetryGroupElements[k, $SymmetryGroups["Default"]], $Failed -> {Range[k]}],
    True, {Range[k]}
  ]


(* The slot orbit of an edge: every tuple that denotes the same edge. *)
edgeOrbit[edge_List] :=
  If[
    $EdgeSymmetry === "Declared",
    DeleteDuplicates[edge[[#]] & /@ slotPermutations[Length[edge]]],
    {edge}
  ]


declaredEdgeRepresentative[edge_List] := First @ Sort @ edgeOrbit[edge]


(* The positional Hypergraph[edges, "Ordered"] form silently constructs a
   broken object in WolframInstitute/Hypergraph 1.2.3; only the option form
   is safe. *)
modeHypergraph[edges_] := Hypergraph[edges, "EdgeSymmetry" -> nativeEdgeSymmetry[]]


(* Unordered: simple hypergraphs (sorted edges, duplicates removed).
   Ordered: multiset semantics -- positions and multiplicity are semantic.
   Declared: each edge is replaced by the least tuple of its slot orbit; the
   multiset of edges is kept. *)
normalizeStateEdges[state_List] :=
  Switch[
    $EdgeSymmetry,
    "Ordered", state,
    "Declared", declaredEdgeRepresentative /@ state,
    _, DeleteDuplicates[Sort /@ state]
  ]


(* ::Section:: *)
(*Rules and rule sets*)


validHypergraphRuleQ[rule_] :=
  MatchQ[rule, (lhs_ -> rhs_) /; hypergraphStateQ[lhs] && hypergraphStateQ[rhs]]


(* A rule specification is a single rule or an unordered rule set: a list of
   rules, each with its own variables (no variable is shared across rules),
   any of which may fire. *)
validRuleSpecQ[rule_Rule] := validHypergraphRuleQ[rule]
validRuleSpecQ[rules : {__Rule}] := AllTrue[rules, validHypergraphRuleQ]
validRuleSpecQ[_] := False


ruleSetQ[{__Rule}] := True
ruleSetQ[_] := False


ruleList[rule_Rule] := {rule}
ruleList[rules_List] := rules


toHypergraphRule[lhs_ -> rhs_] :=
  HypergraphRule[modeHypergraph[lhs], modeHypergraph[rhs]]


(* Application-time rule constructor. Under "EdgeToken" semantics the RHS
   hypergraph declares every rule variable as a vertex, so nothing lands in
   the paclet's deleted-vertex set and untouched edges survive rewrites
   intact. Canonicalization keeps using toHypergraphRule: rule identity does
   not depend on the application semantics. *)
toApplicationRule[lhs_ -> rhs_] :=
  If[
    $RewriteSemantics === "EdgeToken",
    HypergraphRule[
      modeHypergraph[lhs],
      Hypergraph[
        DeleteDuplicates @ Flatten[{lhs, rhs}],
        rhs,
        "EdgeSymmetry" -> nativeEdgeSymmetry[]
      ]
    ],
    toHypergraphRule[lhs -> rhs]
  ]


(* Declared universe: an LHS edge pattern matches a state edge when some
   tuple of its slot orbit matches it positionally, so the LHS is expanded
   into every combination of orbit tuples and matched in ordered mode. *)
lhsVariants[lhs_List] :=
  If[$EdgeSymmetry === "Declared", Tuples[edgeOrbit /@ lhs], {lhs}]


(* Compiled application data for a rule or rule set: a list of
   {ruleIndex, lhsVariables, HypergraphRule} triples (one triple per LHS
   variant in the declared universe). *)
applicationRuleSet[spec_] :=
  Catenate @ MapIndexed[
    Function[{rule, position},
      With[{variables = DeleteDuplicates @ Flatten @ First[rule], rhs = Last[rule]},
        {First[position], variables, toApplicationRule[# -> rhs]} & /@
          lhsVariants[First[rule]]
      ]
    ],
    ruleList[spec]
  ]


(* Every raw rewrite event of a compiled rule set on a state, as the paclet's
   match associations extended with "RuleIndex" and "LHSBinding". Returns
   $Failed when an application fails. In the declared universe two LHS
   variants can reach the same match, so events are deduplicated by rule,
   matched edge positions and LHS binding. *)
rawRewriteEvents[compiled_List, state_List] := Module[
  {hypergraph, results},

  hypergraph = modeHypergraph[state];

  results = Map[
    Function[triple,
      With[{raw = Quiet @ Check[triple[[3]][hypergraph], $Failed]},
        If[
          ListQ[raw],
          Map[
            Join[
              #,
              <|
                "RuleIndex" -> triple[[1]],
                "LHSBinding" ->
                  Lookup[Lookup[#, "RuleVertexMap", <||>], triple[[2]], Missing[]]
              |>
            ] &,
            raw
          ],
          $Failed
        ]
      ]
    ],
    compiled
  ];

  If[MemberQ[results, $Failed], Return[$Failed]];

  results = Catenate[results];

  If[
    $EdgeSymmetry === "Declared",
    DeleteDuplicatesBy[
      results,
      {#["RuleIndex"], #["MatchEdgePositions"], #["LHSBinding"]} &
    ],
    results
  ]
]


(* ::Section:: *)
(*Canonical forms*)


(* Canonical-form backend for the "Unordered" and "Ordered" universes:
     "Exact"  -- the individualization-refinement canonical labelling below
                 (default: complete, invariant, and faster here);
     "Native" -- CanonicalHypergraph / CanonicalHypergraphRule of the
                 WolframInstitute/Hypergraph paclet (the original backend).
   The declared universe always uses "Exact". Dynamically scoped like
   $EdgeSymmetry.

   Why "Exact" exists: with WolframInstitute/Hypergraph 1.2.3,
   CanonicalHypergraph is not invariant on every input. Relabelling the
   vertices and reordering the edges of a state can change its canonical
   form; it happens for some ternary states in both native universes (for
   example {{4,3,1},{5,5,1},{4,3,3},{1,1,5}} versus its relabelled,
   reordered copy {{2,4,4},{5,5,3},{2,4,5},{3,3,5}} in the unordered
   universe). Such splits never merge non-isomorphic states -- every native
   canonical form is an isomorphic copy of its input -- so they can only
   over-count states; "Exact" removes them. *)
$CanonicalBackend = "Exact";

exactBackendQ[] := $EdgeSymmetry === "Declared" || $CanonicalBackend === "Exact"


(* The tuples that denote the same edge in the active universe. *)
universeOrbit[tuple_List] :=
  Switch[
    $EdgeSymmetry,
    "Unordered", Permutations[tuple],
    "Declared", edgeOrbit[tuple],
    _, {tuple}
  ]


(* Leaves of the search tree explored before giving up (a Failure is
   returned; callers treat it as an invalid evaluation). Only highly
   symmetric states that the twin pruning below cannot simplify get near
   this. *)
$ExactCanonicalLeafLimit = 200000;


exactRank[values_List] :=
  With[{sorted = Union[values]},
    Lookup[AssociationThread[sorted, Range @ Length[sorted]], values]
  ]


(* Canonical labelling of a list of sides (a state is one side, a rule is
   {lhs, rhs}); every edge is the orbit of its slot tuple. Colour refinement
   assigns each vertex the multiset of views of its edges (side, and for each
   orbit tuple the colours of its slots with the positions of the vertex);
   when refinement stalls, the least non-singleton colour class is split by
   individualizing each of its vertices in turn. The canonical form is the
   least leaf encoding of this canonical search tree: every leaf encoding is
   an isomorphic copy of the input and the tree commutes with relabelling, so
   the form is complete and invariant.

   Automorphism pruning (as in nauty) keeps symmetric inputs tractable
   without changing the result, which is still the least leaf encoding:
     - two leaves with equal encodings give an automorphism of the input;
     - at a node, a child in the orbit of an explored child under the
       automorphisms found so far that fix the node's individualized vertices
       has the same set of leaf encodings and is skipped (transpositions of
       twin vertices are recognized directly);
     - a leaf equal to the first (or the best) leaf maps the subtree it lies
       in onto an explored subtree, so the search returns to the node where
       its path left the path of that leaf.
   Returns the list of canonical sides over vertices 1..n, or $Failed past
   the leaf limit. *)
exactCanonicalSides[sides_List] := Catch[
  Module[
    {
      vertices, n, index, edgeSides, tuples, orbits, incidence, edgeKeys,
      rowTuples, rowMarks, rowArity, base, groupLengths, groupSides, degrees,
      arityData, rowValues,
      leaves = 0, refine, leafForm, twinQ, automorphism, orbitUnion,
      commonPrefixLength, search,
      firstForm = None, firstLabels = None, firstPath = None,
      bestForm = None, bestLabels = None, bestPath = None, generators = {}
    },

    vertices = DeleteDuplicates @ Flatten[sides];
    n = Length[vertices];
    index = AssociationThread[vertices, Range[n]];

    edgeSides = Catenate @ MapIndexed[ConstantArray[First[#2], Length[#1]] &, sides];
    tuples = Map[index, Catenate[sides], {2}];
    orbits = universeOrbit /@ tuples;

    incidence = ConstantArray[{}, n];
    Do[
      Scan[(incidence[[#]] = Append[incidence[[#]], e]) &, DeleteDuplicates[tuples[[e]]]],
      {e, Length[tuples]}
    ];

    edgeKeys = Sort @ MapThread[{#1, Sort[#2]} &, {edgeSides, orbits}];

    (* Refinement. The view of vertex v in edge e is {side, the sorted list
       over the edge's orbit tuples of the tuple's {colour, slot is v}
       pairs}; a vertex's signature is {colour, sorted views}, and classes are
       ranked by signature. Each pair list is encoded as {arity, value}, the
       value reading the digits 2 colour + mark in base 4 n + 4 (colours stay
       below 2 n + 1): this orders exactly like the pair lists (length first,
       then elementwise, False before True), so the ranking is unchanged, and
       all values of one iteration come from one vectorized pass. Rows are
       (vertex, incident edge, orbit tuple) in that nesting order. *)
    rowTuples = Catenate @ Table[Catenate[orbits[[incidence[[v]]]]], {v, n}];
    rowMarks = Catenate @ Table[
      Catenate @ Map[Function[e, Function[t, Boole[# === v] & /@ t] /@ orbits[[e]]], incidence[[v]]],
      {v, n}
    ];
    rowArity = Length /@ rowTuples;
    base = 4 n + 4;
    groupLengths = Catenate @ Table[Length /@ orbits[[incidence[[v]]]], {v, n}];
    groupSides = Catenate @ Table[edgeSides[[incidence[[v]]]], {v, n}];
    degrees = Length /@ incidence;
    arityData = KeyValueMap[
      Function[{k, positions},
        {positions, k, Flatten[rowTuples[[positions]]], rowMarks[[positions]], base^Range[k - 1, 0, -1]}
      ],
      GroupBy[Range @ Length[rowTuples], rowArity[[#]] &]
    ];
    rowValues[c_] := Module[{values = ConstantArray[0, Length[rowTuples]]},
      Scan[
        Function[d, values[[d[[1]]]] = (2 Partition[c[[d[[3]]]], d[[2]]] + d[[4]]) . d[[5]]],
        arityData
      ];
      values
    ];

    refine[colors_] := Module[{c = colors, next, classes, views},
      classes = Length @ DeleteDuplicates[colors];
      While[True,
        views = MapThread[
          {#1, Sort[#2]} &,
          {groupSides, TakeList[Transpose[{rowArity, rowValues[c]}], groupLengths]}
        ];
        next = exactRank @ MapThread[{#1, Sort[#2]} &, {c, TakeList[views, degrees]}];
        If[Max[0, next] === classes, Return[next, Module]];
        classes = Max[0, next];
        c = next
      ]
    ];

    leafForm[labels_] :=
      Table[
        Sort @ Pick[
          Function[orbit, First @ Sort @ Map[labels[[#]] &, orbit, {2}]] /@ orbits,
          edgeSides,
          side
        ],
        {side, Length[sides]}
      ];

    (* The transposition (u w) is an automorphism of the edge multiset. *)
    twinQ[u_, w_] :=
      Sort[
        MapThread[{#1, Sort[#2 /. {u -> w, w -> u}]} &, {edgeSides, orbits}]
      ] === edgeKeys;

    (* Leaves with equal encodings: v -> the vertex with the same label in
       the reference leaf. *)
    automorphism[labels_, reference_] := Ordering[reference][[labels]];

    orbitUnion[seeds_List, gens_List] := Module[{set = Union[seeds], next},
      If[gens === {} || set === {}, Return[set, Module]];
      While[True,
        next = Union[set, Flatten[#[[set]] & /@ gens]];
        If[Length[next] === Length[set], Return[set, Module]];
        set = next
      ]
    ];

    commonPrefixLength[a_List, b_List] :=
      LengthWhile[Transpose[{Take[a, UpTo[Length[b]]], Take[b, UpTo[Length[a]]]}], SameQ @@ # &];

    search[colors_, path_List] := Module[
      {c = refine[colors], depth = Length[path], form, cells, target, explored = {}, fixing, outcome},
      If[
        Max[0, c] === n,
        leaves++;
        If[leaves > $ExactCanonicalLeafLimit, Throw[$Failed, "exactCanonical"]];
        form = leafForm[c];
        Which[
          firstForm === None,
            firstForm = form; firstLabels = c; firstPath = path;
            bestForm = form; bestLabels = c; bestPath = path,
          form === firstForm,
            With[{g = automorphism[c, firstLabels]}, If[g =!= Range[n], AppendTo[generators, g]]];
            Throw[commonPrefixLength[path, firstPath], "exactJump"],
          form === bestForm,
            With[{g = automorphism[c, bestLabels]}, If[g =!= Range[n], AppendTo[generators, g]]];
            Throw[commonPrefixLength[path, bestPath], "exactJump"],
          OrderedQ[{form, bestForm}],
            bestForm = form; bestLabels = c; bestPath = path
        ];
        Return[Null, Module]
      ];
      cells = Select[GatherBy[Range[n], c[[#]] &], Length[#] > 1 &];
      target = First @ MinimalBy[cells, c[[First[#]]] &];
      Scan[
        Function[w,
          fixing = Select[generators, Function[g, AllTrue[path, g[[#]] === # &]]];
          If[
            NoneTrue[explored, twinQ[#, w] &] && !MemberQ[orbitUnion[explored, fixing], w],
            AppendTo[explored, w];
            outcome = Catch[
              search[ReplacePart[2 c, w -> 2 c[[w]] - 1], Append[path, w]],
              "exactJump",
              exactJump[#1] &
            ];
            (* A jump to this node abandons the child; a jump further up passes on. *)
            If[MatchQ[outcome, exactJump[k_] /; k < depth], Throw[First[outcome], "exactJump"]]
          ]
        ],
        target
      ];
      Null
    ];

    search[ConstantArray[1, n], {}];
    bestForm
  ],
  "exactCanonical"
]


exactCanonicalStateForm[state_List] :=
  With[
    {
      sides = exactCanonicalSides[{
        If[$EdgeSymmetry === "Unordered", DeleteDuplicates[Sort /@ state], state]
      }]
    },
    If[
      sides === $Failed,
      Failure[
        "CanonicalFormLimit",
        <|"Message" -> "The exact canonical form exceeded its search limit.", "State" -> state|>
      ],
      First[sides]
    ]
  ]


(* In the unordered universe the right-hand side of a rule is read as a
   simple hypergraph, as the state it produces is: duplicate right-hand edges
   (also up to slot order) cannot change any evolution, so rules that differ
   only by them have one identity. Left-hand duplicates are kept, because
   they change whether the rule matches. *)
ruleSidesNormalized[lhs_ -> rhs_] :=
  If[$EdgeSymmetry === "Unordered", lhs -> DeleteDuplicates[Sort /@ rhs], lhs -> rhs]


exactCanonicalRuleForm[lhs_ -> rhs_] :=
  With[
    {
      sides = exactCanonicalSides[
        If[$EdgeSymmetry === "Unordered", Map[Sort, {lhs, rhs}, {2}], {lhs, rhs}]
      ]
    },
    If[
      sides === $Failed,
      Failure[
        "CanonicalFormLimit",
        <|"Message" -> "The exact canonical form exceeded its search limit.", "Rule" -> (lhs -> rhs)|>
      ],
      sides[[1]] -> sides[[2]]
    ]
  ]


CanonicalStateForm[{}] := {}

CanonicalStateForm[state_?hypergraphStateQ] :=
  If[
    exactBackendQ[],
    exactCanonicalStateForm[state],
    normalizeStateEdges @ EdgeList @ CanonicalHypergraph @ modeHypergraph @ normalizeStateEdges[state]
  ]

CanonicalStateForm[state_, symmetry : "Unordered" | "Ordered"] :=
  Block[{$EdgeSymmetry = symmetry}, CanonicalStateForm[state]]

CanonicalStateForm[state_, symmetry : "Unordered" | "Ordered", backend : "Native" | "Exact"] :=
  Block[{$EdgeSymmetry = symmetry, $CanonicalBackend = backend}, CanonicalStateForm[state]]

CanonicalStateForm[state_, "Declared", groups_] :=
  With[{normalized = normalizeSymmetryGroups[groups]},
    If[
      FailureQ[normalized],
      normalized,
      Block[{$EdgeSymmetry = "Declared", $SymmetryGroups = normalized},
        CanonicalStateForm[state]
      ]
    ]
  ]

CanonicalStateForm[other_] :=
  Failure[
    "InvalidHypergraphState",
    <|
      "Message" -> "The expression is not a hypergraph state.",
      "Value" -> other
    |>
  ]


CanonicalRuleForm[rule_?validHypergraphRuleQ] :=
  If[
    exactBackendQ[],
    exactCanonicalRuleForm[ruleSidesNormalized[rule]],
    Module[{canonical},
      canonical = CanonicalHypergraphRule[toHypergraphRule[ruleSidesNormalized[rule]]];
      EdgeList[canonical[[1]]] -> EdgeList[canonical[[2]]]
    ]
  ]

(* Rule sets: each rule is canonicalized on its own (rules share no
   variables), the set is sorted and duplicates are removed. A set that
   reduces to one rule is that rule, so rule-set identity extends single-rule
   identity. *)
CanonicalRuleForm[rules : {__Rule}] /; AllTrue[rules, validHypergraphRuleQ] :=
  Module[{forms},
    forms = DeleteDuplicates @ Sort[CanonicalRuleForm /@ rules];
    If[Length[forms] === 1, First[forms], forms]
  ]

CanonicalRuleForm[rule_, symmetry : "Unordered" | "Ordered"] :=
  Block[{$EdgeSymmetry = symmetry}, CanonicalRuleForm[rule]]

CanonicalRuleForm[rule_, symmetry : "Unordered" | "Ordered", backend : "Native" | "Exact"] :=
  Block[{$EdgeSymmetry = symmetry, $CanonicalBackend = backend}, CanonicalRuleForm[rule]]

CanonicalRuleForm[rule_, "Declared", groups_] :=
  With[{normalized = normalizeSymmetryGroups[groups]},
    If[
      FailureQ[normalized],
      normalized,
      Block[{$EdgeSymmetry = "Declared", $SymmetryGroups = normalized},
        CanonicalRuleForm[rule]
      ]
    ]
  ]

CanonicalRuleForm[other_] :=
  Failure[
    "InvalidHypergraphRule",
    <|
      "Message" -> "The expression is not a hypergraph rewrite rule or rule set.",
      "Value" -> other
    |>
  ]


(* ::Section:: *)
(*Canonical-form self test*)


bruteForceCanonical[state_, universe_String] := Module[{vertices = Union @ Flatten[state], edges},
  edges = If[universe === "Unordered", DeleteDuplicates[Sort /@ state], state];
  First @ Sort @ Map[
    Function[perm,
      With[{relabel = AssociationThread[vertices, perm]},
        Sort[If[universe === "Unordered", Sort[relabel /@ #], relabel /@ #] & /@ edges]
      ]
    ],
    Permutations[Range @ Length[vertices]]
  ]
]


Options[CanonicalFormSelfTest] = {
  "Universes" -> {"Unordered", "Ordered"},
  "Backends" -> {"Exact", "Native"},
  "Arity" -> 3,
  "Vertices" -> 5,
  "Edges" -> 4,
  "Trials" -> 200,
  "RandomSeed" -> 1
};

CanonicalFormSelfTest[opts : OptionsPattern[]] := Module[
  {arity, vertexCount, edgeCount, trials, rows},
  {arity, vertexCount, edgeCount, trials} =
    OptionValue[{"Arity", "Vertices", "Edges", "Trials"}];

  rows = Flatten[Table[
    BlockRandom[
      SeedRandom[OptionValue["RandomSeed"]];
      Module[{states, copies, canonical, copyCanonical, invariance, copyFailures, completeness, example = Missing["None"]},
        states = Table[RandomInteger[{1, vertexCount}, {edgeCount, arity}], {trials}];
        copies = Map[
          With[{perm = RandomSample[Range[vertexCount]]}, RandomSample[# /. Thread[Range[vertexCount] -> perm]]] &,
          states
        ];
        canonical = CanonicalStateForm[#, universe, backend] & /@ states;
        copyCanonical = CanonicalStateForm[#, universe, backend] & /@ copies;
        invariance = Count[MapThread[SameQ, {canonical, copyCanonical}], False];
        If[invariance > 0,
          example = First @ Pick[Transpose[{states, copies}], MapThread[SameQ, {canonical, copyCanonical}], False]
        ];
        copyFailures = Count[
          MapThread[
            CanonicalStateForm[#1, universe, "Exact"] === CanonicalStateForm[#2, universe, "Exact"] &,
            {canonical, states}
          ],
          False
        ];
        completeness = With[{brute = bruteForceCanonical[#, universe] & /@ states},
          Count[
            Flatten @ Table[
              (canonical[[i]] === canonical[[j]]) === (brute[[i]] === brute[[j]]),
              {i, Length[states]}, {j, i + 1, Length[states]}
            ],
            False
          ]
        ];
        <|
          "Universe" -> universe,
          "Backend" -> backend,
          "Trials" -> trials,
          "InvarianceFailures" -> invariance,
          "CompletenessFailures" -> completeness,
          "NotIsomorphicCopy" -> copyFailures,
          "Example" -> example
        |>
      ]
    ],
    {universe, OptionValue["Universes"]},
    {backend, OptionValue["Backends"]}
  ], 1];

  <|
    "Arity" -> arity,
    "Vertices" -> vertexCount,
    "Edges" -> edgeCount,
    "HypergraphPacletVersion" -> hypergraphVersionString[],
    "Results" -> Dataset[rows],
    "Claim" ->
      "Random states only: a zero count is evidence, not a proof. InvarianceFailures counts relabelled, edge-shuffled copies with a different canonical form; CompletenessFailures counts state pairs where canonical equality disagrees with brute-force isomorphism; NotIsomorphicCopy counts canonical forms that are not isomorphic to their input (checked with the exact backend)."
  |>
]


(* ::Section:: *)
(*Applicability*)


RuleApplicableQ[rule_?validRuleSpecQ, state_?hypergraphStateQ] :=
  With[
    {events = rawRewriteEvents[applicationRuleSet[rule], normalizeStateEdges[state]]},
    ListQ[events] && events =!= {}
  ]

RuleApplicableQ[___] := False


(* ::Section:: *)
(*Registry access (lazy)*)


(* The WolframModelData resource emits ResourceObject::updavb whenever a newer
   version is published. That notice is informational: it must neither reach
   the user nor make Check-based failure detection reject a working
   registry, so it is silenced at every access. Successful retrievals are
   memoized; failures are not, so a later call can retry. *)
$registryEntriesCache = None;

registryFunction[] :=
  Quiet[ResourceFunction["WolframModelData"], ResourceObject::updavb]


registryEntries[] :=
  If[
    $registryEntriesCache =!= None,
    $registryEntriesCache,
    Module[{function, codes, data},
      function = registryFunction[];
      If[Head[function] =!= ResourceFunction, Return[$Failed, Module]];
      codes = Quiet[function[], ResourceObject::updavb];
      data = Quiet[function[All, {"Rule", "InitialCondition"}], ResourceObject::updavb];
      If[
        !ListQ[codes] || !ListQ[data] || Length[codes] =!= Length[data],
        Return[$Failed, Module]
      ];
      $registryEntriesCache = MapThread[
        Append[Association[#1], "RegistryCode" -> #2] &,
        {data, codes}
      ]
    ]
  ]


$registryMetadataKeys = {
  "Name", "ShortCode", "UUID", "Version", "DocumentationLink",
  "RuleSignature", "CausalInvariant", "ConnectedRule", "ReleaseDate"
};

registryMetadata[code_String] :=
  Quiet[
    Check[
      With[{entry = registryFunction[][code, All]},
        If[AssociationQ[entry], KeyTake[entry, $registryMetadataKeys], Missing["Unavailable"]]
      ],
      Missing["Unavailable"]
    ],
    ResourceObject::updavb
  ]

registryMetadata[_] := Missing["NotRecorded"]


registryVersion[] :=
  Quiet[
    Check[
      ResourceObject["WolframModelData"]["Version"],
      Missing["Unknown"]
    ],
    ResourceObject::updavb
  ]


(* Single-rule entries only: Automatic seeds stay single-rule. *)
singleRuleRegistryEntries[] :=
  With[{entries = registryEntries[]},
    If[
      entries === $Failed,
      $Failed,
      Cases[
        entries,
        entry_Association /; MatchQ[entry["Rule"], {_Rule} | _Rule] :>
          <|
            "Rule" -> Replace[entry["Rule"], {r_Rule} :> r],
            "InitialCondition" -> entry["InitialCondition"],
            "RegistryCode" -> entry["RegistryCode"]
          |>
      ]
    ]
  ]


seedResolutionFailure[message_String, details_Association : <||>] :=
  Failure[
    "SeedResolutionFailed",
    Join[<|"Message" -> message|>, details]
  ]


(* ::Section:: *)
(*Seed resolution*)


SeedIDFromCanonicalForms[canonicalRule_, canonicalState_] :=
  Hash[{canonicalRule, canonicalState}, "SHA256", "HexString"]


buildResolvedSeed[
  source_String,
  originalRule_,
  originalState_,
  registryCode_ : Missing["NotRecorded"]
] := Module[
  {canonicalRule, canonicalState, fromRegistryQ},

  canonicalRule = CanonicalRuleForm[originalRule];
  If[FailureQ[canonicalRule], Return[canonicalRule]];

  canonicalState = CanonicalStateForm[originalState];
  If[FailureQ[canonicalState], Return[canonicalState]];

  fromRegistryQ = StringQ[registryCode];

  <|
    "SeedID" -> SeedIDFromCanonicalForms[canonicalRule, canonicalState],
    "Source" -> source,
    "RegistryCode" -> registryCode,
    "RegistryMetadata" ->
      If[fromRegistryQ, registryMetadata[registryCode], Missing["NotApplicable"]],
    "RegistryVersion" ->
      If[fromRegistryQ, registryVersion[], Missing["NotApplicable"]],
    "OriginalRule" -> originalRule,
    "OriginalInitialState" -> originalState,
    "CanonicalRule" -> canonicalRule,
    "CanonicalInitialState" -> canonicalState,
    "Rule" -> canonicalRule,
    "InitialState" -> canonicalState,
    "InitiallyApplicableQ" -> RuleApplicableQ[canonicalRule, canonicalState]
  |>
]


ResolveAndCanonicalizeSeed[config_Association] := withConfigUniverse[
  config,
  Module[
  {rule, state},

  rule = Lookup[config, "Rule", Automatic];
  state = Lookup[config, "InitialState", Automatic];

  Which[

    (* Explicit rule, explicit state: preserve originals, canonicalize both.
       Applicability is recorded, not enforced: mutation may restore it. *)
    rule =!= Automatic && state =!= Automatic,
    If[
      !validRuleSpecQ[rule],
      seedResolutionFailure[
        "The supplied rule is not a hypergraph rewrite rule or rule set.",
        <|"Rule" -> rule|>
      ],
      buildResolvedSeed["User", rule, state]
    ],

    (* Explicit rule, Automatic state: the canonicalized LHS (of the first
       canonical rule of a rule set) is a guaranteed matching seed. *)
    rule =!= Automatic && state === Automatic,
    If[
      !validRuleSpecQ[rule],
      seedResolutionFailure[
        "The supplied rule is not a hypergraph rewrite rule or rule set.",
        <|"Rule" -> rule|>
      ],
      buildResolvedSeed[
        "RuleInput",
        rule,
        First @ First @ ruleList @ CanonicalRuleForm[rule]
      ]
    ],

    (* Automatic rule, explicit state: select a Registry rule that actually
       matches the supplied state. *)
    rule === Automatic && state =!= Automatic,
    Module[{entries, chosen},
      entries = singleRuleRegistryEntries[];
      If[
        entries === $Failed || !MatchQ[entries, {__Association}],
        Return @ seedResolutionFailure[
          "The Wolfram model registry could not be retrieved."
        ]
      ];
      chosen = SelectFirst[
        RandomSample[entries],
        RuleApplicableQ[#["Rule"], state] &
      ];
      If[
        MissingQ[chosen],
        seedResolutionFailure[
          "No registry rule applies to the supplied initial state.",
          <|"InitialState" -> state|>
        ],
        buildResolvedSeed["WolframModelData", chosen["Rule"], state, chosen["RegistryCode"]]
      ]
    ],

    (* Automatic rule, Automatic state: select a Registry rule-state pair,
       requiring initial applicability. *)
    True,
    Module[{entries, chosen},
      entries = singleRuleRegistryEntries[];
      If[
        entries === $Failed || !MatchQ[entries, {__Association}],
        Return @ seedResolutionFailure[
          "The Wolfram model registry could not be retrieved."
        ]
      ];
      chosen = SelectFirst[
        RandomSample[entries],
        hypergraphStateQ[#["InitialCondition"]] &&
          RuleApplicableQ[#["Rule"], #["InitialCondition"]] &
      ];
      If[
        MissingQ[chosen],
        seedResolutionFailure[
          "No applicable registry rule-state pair was found."
        ],
        buildResolvedSeed[
          "WolframModelData",
          chosen["Rule"],
          chosen["InitialCondition"],
          chosen["RegistryCode"]
        ]
      ]
    ]
  ]
  ]
]

ResolveAndCanonicalizeSeed[other_] :=
  seedResolutionFailure[
    "The configuration must be an Association.",
    <|"Value" -> other|>
  ]
