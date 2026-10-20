(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Event-level single-way evolution*)


(* A single-way evolution that keeps explicit event and edge identities.

   Edges carry integer IDs in creation order (the initial edges are 1..m) and
   a generation: an initial edge has generation 0, an edge produced by an
   event has the event's generation, and an event's generation is one more
   than the largest generation of the edges it consumes (its causal depth).
   An event consumes its matched edges and produces the instantiated RHS
   edges with fresh vertices; under "VertexDeletion" semantics an untouched
   edge that loses a deleted vertex is also consumed and re-produced, since
   the event changed it.

   Update orders choose the events applied at each step:
     "Generational" -- a maximal set of pairwise edge-disjoint events, picked
                       greedily in (generation, rule, consumed IDs) order and
                       applied simultaneously (one event per step under
                       "VertexDeletion");
     "Sequential"   -- one event: least (rule index, sorted consumed IDs);
     "LeastRecent"  -- one event: the one consuming the oldest edges;
     "MostRecent"   -- one event: the one consuming the newest edges;
     {"Random", s}  -- one event chosen with a private generator seeded by
                       {s, step}; the session generator is untouched.

   Statuses: "Terminated" (no applicable event: the final state is
   terminal), "GenerationCap" (only events beyond "MaxGenerations" remain),
   "EventCap" ("MaxEvents" events applied), "TimedOut", "Invalid". *)

Options[RewriteEventEvolution] = {
  "UpdateOrder" -> "Generational",
  "IncludeInitialEvent" -> False
};


eventOrderKey[candidate_Association] :=
  {candidate["Generation"], candidate["RuleIndex"], Sort[candidate["Consumed"]], candidate["Index"]}


selectEvents[candidates_List, order_, step_Integer, semantics_String] :=
  Switch[
    order,
    "Generational",
      If[
        semantics === "VertexDeletion",
        {First @ SortBy[candidates, eventOrderKey]},
        Module[{used = <||>, chosen = Internal`Bag[]},
          Scan[
            Function[candidate,
              If[
                NoneTrue[candidate["Consumed"], KeyExistsQ[used, #] &],
                Scan[(used[#] = True) &, candidate["Consumed"]];
                Internal`StuffBag[chosen, candidate]
              ]
            ],
            SortBy[candidates, eventOrderKey]
          ];
          Internal`BagPart[chosen, All]
        ]
      ],
    "Sequential",
      {First @ SortBy[candidates, {#["RuleIndex"], Sort[#["Consumed"]], #["Index"]} &]},
    "LeastRecent",
      {First @ SortBy[candidates, {Sort[#["Consumed"]], #["RuleIndex"], #["Index"]} &]},
    "MostRecent",
      {First @ SortBy[candidates, {-ReverseSort[#["Consumed"]], #["RuleIndex"], #["Index"]} &]},
    {"Random", _Integer},
      {BlockRandom[SeedRandom[Hash[{order[[2]], step}]]; RandomChoice[candidates]]}
  ]


RewriteEventEvolution[
  rule_?validRuleSpecQ,
  initialState_?hypergraphStateQ,
  limits_Association : <||>,
  opts : OptionsPattern[]
] := Module[
  {
    effectiveLimits, maxGenerations, maxEvents, timeConstraint, order, compiled,
    deadline, normalized, vertices, index, nextVertex, edgeRecords, live,
    nextEdgeID = 1, eventCount = 0, eventBag = Internal`Bag[],
    stateBag = Internal`Bag[], liveBag = Internal`Bag[], step = 0, status,
    events, causalEdges, causalVertices, finalState
  },

  effectiveLimits = Join[$DefaultEvolutionLimits, limits];
  {maxGenerations, maxEvents, timeConstraint} =
    Lookup[effectiveLimits, {"MaxGenerations", "MaxEvents", "TimeConstraint"}];
  order = OptionValue["UpdateOrder"];
  If[
    !validUpdateOrderQ[order],
    Return @ evolutionFailure["Invalid update order.", <|"UpdateOrder" -> order|>]
  ];

  compiled = applicationRuleSet[rule];
  deadline = If[timeConstraint === Infinity, Infinity, AbsoluteTime[] + timeConstraint];

  normalized = normalizeStateEdges[initialState];
  vertices = DeleteDuplicates @ Flatten[normalized];
  index = AssociationThread[vertices, Range @ Length[vertices]];
  nextVertex = Length[vertices] + 1;

  edgeRecords = <||>;
  Scan[
    Function[edge,
      edgeRecords[nextEdgeID] = <|
        "Edge" -> Map[index, edge],
        "Generation" -> 0,
        "Creator" -> 0,
        "Destroyer" -> Missing["Live"]
      |>;
      nextEdgeID++
    ],
    normalized
  ];
  live = Keys[edgeRecords];

  Internal`StuffBag[stateBag, edgeRecords[#]["Edge"] & /@ live];
  Internal`StuffBag[liveBag, live];

  status = Catch[
    While[True,
      Module[{current, raw, candidates, admissible, chosen},
        If[deadline =!= Infinity && AbsoluteTime[] > deadline, Throw["TimedOut", "events"]];
        If[maxEvents =!= Infinity && eventCount >= maxEvents, Throw["EventCap", "events"]];

        current = edgeRecords[#]["Edge"] & /@ live;
        (* Matching a large state can take long: it runs within the time left. *)
        raw = If[
          deadline === Infinity,
          rawRewriteEvents[compiled, current],
          TimeConstrained[rawRewriteEvents[compiled, current], Max[deadline - AbsoluteTime[], 0.001], $TimedOut]
        ];
        If[raw === $TimedOut, Throw["TimedOut", "events"]];
        If[raw === $Failed, Throw["Invalid", "events"]];
        If[raw === {}, Throw["Terminated", "events"]];

        candidates = MapIndexed[
          Function[{event, position},
            With[{consumed = live[[Flatten[event["MatchEdgePositions"]]]]},
              <|
                "Index" -> First[position],
                "RuleIndex" -> event["RuleIndex"],
                "Consumed" -> consumed,
                "Generation" -> 1 + Max[0, edgeRecords[#]["Generation"] & /@ consumed],
                "Raw" -> event
              |>
            ]
          ],
          raw
        ];

        admissible = Select[candidates, #["Generation"] <= maxGenerations &];
        If[admissible === {}, Throw["GenerationCap", "events"]];

        chosen = selectEvents[admissible, order, step, $RewriteSemantics];
        If[
          maxEvents =!= Infinity,
          chosen = Take[chosen, UpTo[maxEvents - eventCount]]
        ];

        Scan[
          Function[candidate,
            Module[{event = candidate["Raw"], fresh, newEdges, deleted, modified, consumed, produced},
              fresh = Table[nextVertex++, {Length[Lookup[event, "NewVertices", {}]]}];
              newEdges = Lookup[event, "NewEdges", {}] /.
                Dispatch[Thread[Lookup[event, "NewVertices", {}] -> fresh]];

              (* Under "VertexDeletion" an untouched edge that loses a
                 deleted vertex is changed by the event. *)
              deleted = If[
                $RewriteSemantics === "VertexDeletion",
                Lookup[event, "DeletedVertices", {}],
                {}
              ];
              modified = If[
                deleted === {},
                {},
                Select[
                  Complement[live, candidate["Consumed"]],
                  IntersectingQ[edgeRecords[#]["Edge"], deleted] &
                ]
              ];

              consumed = Join[candidate["Consumed"], modified];
              newEdges = Join[
                newEdges,
                DeleteCases[edgeRecords[#]["Edge"], Alternatives @@ deleted] & /@ modified
              ];

              eventCount++;
              produced = Table[
                With[{id = nextEdgeID++},
                  edgeRecords[id] = <|
                    "Edge" -> newEdge,
                    "Generation" -> candidate["Generation"],
                    "Creator" -> eventCount,
                    "Destroyer" -> Missing["Live"]
                  |>;
                  id
                ],
                {newEdge, newEdges}
              ];
              Scan[
                (edgeRecords[#] = Append[edgeRecords[#], "Destroyer" -> eventCount]) &,
                consumed
              ];

              Internal`StuffBag[
                eventBag,
                <|
                  "EventID" -> eventCount,
                  "Step" -> step + 1,
                  "Generation" -> candidate["Generation"],
                  "RuleIndex" -> candidate["RuleIndex"],
                  "Inputs" -> consumed,
                  "Outputs" -> produced
                |>
              ];

              live = Join[DeleteCases[live, Alternatives @@ consumed], produced]
            ]
          ],
          chosen
        ];

        step++;

        (* Unordered universe: simple-hypergraph semantics, as in the
           multiway evaluator. Copies of one edge are merged after the step
           into the oldest copy; a merged copy records the edge it was merged
           into. (A simultaneous "Generational" step deduplicates after all
           its events, which in rare cases differs from applying them one by
           one.) *)
        If[
          $EdgeSymmetry === "Unordered",
          Module[{groups},
            groups = Select[GatherBy[live, Sort[edgeRecords[#]["Edge"]] &], Length[#] > 1 &];
            Scan[
              Function[group,
                Scan[
                  (edgeRecords[#] = Append[edgeRecords[#], "Destroyer" -> Missing["MergedInto", Min[group]]]) &,
                  DeleteCases[group, Min[group]]
                ]
              ],
              groups
            ];
            live = DeleteCases[live, Alternatives @@ Catenate[DeleteCases[#, Min[#]] & /@ groups]]
          ]
        ];

        Internal`StuffBag[stateBag, edgeRecords[#]["Edge"] & /@ live];
        Internal`StuffBag[liveBag, live]
      ]
    ],
    "events"
  ];

  events = Internal`BagPart[eventBag, All];

  causalEdges = Catenate @ Map[
    Function[event,
      DirectedEdge[edgeRecords[#]["Creator"], event["EventID"]] & /@
        If[
          TrueQ[OptionValue["IncludeInitialEvent"]],
          event["Inputs"],
          Select[event["Inputs"], edgeRecords[#]["Creator"] =!= 0 &]
        ]
    ],
    events
  ];
  causalVertices = Join[
    If[TrueQ[OptionValue["IncludeInitialEvent"]], {0}, {}],
    Lookup[events, "EventID", {}]
  ];

  finalState = edgeRecords[#]["Edge"] & /@ live;

  <|
    "Rule" -> rule,
    "UpdateOrder" -> order,
    "Status" -> status,
    "EdgeSymmetry" -> universeTag[],
    "RewriteSemantics" -> $RewriteSemantics,
    "Events" -> events,
    "EdgeRecords" -> edgeRecords,
    "States" -> Internal`BagPart[stateBag, All],
    "LiveEdges" -> Internal`BagPart[liveBag, All],
    "FinalState" -> finalState,
    "CanonicalFinalState" -> CanonicalStateForm[finalState],
    "EventCount" -> eventCount,
    "StepCount" -> step,
    "MaxGeneration" -> Max[0, Lookup[events, "Generation", {}]],
    "CausalGraph" -> Graph[causalVertices, causalEdges],
    "EvolutionLimits" -> effectiveLimits
  |>
]

RewriteEventEvolution[rule_, state_, ___] :=
  evolutionFailure[
    "The rule or initial state is not a valid hypergraph rewrite specification.",
    <|"Rule" -> rule, "InitialState" -> state|>
  ]


(* ::Section:: *)
(*Generation-unrolled multiway evolution graph*)


(* The canonical states graph merges a state with every later occurrence.
   The evolution graph keeps occurrences apart by generation: vertex
   {state, k} for a state reachable in exactly k events, with an edge
   {s, k} -> {t, k + 1} for every transition s -> t of the states graph.
   Unrolling stops at the first empty layer or after maxDepth layers
   (default: the run's "MaxGenerations"); a cycle makes the unrolled graph
   infinite, so the depth bound matters there. States left unexpanded at a
   cap have no recorded successors, so unrolling stops at them. *)
MultiwayEvolutionGraph[evolution_Association, maxDepth_ : Automatic] := Module[
  {graph, initial, depth, outNeighbors, layers, edges = Internal`Bag[], vertices},

  graph = evolution["StatesGraph"];
  initial = First @ First @ evolution["Generations"];
  depth = Replace[
    maxDepth,
    Automatic :> Lookup[Lookup[evolution, "EvolutionLimits", <||>], "MaxGenerations", 10]
  ];
  outNeighbors = GroupBy[EdgeList[graph], First -> Last];

  layers = {{initial}};
  Do[
    Module[{current = Last[layers], next},
      Scan[
        Function[source,
          Scan[
            Internal`StuffBag[edges, DirectedEdge[{source, k - 1}, {#, k}]] &,
            Lookup[outNeighbors, Key[source], {}]
          ]
        ],
        current
      ];
      next = DeleteDuplicates @ Catenate[Lookup[outNeighbors, Key[#], {}] & /@ current];
      If[next === {}, Break[]];
      AppendTo[layers, next]
    ],
    {k, 1, depth}
  ];

  vertices = Catenate @ MapIndexed[
    Function[{layer, position}, {#, First[position] - 1} & /@ layer],
    layers
  ];

  Graph[vertices, DeleteDuplicates @ Internal`BagPart[edges, All]]
]

MultiwayEvolutionGraph[other_, ___] :=
  Failure[
    "InvalidEvolution",
    <|"Message" -> "MultiwayEvolutionGraph expects a CanonicalMultiwayEvolution result.", "Value" -> Short[other]|>
  ]
