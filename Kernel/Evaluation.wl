(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Versions*)


(* Bump whenever evaluator semantics change: it is part of every evolution
   key, so cached or stored evaluations from an older evaluator are never
   reused. *)
$EvaluatorVersion = "2.0";


pacletVersionString[] := pacletVersionString[] =
  Quiet @ Check[
    Replace[PacletObject[File[$pacletRoot]]["Version"], Except[_String] -> Missing["Unknown"]],
    Missing["Unknown"]
  ]


hypergraphVersionString[] := hypergraphVersionString[] =
  Quiet @ Check[
    Replace[
      First[PacletFind["WolframInstitute/Hypergraph"], Missing["NotFound"]],
      paclet_PacletObject :> paclet["Version"]
    ],
    Missing["Unknown"]
  ]


(* ::Section:: *)
(*Canonical BFS multiway evolver*)


evolutionFailure[message_String, details_Association : <||>] :=
  Failure["EvolutionFailed", <|"Message" -> message|> ~Join~ details]


(* All canonical one-event successors of a canonical state, with the raw
   rewrite-event count before canonical deduplication, the canonical
   successor of every raw event, and every event's {rule index, matched
   edge positions}. *)
canonicalSuccessorStates[compiled_List, state_List] := Module[{raw, successors},
  raw = rawRewriteEvents[compiled, state];
  If[!ListQ[raw], Return[$Failed]];

  successors = Quiet @ Check[
    CanonicalStateForm[EdgeList[#["Hypergraph"]]] & /@ raw,
    $Failed
  ];
  If[!ListQ[successors] || AnyTrue[successors, FailureQ], Return[$Failed]];

  <|
    "EventCount" -> Length[raw],
    "RawSuccessors" -> successors,
    "Matches" -> ({#["RuleIndex"], Flatten[#["MatchEdgePositions"]]} & /@ raw),
    "Successors" -> DeleteDuplicates[successors]
  |>
]


limitsReached[status_] :=
  Replace[
    status,
    {
      "GenerationCap" -> {"MaxGenerations"},
      "EventCap" -> {"MaxEvents"},
      "StateCap" -> {"MaxStates"},
      "TimedOut" -> {"TimeConstraint"},
      _ -> {}
    }
  ]


(* Evidence for a cycle: a self-loop if one exists, otherwise one directed
   cycle, as a list of DirectedEdge. *)
cycleWitness[graph_Graph] := Module[{loops},
  loops = Select[EdgeList[graph], First[#] === Last[#] &, 1];
  If[loops =!= {}, loops, First[FindCycle[graph, Infinity, 1], {}]]
]


(* Length of the longest directed path from the initial state in an acyclic
   states graph. Every explored state is reachable from the initial state. *)
longestPathLength[graph_Graph, initial_] := Module[{order, outNeighbors, distance},
  order = TopologicalSort[graph];
  outNeighbors = GroupBy[EdgeList[graph], First -> Last];
  distance = AssociationThread[order, ConstantArray[-Infinity, Length[order]]];
  distance[initial] = 0;
  Scan[
    Function[vertex,
      If[
        distance[vertex] > -Infinity,
        Scan[
          Function[next,
            If[distance[vertex] + 1 > distance[next], distance[next] = distance[vertex] + 1]
          ],
          Lookup[outNeighbors, Key[vertex], {}]
        ]
      ]
    ],
    order
  ];
  Max[0, Select[Values[distance], NumericQ]]
]


Options[CanonicalMultiwayEvolution] = {"RecordEvents" -> False};


(* Breadth-first exploration of the canonical state space. Statuses:
     "Halted"        -- the frontier is exhausted and the explored states
                        graph has no directed cycle or self-loop: every
                        derivation from the initial state terminates (given
                        a complete canonical form);
     "CycleDetected" -- the frontier is exhausted but some branch revisits a
                        state, so that branch rewrites forever;
     "GenerationCap" | "EventCap" | "StateCap" | "TimedOut" -- a limit
                        stopped exploration; nothing about global behavior
                        is certified;
     "Invalid"       -- a rewrite application failed.
   Caps never certify terminal states: only expanded states without
   successors are terminal. "MaxStates" bounds the number of distinct
   explored states. *)
CanonicalMultiwayEvolution[
  rule_?validRuleSpecQ,
  initialState_?hypergraphStateQ,
  limits_Association : <||>,
  opts : OptionsPattern[]
] := Module[
  {
    effectiveLimits, maxGenerations, maxEvents, maxStates, timeConstraint,
    recordEvents, compiled, deadline, initial, visited, frontier, generations,
    transitions, terminals, multiplicities, eventRecords, events, status,
    statesGraph, allStates, cyclicQ, witness, longest
  },

  effectiveLimits = Join[$DefaultEvolutionLimits, limits];
  {maxGenerations, maxEvents, maxStates, timeConstraint} =
    Lookup[effectiveLimits, {"MaxGenerations", "MaxEvents", "MaxStates", "TimeConstraint"}];
  recordEvents = TrueQ[OptionValue["RecordEvents"]];

  compiled = applicationRuleSet[rule];
  deadline =
    If[timeConstraint === Infinity, Infinity, AbsoluteTime[] + timeConstraint];

  initial = CanonicalStateForm[initialState];
  visited = <|initial -> 0|>;
  frontier = {initial};
  generations = {frontier};
  transitions = Internal`Bag[];
  terminals = Internal`Bag[];
  multiplicities = Internal`Bag[];
  eventRecords = Internal`Bag[];
  events = 0;

  status = Catch[
    Do[
      Module[{next = Internal`Bag[]},
        Do[
          If[
            deadline =!= Infinity && AbsoluteTime[] > deadline,
            Throw["TimedOut", "evolution"]
          ];

          Module[
            {
              (* One expansion of a large state can take long: it runs
                 within the time left. *)
              expansion = If[
                deadline === Infinity,
                canonicalSuccessorStates[compiled, state],
                TimeConstrained[canonicalSuccessorStates[compiled, state], Max[deadline - AbsoluteTime[], 0.001], $TimedOut]
              ],
              successors
            },
            If[expansion === $TimedOut, Throw["TimedOut", "evolution"]];
            If[expansion === $Failed, Throw["Invalid", "evolution"]];

            successors = expansion["Successors"];

            events += expansion["EventCount"];
            If[
              maxEvents =!= Infinity && events > maxEvents,
              Throw["EventCap", "evolution"]
            ];

            If[successors === {}, Internal`StuffBag[terminals, state]];

            If[
              recordEvents,
              Internal`StuffBag[
                eventRecords,
                <|
                  "State" -> state,
                  "Matches" -> expansion["Matches"],
                  "Successors" -> expansion["RawSuccessors"]
                |>
              ]
            ];

            Internal`StuffBag[
              multiplicities,
              Counts[DirectedEdge[state, #] & /@ expansion["RawSuccessors"]]
            ];

            Scan[
              Function[successor,
                If[
                  !KeyExistsQ[visited, successor],
                  If[
                    maxStates =!= Infinity && Length[visited] >= maxStates,
                    Throw["StateCap", "evolution"]
                  ];
                  AssociateTo[visited, successor -> generation];
                  Internal`StuffBag[next, successor]
                ];
                Internal`StuffBag[transitions, DirectedEdge[state, successor]]
              ],
              successors
            ]
          ],
          {state, frontier}
        ];

        frontier = Internal`BagPart[next, All];
        AppendTo[generations, frontier];
        If[frontier === {}, Throw["FrontierExhausted", "evolution"]]
      ],
      {generation, maxGenerations}
    ];
    "GenerationCap",
    "evolution"
  ];

  transitions = DeleteDuplicates @ Internal`BagPart[transitions, All];
  allStates = Keys[visited];

  statesGraph = Graph[
    DeleteDuplicates @ Join[allStates, Catenate[List @@@ transitions]],
    transitions
  ];

  (* AcyclicGraphQ ignores self-loops, which are genuine one-state cycles here. *)
  cyclicQ = !AcyclicGraphQ[statesGraph] || !LoopFreeGraphQ[statesGraph];
  witness = If[cyclicQ, cycleWitness[statesGraph], Missing["NoCycle"]];

  (* An empty frontier proves the canonical state space is exhausted. That is
     a genuine global halt only when no directed cycle exists; otherwise some
     branch rewrites forever through revisited states. The trailing {} in
     "Generations" is reserved for genuine halts. *)
  If[
    status === "FrontierExhausted",
    If[
      cyclicQ,
      status = "CycleDetected";
      generations = Most[generations],
      status = "Halted"
    ]
  ];

  (* Longest derivation: exact for "Halted" (every derivation from the
     initial state is a path of the acyclic quotient and conversely); for a
     capped acyclic exploration it is the longest derivation found within
     the limits; undefined when a cycle makes derivations unbounded. *)
  longest =
    If[cyclicQ, Missing["CyclicStatesGraph"], longestPathLength[statesGraph, initial]];

  <|
    "Generations" -> generations,
    "States" -> allStates,
    "StatesGraph" -> statesGraph,
    "TransitionEdges" -> transitions,
    "TransitionMultiplicities" ->
      KeyTake[Merge[Internal`BagPart[multiplicities, All], Total], transitions],
    (* Verified by actual rule inapplicability during expansion; unexpanded
       frontier states at a cap boundary are never counted as terminal. *)
    "TerminalStates" -> DeleteDuplicates @ Internal`BagPart[terminals, All],
    "Frontier" -> Last[DeleteCases[generations, {}], {}],
    "DiscoveryGenerations" -> visited,
    "Status" -> status,
    "CycleDetectedQ" -> cyclicQ,
    "CycleWitness" -> witness,
    "LongestDerivation" -> longest,
    "LongestDerivationExactQ" -> status === "Halted",
    "EventCount" -> events,
    "LimitsReached" -> limitsReached[status],
    "EvolutionLimits" -> effectiveLimits,
    "EventRecords" ->
      If[recordEvents, Internal`BagPart[eventRecords, All], Missing["NotRequested"]],
    "EvaluatorVersion" -> $EvaluatorVersion
  |>
]

CanonicalMultiwayEvolution[rule_, state_, ___] :=
  evolutionFailure[
    "The rule or initial state is not a valid hypergraph rewrite specification.",
    <|"Rule" -> rule, "InitialState" -> state|>
  ]


(* Layered evolution list convention used by the strategy helpers:
   {gen0, gen1, ...} with a trailing {} exactly when the system halted. *)
MultiwayEvolutionList[rule_, initialState_, limits_Association : <||>] :=
  Replace[
    CanonicalMultiwayEvolution[rule, initialState, limits],
    result_Association :> result["Generations"]
  ]


(* ::Section:: *)
(*Artifacts*)


(* Evaluation artifacts beyond the canonical states graph, built only when a
   selected metric declares them ("Artifacts" or an artifact "Input") or the
   configuration requests them ("EvolutionArtifacts"). A builder receives
   the rule, the canonical initial state, the canonical evolution, the
   configuration and the artifacts already built. *)
$ArtifactBuilders = <|

  (* Produced by the BFS itself ("RecordEvents" -> True). *)
  "EventRecords" -> None,

  "EvolutionGraph" -> Function[{rule, state, evolution, config, built},
    MultiwayEvolutionGraph[evolution]
  ],

  "EventEvolution" -> Function[{rule, state, evolution, config, built},
    RewriteEventEvolution[
      rule,
      state,
      config["EvolutionLimits"],
      "UpdateOrder" -> config["UpdateOrder"]
    ]
  ],

  "CausalGraph" -> Function[{rule, state, evolution, config, built},
    Replace[built["EventEvolution"], {e_Association :> e["CausalGraph"], other_ :> other}]
  ],

  "UpdateOrderRuns" -> Function[{rule, state, evolution, config, built},
    AssociationMap[
      RewriteEventEvolution[rule, state, config["EvolutionLimits"], "UpdateOrder" -> #] &,
      config["UpdateOrders"]
    ]
  ]

|>;

$ArtifactDependencies = <|"CausalGraph" -> {"EventEvolution"}|>;

$ArtifactInputs = {"EvolutionGraph", "CausalGraph", "EventEvolution", "UpdateOrderRuns"};


registerArtifactBuilder[name_String, builder_, dependencies_List : {}] := (
  AssociateTo[$ArtifactBuilders, name -> builder];
  AssociateTo[$ArtifactDependencies, name -> dependencies];
  $ArtifactInputs = DeleteDuplicates @ Append[$ArtifactInputs, name];
  If[!MemberQ[$AllowedMetricInputs, name], AppendTo[$AllowedMetricInputs, name]];
)


expandArtifactDependencies[names_List] :=
  FixedPoint[
    DeleteDuplicates[Join[Catenate[Lookup[$ArtifactDependencies, #, {}] & /@ #], #]] &,
    names
  ]


requiredArtifacts[config_Association] := Module[{specifications},
  specifications = Values @ resolveMetricSpecifications[config];
  expandArtifactDependencies @ DeleteDuplicates @ Join[
    Replace[Lookup[config, "EvolutionArtifacts", Automatic], Automatic -> {}],
    Catenate[Lookup[#, "Artifacts", {}] & /@ specifications],
    Select[Lookup[specifications, "Input", {}], MemberQ[$ArtifactInputs, #] &]
  ]
]


(* Configuration fields an artifact value depends on, for cache keys. *)
artifactParameters[config_Association] :=
  KeyTake[config, {"UpdateOrder", "UpdateOrders", "EvolutionLimits"}]


$ArtifactCache = <||>;

buildArtifacts[names_List, rule_, state_, evolution_Association, config_Association, evolutionKey_] :=
  Module[{order, built = <||>},
    (* Dependencies first. *)
    order = SortBy[names, Length[expandArtifactDependencies[{#}]] &];
    Scan[
      Function[name,
        Module[{builder = Lookup[$ArtifactBuilders, name, None], key},
          If[
            builder =!= None,
            key = Hash[{evolutionKey, name, artifactParameters[config]}, "SHA256", "HexString"];
            built[name] =
              If[
                KeyExistsQ[$ArtifactCache, key],
                $ArtifactCache[key],
                With[{value = builder[rule, state, evolution, config, built]},
                  AssociateTo[$ArtifactCache, key -> value];
                  value
                ]
              ]
          ]
        ]
      ],
      order
    ];
    built
  ]


(* ::Section:: *)
(*Evaluation context and metric computation*)


metricInput[context_Association, input_String] :=
  Switch[input,
    "State", context["InitialState"],
    "States", context["States"],
    "FinalStates", context["FinalStates"],
    "StatesGraph", context["StatesGraph"],
    "EvaluationContext", context,
    _?(MemberQ[$ArtifactInputs, #] &), Lookup[context, input, Missing["NotRequested"]],
    _, Missing["UnknownInputLevel", input]
  ]


(* Effective specification of every selected metric: the registry or custom
   specification, then any MetricOverrides fields ("Parameters" are merged
   key by key). *)
resolveMetricSpecifications[config_Association] :=
  AssociationMap[
    Function[name,
      Module[{base, override},
        base = Lookup[
          Join[$FitnessMetricRegistry, Lookup[config, "CustomFitnessMetrics", <||>]],
          name
        ];
        override = Lookup[Lookup[config, "MetricOverrides", <||>], name, <||>];
        If[
          KeyExistsQ[override, "Parameters"],
          override = Append[
            override,
            "Parameters" -> Join[Lookup[base, "Parameters", <||>], override["Parameters"]]
          ]
        ];
        Join[base, override]
      ]
    ],
    config["FitnessMetrics"]
  ]


metricSpecificationsHash[config_Association] :=
  Hash[Normal /@ resolveMetricSpecifications[config], "SHA256", "HexString"]


(* A metric with "Parameters" receives them as a second argument. *)
applyMetricFunction[specification_Association, input_] :=
  If[
    KeyExistsQ[specification, "Parameters"],
    specification["Function"][input, specification["Parameters"]],
    specification["Function"][input]
  ]


computeFitness[context_Association, config_Association] := Module[
  {specifications},

  specifications = resolveMetricSpecifications[config];

  Association @ KeyValueMap[
    Function[{name, specification},
      name -> ValidateFitnessMetricResult[
        name,
        specification,
        Quiet @ Check[
          applyMetricFunction[
            specification,
            metricInput[context, Lookup[specification, "Input", "EvaluationContext"]]
          ],
          Failure[
            "FitnessMetricError",
            <|"Message" -> "The fitness metric raised messages.", "Metric" -> name|>
          ]
        ]
      ]
    ],
    specifications
  ]
]


buildEvaluationContext[rule_, state_, evolution_Association, runtime_] :=
  buildEvaluationContext[rule, state, evolution, runtime, <||>]

buildEvaluationContext[rule_, state_, evolution_Association, runtime_, artifacts_Association] :=
  Join[
    <|
      "Rule" -> rule,
      "InitialState" -> state,
      "Evolution" -> evolution,
      "Generations" -> evolution["Generations"],
      "States" -> evolution["States"],
      "FinalStates" -> evolution["TerminalStates"],
      "StatesGraph" -> evolution["StatesGraph"],
      "EvolutionGraph" -> Missing["NotRequested"],
      "CausalGraph" -> Missing["NotRequested"],
      "Events" -> evolution["EventCount"],
      "Frontier" -> evolution["Frontier"],
      "Status" -> evolution["Status"],
      "CycleDetectedQ" -> evolution["CycleDetectedQ"],
      "CycleWitness" -> Lookup[evolution, "CycleWitness", Missing["NotRecorded"]],
      "HaltedWithinCapQ" -> evolution["Status"] === "Halted",
      "LongestDerivation" -> Lookup[evolution, "LongestDerivation", Missing["NotRecorded"]],
      "TransitionMultiplicities" -> Lookup[evolution, "TransitionMultiplicities", <||>],
      "EventRecords" -> Lookup[evolution, "EventRecords", Missing["NotRequested"]],
      "DiscoveryGenerations" -> Lookup[evolution, "DiscoveryGenerations", <||>],
      "Runtime" -> runtime,
      "LimitsReached" -> limitsReached[evolution["Status"]]
    |>,
    KeyDrop[artifacts, "EventRecords"],
    <|"Artifacts" -> Keys[artifacts]|>
  ]


(* ::Section:: *)
(*Candidate evaluation with behavioral caching*)


(* Every behavior-changing policy and implementation version is part of the
   evolution identity. The mutation strategy is deliberately excluded: two
   strategies reaching the same canonical rule under the same configuration
   share one evolution. *)
evolutionIdentity[rule_, state_, limits_Association, recordEvents_] :=
  {
    rule, state, Normal @ KeySort[limits],
    "CanonicalBFS", $EvaluatorVersion,
    universeTag[], $RewriteSemantics,
    TrueQ[recordEvents],
    hypergraphVersionString[], pacletVersionString[], $VersionNumber
  }


CandidateEvaluationKey[rule_, state_, limits_Association] :=
  CandidateEvaluationKey[rule, state, limits, False]

CandidateEvaluationKey[rule_, state_, limits_Association, recordEvents_] :=
  Hash[evolutionIdentity[rule, state, limits, recordEvents], "SHA256", "HexString"]


(* Evolution cache (keyed by evolution identity), artifact cache and fitness
   cache (keyed by evolution identity, effective metric specifications and
   artifact parameters). *)
$EvaluationCache = <||>;
$FitnessCache = <||>;

ClearEvaluationCache[] := (
  $EvaluationCache = <||>;
  $ArtifactCache = <||>;
  $FitnessCache = <||>;
)


(* Git checkout of the paclet source: <|"Commit", "Dirty", "RootIsPacletRoot"|>,
   Null where unknown (no git, or not a checkout). Commit is the HEAD hash,
   Dirty says whether tracked files differ from it, and RootIsPacletRoot is
   False when the paclet sits inside an enclosing repository. *)
$noGitInformation = <|"Commit" -> Null, "Dirty" -> Null, "RootIsPacletRoot" -> Null|>;

pacletGitInformation[] := Module[{run, lines, commit, root, status},
  run = Quiet @ Check[
    RunProcess[{"git", "rev-parse", "HEAD", "--show-toplevel"}, ProcessDirectory -> $pacletRoot],
    $Failed
  ];
  If[!AssociationQ[run] || run["ExitCode"] =!= 0, Return[$noGitInformation]];
  lines = Select[StringTrim /@ StringSplit[run["StandardOutput"], {"\r\n", "\n"}], # =!= "" &];
  commit = SelectFirst[lines, StringMatchQ[#, RegularExpression["[0-9a-f]{40}"]] &, Null];
  If[commit === Null, Return[$noGitInformation]];
  root = SelectFirst[lines, # =!= commit &, Null];
  status = Quiet @ Check[
    RunProcess[{"git", "status", "--porcelain", "--untracked-files=no"}, ProcessDirectory -> $pacletRoot],
    $Failed
  ];
  <|
    "Commit" -> commit,
    "Dirty" -> If[
      AssociationQ[status] && status["ExitCode"] === 0,
      StringTrim[status["StandardOutput"]] =!= "",
      Null
    ],
    "RootIsPacletRoot" -> If[
      StringQ[root],
      ToLowerCase[ExpandFileName[FileNameJoin[FileNameSplit[root]]]] === ToLowerCase[ExpandFileName[$pacletRoot]],
      Null
    ]
  |>
]


(* Behavior fields of an evaluated candidate (everything except identity,
   lineage and provenance). *)
$BehaviorKeys = {
  "Status", "CycleDetectedQ", "Fitness", "Runtime", "Generations", "States",
  "FinalStates", "StatesGraph", "TransitionCount", "HaltedWithinCapQ",
  "LimitsReached", "LongestDerivation", "CycleWitness",
  "TransitionMultiplicities", "EventCount"
};


(* Cross-run reuse: behaviors stored by an earlier run, keyed by EvaluationID
   (which covers the evolution identity, the effective metric specifications
   and the artifact parameters). Consulted only when a run has
   "ReuseEvaluations" -> True (StructureAdaptiveEvolution Blocks it to <||>
   otherwise) and by direct EvaluateCandidate calls. "TimedOut" behaviors are
   machine-dependent and are never preloaded. *)
$PreloadedEvaluations = <||>;

preloadEvaluations[behaviors_Association] := Module[{usable},
  usable = Select[behaviors, AssociationQ[#] && Lookup[#, "Status", "TimedOut"] =!= "TimedOut" &];
  $PreloadedEvaluations = Join[$PreloadedEvaluations, KeyTake[#, $BehaviorKeys] & /@ usable];
  Length[usable]
]

clearPreloadedEvaluations[] := ($PreloadedEvaluations = <||>;)

ClearPreloadedEvaluations[] := clearPreloadedEvaluations[]


(* Run statistics, Block-scoped by StructureAdaptiveEvolution. *)
$evaluationStatistics = None;

countStatistic[name_String, amount_ : 1] :=
  If[
    AssociationQ[$evaluationStatistics],
    $evaluationStatistics[name] = Lookup[$evaluationStatistics, name, 0] + amount
  ]


CandidateIDFromForms[rule_, state_] :=
  Hash[{rule, state}, "SHA256", "HexString"]


validCandidateQ[candidate_Association] :=
  candidate["Status"] =!= "Invalid" &&
    AllTrue[Values @ candidate["Fitness"], !FailureQ[#] &]


runEvolution[rule_, state_, limits_Association, recordEvents_] := Module[{runtime, evolution},
  {runtime, evolution} =
    AbsoluteTiming[CanonicalMultiwayEvolution[rule, state, limits, "RecordEvents" -> recordEvents]];
  <|"Runtime" -> runtime, "Evolution" -> evolution|>
]


invalidBehavior[evolution_, runtime_] := <|
  "Status" -> "Invalid",
  "CycleDetectedQ" -> Missing["NotEvaluated"],
  "Fitness" -> <||>,
  "Runtime" -> runtime,
  "Generations" -> {},
  "States" -> {},
  "FinalStates" -> {},
  "StatesGraph" -> Graph[{}, {}],
  "TransitionCount" -> 0,
  "HaltedWithinCapQ" -> False,
  "LimitsReached" -> {},
  "LongestDerivation" -> Missing["NotEvaluated"],
  "CycleWitness" -> Missing["NotEvaluated"],
  "TransitionMultiplicities" -> <||>,
  "EventCount" -> 0,
  "EvaluationFailure" -> evolution
|>


EvaluateCandidate[candidate_Association, config_Association] := withConfigUniverse[
  config,
  Module[
  {
    rule, state, limits, artifactNames, recordEvents, key, record, evolution,
    runtime, artifacts, context, fitnessKey, fitness, behavior
  },

  rule = candidate["Rule"];
  state = candidate["InitialState"];
  limits = config["EvolutionLimits"];
  artifactNames = requiredArtifacts[config];
  recordEvents = MemberQ[artifactNames, "EventRecords"];
  key = CandidateEvaluationKey[rule, state, limits, recordEvents];

  fitnessKey = Hash[
    {key, metricSpecificationsHash[config], artifactParameters[config]},
    "SHA256",
    "HexString"
  ];

  If[
    KeyExistsQ[$PreloadedEvaluations, fitnessKey],
    countStatistic["PreloadedHits"];
    behavior = $PreloadedEvaluations[fitnessKey];
    Return @ Join[
      candidate,
      behavior,
      <|
        "EvolutionKey" -> key,
        "EvaluationID" -> fitnessKey,
        "ValidQ" -> validCandidateQ[Join[candidate, behavior]]
      |>
    ]
  ];

  record = Lookup[$EvaluationCache, key, None];
  If[
    record === None,
    record = runEvolution[rule, state, limits, recordEvents];
    AssociateTo[$EvaluationCache, key -> record];
    countStatistic["FreshEvolutions"];
    countStatistic["EvolutionTime", record["Runtime"]],
    countStatistic["CacheHits"]
  ];

  {runtime, evolution} = Lookup[record, {"Runtime", "Evolution"}];

  If[
    FailureQ[evolution],
    behavior = invalidBehavior[evolution, runtime];
    Return @ Join[
      candidate,
      behavior,
      <|
        "EvolutionKey" -> key,
        "EvaluationID" -> key,
        "ValidQ" -> False
      |>
    ]
  ];

  artifacts = buildArtifacts[artifactNames, rule, state, evolution, config, key];
  context = buildEvaluationContext[rule, state, evolution, runtime, artifacts];

  fitness = Lookup[$FitnessCache, fitnessKey, None];
  If[
    fitness === None,
    fitness = computeFitness[context, config];
    AssociateTo[$FitnessCache, fitnessKey -> fitness]
  ];

  behavior = <|
    "Status" -> context["Status"],
    "CycleDetectedQ" -> context["CycleDetectedQ"],
    "Fitness" -> fitness,
    "Runtime" -> runtime,
    "Generations" -> context["Generations"],
    "States" -> context["States"],
    "FinalStates" -> context["FinalStates"],
    "StatesGraph" -> context["StatesGraph"],
    "TransitionCount" -> EdgeCount[context["StatesGraph"]],
    "HaltedWithinCapQ" -> context["HaltedWithinCapQ"],
    "LimitsReached" -> context["LimitsReached"],
    "LongestDerivation" -> context["LongestDerivation"],
    "CycleWitness" -> context["CycleWitness"],
    "TransitionMultiplicities" -> context["TransitionMultiplicities"],
    "EventCount" -> context["Events"]
  |>;

  Join[
    candidate,
    behavior,
    <|
      "EvolutionKey" -> key,
      "EvaluationID" -> fitnessKey,
      "ValidQ" -> validCandidateQ[Join[candidate, behavior]]
    |>
  ]
  ]
]
