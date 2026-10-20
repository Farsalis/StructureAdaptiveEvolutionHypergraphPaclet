(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Canonical BFS multiway evolver*)


evolutionFailure[message_String, details_Association : <||>] :=
  Failure["EvolutionFailed", <|"Message" -> message|> ~Join~ details]


(* All canonical one-event successors of a canonical state, together with the
   raw rewrite-event count before canonical deduplication. *)
canonicalSuccessorStates[hrule_, state_] := Module[{raw},
  raw = Quiet @ Check[hrule[modeHypergraph[state]], $Failed];

  If[
    !ListQ[raw],
    $Failed,
    <|
      "EventCount" -> Length[raw],
      "Successors" -> DeleteDuplicates[
        CanonicalStateForm[EdgeList[#["Hypergraph"]]] & /@ raw
      ]
    |>
  ]
]


CanonicalMultiwayEvolution[
  rule_?validHypergraphRuleQ,
  initialState_?hypergraphStateQ,
  limits_Association : <||>
] := Module[
  {
    effectiveLimits, maxGenerations, maxEvents, timeConstraint,
    hrule, deadline, initial, visited, frontier, generations,
    transitions, terminals, events, status, statesGraph, allStates, cyclicQ
  },

  effectiveLimits = Join[$DefaultEvolutionLimits, limits];
  maxGenerations = effectiveLimits["MaxGenerations"];
  maxEvents = effectiveLimits["MaxEvents"];
  timeConstraint = effectiveLimits["TimeConstraint"];

  hrule = toApplicationRule[rule];
  deadline =
    If[timeConstraint === Infinity, Infinity, AbsoluteTime[] + timeConstraint];

  initial = CanonicalStateForm[initialState];
  visited = <|initial -> True|>;
  frontier = {initial};
  generations = {frontier};
  transitions = Internal`Bag[];
  terminals = Internal`Bag[];
  events = 0;

  status = Catch[
    Do[
      Module[{next = Internal`Bag[]},
        Do[
          If[
            deadline =!= Infinity && AbsoluteTime[] > deadline,
            Throw["TimedOut", "evolution"]
          ];

          Module[{expansion = canonicalSuccessorStates[hrule, state], successors},
            If[expansion === $Failed, Throw["Invalid", "evolution"]];

            successors = expansion["Successors"];

            events += expansion["EventCount"];
            If[
              maxEvents =!= Infinity && events > maxEvents,
              Throw["EventCap", "evolution"]
            ];

            If[successors === {}, Internal`StuffBag[terminals, state]];

            Scan[
              (
                Internal`StuffBag[transitions, DirectedEdge[state, #]];
                If[
                  !KeyExistsQ[visited, #],
                  AssociateTo[visited, # -> True];
                  Internal`StuffBag[next, #]
                ]
              ) &,
              successors
            ]
          ],
          {state, frontier}
        ];

        frontier = Internal`BagPart[next, All];
        AppendTo[generations, frontier];
        If[frontier === {}, Throw["FrontierExhausted", "evolution"]]
      ],
      {maxGenerations}
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

  <|
    "Generations" -> generations,
    "States" -> allStates,
    "StatesGraph" -> statesGraph,
    "TransitionEdges" -> transitions,
    (* Verified by actual rule inapplicability during expansion; unexpanded
       frontier states at a cap boundary are never counted as terminal. *)
    "TerminalStates" -> DeleteDuplicates @ Internal`BagPart[terminals, All],
    "Frontier" -> Last[DeleteCases[generations, {}], {}],
    "Status" -> status,
    "CycleDetectedQ" -> cyclicQ,
    "EventCount" -> events,
    "EvolutionLimits" -> effectiveLimits
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
(*Evaluation context and metric computation*)


metricInput[context_Association, input_String] :=
  Switch[input,
    "State", context["InitialState"],
    "States", context["States"],
    "FinalStates", context["FinalStates"],
    "StatesGraph", context["StatesGraph"],
    "EvolutionGraph", context["EvolutionGraph"],
    "CausalGraph", context["CausalGraph"],
    "EvaluationContext", context,
    _, Missing["UnknownInputLevel", input]
  ]


resolveMetricSpecifications[config_Association] :=
  AssociationMap[
    Lookup[
      Join[$FitnessMetricRegistry, config["CustomFitnessMetrics"]],
      #
    ] &,
    config["FitnessMetrics"]
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
          specification["Function"][
            metricInput[context, specification["Input"]]
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


buildEvaluationContext[rule_, state_, evolution_Association, runtime_] := <|
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
  "HaltedWithinCapQ" -> evolution["Status"] === "Halted",
  "Runtime" -> runtime,
  "LimitsReached" -> Replace[
    evolution["Status"],
    {
      "GenerationCap" -> {"MaxGenerations"},
      "EventCap" -> {"MaxEvents"},
      "TimedOut" -> {"TimeConstraint"},
      _ -> {}
    }
  ]
|>


(* ::Section:: *)
(*Candidate evaluation with behavioral caching*)


(* The mutation strategy is deliberately excluded: two strategies reaching the
   same canonical rule under the same configuration share one evaluation. The
   state-equivalence and rewrite-semantics tags keep the different universes
   in separate keys. *)
CandidateEvaluationKey[rule_, state_, limits_Association] :=
  Hash[
    {
      rule, state, Normal @ KeySort[limits], "CanonicalBFS",
      If[$EdgeSymmetry === "Ordered", "OrderedMultiset", "UnorderedSimple"],
      $RewriteSemantics
    },
    "SHA256",
    "HexString"
  ]


$EvaluationCache = <||>;

ClearEvaluationCache[] := ($EvaluationCache = <||>;)


CandidateIDFromForms[rule_, state_] :=
  Hash[{rule, state}, "SHA256", "HexString"]


validCandidateQ[candidate_Association] :=
  candidate["Status"] =!= "Invalid" &&
    AllTrue[Values @ candidate["Fitness"], !FailureQ[#] &]


evaluateBehavior[rule_, state_, config_Association] := Module[
  {limits, runtime, evolution, context, fitness},

  limits = config["EvolutionLimits"];
  {runtime, evolution} =
    AbsoluteTiming[CanonicalMultiwayEvolution[rule, state, limits]];

  If[
    FailureQ[evolution],
    Return @ <|
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
      "EvaluationFailure" -> evolution
    |>
  ];

  context = buildEvaluationContext[rule, state, evolution, runtime];
  fitness = computeFitness[context, config];

  <|
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
    "LimitsReached" -> context["LimitsReached"]
  |>
]


EvaluateCandidate[candidate_Association, config_Association] := Block[
  {
    $EdgeSymmetry = Lookup[config, "EdgeSymmetry", "Unordered"],
    $RewriteSemantics = Lookup[config, "RewriteSemantics", "EdgeToken"]
  },
  Module[
  {rule, state, key, behavior},

  rule = candidate["Rule"];
  state = candidate["InitialState"];
  key = CandidateEvaluationKey[rule, state, config["EvolutionLimits"]];

  behavior =
    If[
      KeyExistsQ[$EvaluationCache, key],
      $EvaluationCache[key],
      With[{fresh = evaluateBehavior[rule, state, config]},
        AssociateTo[$EvaluationCache, key -> fresh];
        fresh
      ]
    ];

  Join[
    candidate,
    behavior,
    <|
      "EvolutionKey" -> key,
      "ValidQ" -> validCandidateQ[Join[candidate, behavior]]
    |>
  ]
  ]
]
