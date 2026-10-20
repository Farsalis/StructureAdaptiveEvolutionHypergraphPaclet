(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Objective normalization*)


resolveObjectiveRange[specification_Association, config_Association] :=
  Lookup[specification, "Range", Lookup[config, "RatioRange", {0., Infinity}]]


rangeDistance[value_?NumericQ, {min_, max_}] :=
  Which[
    value < min, N[min - value],
    max =!= Infinity && value > max, N[value - max],
    True, 0.
  ]


(* Every objective becomes a minimization coordinate. *)
NormalizedObjectiveValue[value_, specification_Association, config_Association] :=
  Which[
    MatchQ[value, True | False],
    Switch[specification["Direction"],
      "Minimize", Boole[value],
      _, Boole[!value]
    ],

    !NumericQ[value],
    Missing["NonNumericMetricValue"],

    True,
    Switch[specification["Direction"],
      "Maximize", -value,
      "Minimize", value,
      "Target", Abs[value - specification["Target"]],
      "Range", rangeDistance[value, resolveObjectiveRange[specification, config]],
      _, Missing["UnknownDirection", specification["Direction"]]
    ]
  ]


DominatesQ[a_List, b_List] /; Length[a] === Length[b] :=
  And @@ MapThread[#1 <= #2 &, {a, b}] &&
    Or @@ MapThread[#1 < #2 &, {a, b}]


(* ::Section:: *)
(*Front computation*)


objectiveSpecifications[config_Association] :=
  Select[
    resolveMetricSpecifications[config],
    #["Stage"] === "Objective" &
  ]


constraintSpecifications[config_Association] :=
  Select[
    resolveMetricSpecifications[config],
    #["Stage"] === "Constraint" &
  ]


CandidateObjectiveVector[candidate_Association, config_Association] := Module[
  {specifications, vector},

  specifications = objectiveSpecifications[config];

  vector = KeyValueMap[
    NormalizedObjectiveValue[
      Lookup[candidate["Fitness"], #1, Missing["NotComputed"]],
      #2,
      config
    ] &,
    specifications
  ];

  If[AllTrue[vector, NumericQ], vector, Missing["IncompleteObjectiveVector"]]
]


constraintSatisfiedQ[value_, specification_Association, config_Association] :=
  Which[
    MatchQ[value, True | False],
    TrueQ[value],

    specification["Direction"] === "Range" && NumericQ[value],
    rangeDistance[value, resolveObjectiveRange[specification, config]] == 0,

    True,
    NumericQ[value]
  ]


SatisfiesConstraintsQ[candidate_Association, config_Association] :=
  AllTrue[
    Normal @ constraintSpecifications[config],
    constraintSatisfiedQ[
      Lookup[candidate["Fitness"], First[#], Missing["NotComputed"]],
      Last[#],
      config
    ] &
  ]


(* Nondominated subset; duplicate objective vectors are all retained. *)
paretoFrontOf[candidates_List, config_Association] := Module[
  {scored, vectors},

  scored = Select[
    {#, CandidateObjectiveVector[#, config]} & /@ candidates,
    ListQ[Last[#]] &
  ];

  vectors = Last /@ scored;

  First /@ Select[
    scored,
    Function[pair, NoneTrue[vectors, DominatesQ[#, Last[pair]] &]]
  ]
]


SearchParetoFront[candidates_List, config_Association] :=
  paretoFrontOf[Select[candidates, TrueQ[#["ValidQ"]] &], config]


solutionEligibleQ[candidate_Association, config_Association] :=
  TrueQ[candidate["ValidQ"]] &&
    candidate["Status"] === "Halted" &&
    (* Nontriviality: at least one transition occurred. *)
    candidate["TransitionCount"] >= 1 &&
    SatisfiesConstraintsQ[candidate, config]


SolutionParetoFront[candidates_List, config_Association] :=
  paretoFrontOf[Select[candidates, solutionEligibleQ[#, config] &], config]


championsOverSpecifications[
  candidates_List,
  specifications_Association,
  config_Association
] := Module[
  {valid},

  valid = Select[candidates, TrueQ[#["ValidQ"]] &];

  Association @ KeyValueMap[
    Function[{name, specification},
      Module[{scored},
        scored = Select[
          {#, NormalizedObjectiveValue[
            Lookup[#["Fitness"], name, Missing["NotComputed"]],
            specification,
            config
          ]} & /@ valid,
          NumericQ[Last[#]] &
        ];
        name -> If[
          scored === {},
          Missing["NoValidCandidate"],
          First[First[MinimalBy[scored, Last]]]["CandidateID"]
        ]
      ]
    ],
    specifications
  ]
]


MetricChampions[candidates_List, config_Association] :=
  championsOverSpecifications[
    candidates,
    resolveMetricSpecifications[config],
    config
  ]


(* ::Section:: *)
(*Adaptive strategy weights*)


EqualStrategyWeights[strategies : {__String}] :=
  AssociationThread[strategies, ConstantArray[1./Length[strategies], Length[strategies]]]


(* Provisional deterministic credit formula from handoff section 9.10. *)
UpdateStrategyWeights[
  oldWeights_Association,
  trials_Association,
  roundCandidates_List,
  searchFront_List,
  solutionFront_List
] := Module[
  {
    strategies, searchFrontIDs, solutionFrontIDs, byStrategy,
    rates, rawCredit, alpha = 0.25, epsilon, targetValues, newValues
  },

  strategies = Keys[oldWeights];

  If[Total[Values[trials]] === 0, Return[<|"Weights" -> oldWeights, "Rates" -> <||>|>]];

  searchFrontIDs = Lookup[searchFront, "CandidateID", {}];
  solutionFrontIDs = Lookup[solutionFront, "CandidateID", {}];

  byStrategy = GroupBy[roundCandidates, #["Strategy"] &];

  rates = AssociationMap[
    Function[strategy,
      Module[{n = Lookup[trials, strategy, 0], proposed},
        proposed = Lookup[byStrategy, strategy, {}];
        If[
          n === 0,
          <|
            "Trials" -> 0,
            "ValidRate" -> 0., "SearchFrontRate" -> 0.,
            "HaltedRate" -> 0., "SolutionFrontRate" -> 0.
          |>,
          <|
            "Trials" -> n,
            "ValidRate" -> N[Count[proposed, _?(TrueQ[#["ValidQ"]] &)]/n],
            "SearchFrontRate" ->
              N[Count[proposed, _?(MemberQ[searchFrontIDs, #["CandidateID"]] &)]/n],
            "HaltedRate" ->
              N[Count[proposed, _?(#["Status"] === "Halted" &)]/n],
            "SolutionFrontRate" ->
              N[Count[proposed, _?(MemberQ[solutionFrontIDs, #["CandidateID"]] &)]/n]
          |>
        ]
      ]
    ],
    strategies
  ];

  rawCredit =
    (#["ValidRate"] + #["SearchFrontRate"] +
      2 #["HaltedRate"] + 3 #["SolutionFrontRate"])/7 & /@ rates;

  If[
    Total[Values[rawCredit]] == 0,
    Return[<|"Weights" -> oldWeights, "Rates" -> rates|>]
  ];

  epsilon = 0.01/Length[strategies];
  targetValues = Normalize[Lookup[rawCredit, strategies] + epsilon, Total];
  newValues = (1 - alpha) Lookup[oldWeights, strategies] + alpha targetValues;

  <|
    "Weights" -> AssociationThread[strategies, newValues],
    "Rates" -> rates,
    "RawCredit" -> rawCredit,
    "Alpha" -> alpha,
    "Epsilon" -> epsilon
  |>
]


(* ::Section:: *)
(*Candidate proposal*)


ProposeCandidate[
  parent_Association,
  strategy_String,
  round_Integer,
  trial_Integer,
  config_Association : <||>
] := Block[
  {
    $EdgeSymmetry = Lookup[config, "EdgeSymmetry", "Unordered"],
    $RewriteSemantics = Lookup[config, "RewriteSemantics", "EdgeToken"]
  },
  Module[
  {registryEntry, mutated, proposedRule, details, canonicalRule},

  registryEntry = $MutationStrategyRegistry[strategy];

  mutated = registryEntry["MutationFunction"][parent["Rule"]];
  If[FailureQ[mutated], Return[mutated]];

  (* Operators may return a bare rule or an association carrying provenance
     details (e.g. OrderedEdgePermutation's side/edge/permutation record). *)
  {proposedRule, details} = If[
    AssociationQ[mutated],
    {mutated["Rule"], Lookup[mutated, "Details", <||>]},
    {mutated, <||>}
  ];
  If[FailureQ[proposedRule], Return[proposedRule]];

  canonicalRule = CanonicalRuleForm[proposedRule];
  If[FailureQ[canonicalRule], Return[canonicalRule]];

  <|
    "CandidateID" ->
      CandidateIDFromForms[canonicalRule, parent["InitialState"]],
    "ParentID" -> parent["CandidateID"],
    "Round" -> round,
    "Trial" -> trial,
    "Strategy" -> strategy,
    "Rule" -> canonicalRule,
    "InitialState" -> parent["InitialState"],
    "Provenance" -> <|
      "Strategy" -> strategy,
      "Operators" -> Lookup[registryEntry, "Operators", {}],
      "Parameters" -> Lookup[registryEntry, "DefaultOptions", <||>],
      "ProposedRule" -> proposedRule,
      "Details" -> details
    |>
  |>
  ]
]


(* ::Section:: *)
(*Finalist initial-state diagnostics*)


(* Signature: {count, arity} pairs of the seed state's hyperedges. *)
diagnosticStateSignature[state_?hypergraphStateQ] :=
  Reverse /@ Tally[Length /@ normalizeStateEdges[state]]


randomStateFromSignature[signature_List] := Module[
  {slots, pool},

  slots = Total[Times @@@ signature];
  pool = Range[Max[2, Ceiling[0.7 slots]]];

  Catenate @ Map[
    Function[pair,
      Table[Table[RandomChoice[pool], {pair[[2]]}], {pair[[1]]}]
    ],
    signature
  ]
]


DiagnosticInitialStateEnsemble[seedState_, size_Integer : 5] := Module[
  {signature, raw},

  signature = diagnosticStateSignature[seedState];
  If[signature === {}, Return[{}]];

  raw = Table[
    CanonicalStateForm @ randomStateFromSignature[signature],
    {size}
  ];

  DeleteCases[
    DeleteDuplicates[raw],
    CanonicalStateForm[seedState]
  ]
]


finalistDiagnostics[candidate_Association, ensemble_List, config_Association] := Module[
  {perState, applicable, stateCounts, runtimes, halted},

  perState = Map[
    Function[state,
      Module[{applicableQ, evaluated},
        applicableQ = RuleApplicableQ[candidate["Rule"], state];
        evaluated = If[
          applicableQ,
          EvaluateCandidate[
            <|
              "CandidateID" ->
                CandidateIDFromForms[candidate["Rule"], state],
              "Rule" -> candidate["Rule"],
              "InitialState" -> state
            |>,
            config
          ],
          Missing["NotApplicable"]
        ];
        <|
          "InitialState" -> state,
          "ApplicableQ" -> applicableQ,
          "Status" -> If[MissingQ[evaluated], Missing["NotApplicable"], evaluated["Status"]],
          "MultiwayStateCount" ->
            If[MissingQ[evaluated], Missing["NotApplicable"], Length[evaluated["States"]]],
          "Runtime" ->
            If[MissingQ[evaluated], Missing["NotApplicable"], evaluated["Runtime"]]
        |>
      ]
    ],
    ensemble
  ];

  applicable = Select[perState, TrueQ[#["ApplicableQ"]] &];
  stateCounts = Lookup[applicable, "MultiwayStateCount", {}];
  runtimes = Lookup[applicable, "Runtime", {}];
  halted = Count[applicable, _?(#["Status"] === "Halted" &)];

  <|
    "CandidateID" -> candidate["CandidateID"],
    "InitialStatesTested" -> Length[ensemble],
    "InitiallyApplicableRate" ->
      If[ensemble === {}, Missing["EmptyEnsemble"], N[Length[applicable]/Length[ensemble]]],
    "TerminationRate" ->
      If[applicable === {}, Missing["NoApplicableStates"], N[halted/Length[applicable]]],
    "MedianMultiwayStateCount" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], N @ Median[stateCounts]],
    "MinimumMultiwayStateCount" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], Min[stateCounts]],
    "MaximumMultiwayStateCount" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], Max[stateCounts]],
    "FitnessMean" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], N @ Mean[stateCounts]],
    "FitnessMedian" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], N @ Median[stateCounts]],
    "FitnessVariance" ->
      If[Length[stateCounts] <= 1, Missing["InsufficientData"], N @ Variance[stateCounts]],
    "WorstCaseRuntime" ->
      If[runtimes === {}, Missing["NoApplicableStates"], Max[runtimes]],
    "PerStateResults" -> perState
  |>
]


EvaluateFinalistInitialStates[
  finalists_List,
  baseline_Association,
  config_Association
] := Block[
  {
    $EdgeSymmetry = Lookup[config, "EdgeSymmetry", "Unordered"],
    $RewriteSemantics = Lookup[config, "RewriteSemantics", "EdgeToken"]
  },
  Module[
  {targets, ensemble},

  targets = Switch[
    config["InitialStateDiagnostics"],
    None, Return[Missing["NotRequested"]],
    "Finalists", finalists,
    "SeedAndFinalists", DeleteDuplicatesBy[Prepend[finalists, baseline], #["CandidateID"] &],
    "EveryCandidate", finalists
  ];

  If[targets === {}, Return[<|"Finalists" -> {}, "EnsemblePolicy" -> Missing["NoFinalists"]|>]];

  ensemble = DiagnosticInitialStateEnsemble[baseline["InitialState"]];

  <|
    "EnsemblePolicy" -> <|
      "Generator" -> "RandomHypergraph",
      "Signature" -> diagnosticStateSignature[baseline["InitialState"]],
      "RequestedSize" -> 5
    |>,
    "Ensemble" -> ensemble,
    "Finalists" -> (finalistDiagnostics[#, ensemble, config] & /@ targets)
  |>
  ]
]


(* ::Section:: *)
(*Main orchestration*)


buildConfigurationFromOptions[optionList_List] :=
  ValidateEvolutionConfiguration[Association[optionList]]


StructureAdaptiveEvolution[opts : OptionsPattern[]] := BlockRandom @ Module[
  {
    config, seed, strategies, weights, weightHistory, archive,
    allCandidates, seenIDs, lineageEdges, runLog, baseline,
    searchFront, solutionFront, diagnostics
  },

  config = buildConfigurationFromOptions[
    Table[
      key -> OptionValue[StructureAdaptiveEvolution, {opts}, key],
      {key, Keys @ Association @ Options[StructureAdaptiveEvolution]}
    ]
  ];
  If[FailureQ[config], Return[config]];

  If[IntegerQ[config["RandomSeed"]], SeedRandom[config["RandomSeed"]]];

  ClearEvaluationCache[];

  seed = ResolveAndCanonicalizeSeed[config];
  If[FailureQ[seed], Return[seed]];

  strategies = config["MutationStrategies"];
  weights = EqualStrategyWeights[strategies];
  weightHistory = {weights};

  baseline = EvaluateCandidate[
    <|
      "CandidateID" -> CandidateIDFromForms[seed["Rule"], seed["InitialState"]],
      "ParentID" -> Missing["Seed"],
      "Round" -> 0,
      "Trial" -> 0,
      "Strategy" -> "Seed",
      "Rule" -> seed["Rule"],
      "InitialState" -> seed["InitialState"],
      "Provenance" -> <|
        "Strategy" -> "Seed",
        "SeedID" -> seed["SeedID"],
        "Source" -> seed["Source"]
      |>
    |>,
    config
  ];

  (* Custom metric result types can only be verified against a real
     evaluation context; the baseline is that context. *)
  With[
    {customFailures = Select[
      KeyTake[baseline["Fitness"], Keys[config["CustomFitnessMetrics"]]],
      FailureQ
    ]},
    If[
      customFailures =!= <||>,
      Return @ Failure[
        "InvalidCustomMetricResult",
        <|
          "Message" ->
            "One or more custom fitness metrics failed validation on the baseline evaluation.",
          "Metrics" -> Keys[customFailures],
          "Failures" -> customFailures
        |>
      ]
    ]
  ];

  allCandidates = {baseline};
  seenIDs = <|baseline["CandidateID"] -> True|>;
  archive = {baseline};
  lineageEdges = {};
  runLog = {
    <|
      "Event" -> "RunStart",
      "Timestamp" -> DateString["ISODateTime"],
      "WolframVersion" -> $VersionNumber,
      "HypergraphPacletVersion" ->
        Quiet @ Check[PacletObject["WolframInstitute/Hypergraph"]["Version"], Missing["Unknown"]],
      "RandomSeed" -> config["RandomSeed"],
      "SeedID" -> seed["SeedID"],
      "Backend" -> "CanonicalBFS",
      "StateEquivalence" ->
        "CanonicalHypergraph-" <>
          If[config["EdgeSymmetry"] === "Ordered", "OrderedMultiset", "UnorderedSimple"],
      "RewriteSemantics" -> config["RewriteSemantics"]
    |>
  };

  searchFront = SearchParetoFront[allCandidates, config];
  solutionFront = SolutionParetoFront[allCandidates, config];

  Do[
    Module[
      {
        trials, invalidProposals = 0, duplicateProposals = 0,
        newCandidates = {}, update
      },

      trials = AssociationThread[strategies, 0];

      Do[
        Module[{parent, strategy, proposal},
          parent = RandomChoice[archive];
          strategy = RandomChoice[Values[weights] -> Keys[weights]];
          trials[strategy]++;

          proposal = ProposeCandidate[parent, strategy, round, trial, config];

          Which[
            FailureQ[proposal],
            invalidProposals++,

            KeyExistsQ[seenIDs, proposal["CandidateID"]],
            duplicateProposals++;
            AppendTo[
              lineageEdges,
              <|
                "Parent" -> parent["CandidateID"],
                "Child" -> proposal["CandidateID"],
                "Strategy" -> strategy,
                "Round" -> round,
                "Trial" -> trial,
                "DuplicateQ" -> True
              |>
            ],

            True,
            AssociateTo[seenIDs, proposal["CandidateID"] -> True];
            AppendTo[
              lineageEdges,
              <|
                "Parent" -> parent["CandidateID"],
                "Child" -> proposal["CandidateID"],
                "Strategy" -> strategy,
                "Round" -> round,
                "Trial" -> trial,
                "DuplicateQ" -> False
              |>
            ];
            AppendTo[newCandidates, EvaluateCandidate[proposal, config]]
          ]
        ],
        {trial, config["MutationBudget"]}
      ];

      allCandidates = Join[allCandidates, newCandidates];

      searchFront = SearchParetoFront[allCandidates, config];
      solutionFront = SolutionParetoFront[allCandidates, config];

      update = UpdateStrategyWeights[
        weights,
        trials,
        newCandidates,
        searchFront,
        solutionFront
      ];

      AppendTo[
        runLog,
        <|
          "Event" -> "Round",
          "Round" -> round,
          "Trials" -> trials,
          "InvalidProposals" -> invalidProposals,
          "DuplicateProposals" -> duplicateProposals,
          "NewCandidates" -> Length[newCandidates],
          "SearchFrontSize" -> Length[searchFront],
          "SolutionFrontSize" -> Length[solutionFront],
          "PreviousWeights" -> weights,
          "StrategyRates" -> Lookup[update, "Rates", <||>],
          "UpdatedWeights" -> update["Weights"]
        |>
      ];

      weights = update["Weights"];
      AppendTo[weightHistory, weights];

      (* Parent archive: the search front plus per-objective champions and a
         few random valid candidates, so near-miss lineages stay reachable
         even when the front collapses to one or two candidates (handoff
         9.7). Only Objective-stage champions are used: diagnostic metrics
         like Runtime are wall-clock-dependent and would make parent
         selection nondeterministic under a fixed random seed. *)
      Module[{championIDs, champions, validPool, extras, pool},
        championIDs = DeleteMissing @ Values @ championsOverSpecifications[
          allCandidates, objectiveSpecifications[config], config];
        champions = Select[allCandidates, MemberQ[championIDs, #["CandidateID"]] &];
        validPool = Select[allCandidates, TrueQ[#["ValidQ"]] &];
        extras = RandomSample[validPool, UpTo[3]];
        pool = DeleteDuplicatesBy[
          Join[searchFront, champions, extras],
          #["CandidateID"] &
        ];
        If[pool =!= {}, archive = pool]
      ]
    ],
    {round, config["Rounds"]}
  ];

  diagnostics = EvaluateFinalistInitialStates[
    If[
      config["InitialStateDiagnostics"] === "EveryCandidate",
      allCandidates,
      If[solutionFront =!= {}, solutionFront, searchFront]
    ],
    baseline,
    config
  ];

  <|
    "Configuration" -> config,
    "Seed" -> seed,
    "Baseline" -> baseline,
    "Candidates" -> allCandidates,
    "SearchParetoFront" -> searchFront,
    "SolutionParetoFront" -> solutionFront,
    "MetricChampions" -> MetricChampions[allCandidates, config],
    "CompromiseCandidate" -> Missing["NoMetricPreferencePolicy"],
    "InitialStateDiagnostics" -> diagnostics,
    "StrategyWeightHistory" -> weightHistory,
    "FinalStrategyWeights" -> weights,
    "LineageEdges" -> lineageEdges,
    "RunLog" -> runLog
  |>
]
