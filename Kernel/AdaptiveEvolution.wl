(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Objective normalization*)


resolveObjectiveRange[specification_Association, config_Association] :=
  Lookup[specification, "Range", Lookup[config, "RatioRange", {0., Infinity}]]


rangeDistance[value_?NumericQ, {min_, max_}] :=
  Which[
    min =!= -Infinity && value < min, N[min - value],
    max =!= Infinity && value > max, N[value - max],
    True, 0.
  ]


(* Missing-value policy for objectives (configuration
   "MissingObjectivePolicy"): "Worst" (default) maps a Missing[...] metric
   value to the worst coordinate, Infinity, so the candidate stays
   comparable on its other objectives; "Exclude" leaves the candidate out of
   both fronts. A Missing value never satisfies a constraint. *)
missingObjectiveCoordinate[config_Association] :=
  If[
    Lookup[config, "MissingObjectivePolicy", "Worst"] === "Exclude",
    Missing["NonNumericMetricValue"],
    Infinity
  ]


(* Every objective becomes a minimization coordinate. *)
NormalizedObjectiveValue[value_, specification_Association, config_Association] :=
  Which[
    MatchQ[value, True | False],
    Switch[specification["Direction"],
      "Minimize", Boole[value],
      _, Boole[!value]
    ],

    MissingQ[value],
    missingObjectiveCoordinate[config],

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


objectiveCoordinateQ[value_] := NumericQ[value] || value === Infinity


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

  (* A metric absent from the fitness record means an incomplete
     evaluation: the candidate cannot be placed on a front. A metric that
     reported Missing[...] is handled by the missing-value policy. *)
  vector = KeyValueMap[
    If[
      KeyExistsQ[candidate["Fitness"], #1],
      NormalizedObjectiveValue[candidate["Fitness"][#1], #2, config],
      Missing["NotComputed"]
    ] &,
    specifications
  ];

  If[AllTrue[vector, objectiveCoordinateQ], vector, Missing["IncompleteObjectiveVector"]]
]


(* Hard constraint semantics:
     Boolean value      -- True satisfies a "Maximize" constraint, False a
                           "Minimize" constraint;
     "Range"            -- value inside the range ("Range" key, else
                           RatioRange);
     "Target"           -- Abs[value - Target] <= Tolerance (Tolerance is
                           required by configuration validation);
     "Maximize"/"Minimize" -- value >= Threshold, respectively
                           value <= Threshold;
     Missing or non-numeric values never satisfy a constraint. *)
constraintSatisfiedQ[value_, specification_Association, config_Association] :=
  Which[
    MatchQ[value, True | False],
    If[specification["Direction"] === "Minimize", !TrueQ[value], TrueQ[value]],

    !NumericQ[value],
    False,

    specification["Direction"] === "Range",
    rangeDistance[value, resolveObjectiveRange[specification, config]] == 0,

    specification["Direction"] === "Target",
    KeyExistsQ[specification, "Tolerance"] &&
      TrueQ[Abs[value - specification["Target"]] <= specification["Tolerance"]],

    specification["Direction"] === "Maximize",
    KeyExistsQ[specification, "Threshold"] && TrueQ[value >= specification["Threshold"]],

    specification["Direction"] === "Minimize",
    KeyExistsQ[specification, "Threshold"] && TrueQ[value <= specification["Threshold"]],

    True,
    False
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


(* Compromise among a front: the candidate with the least normalized
   Chebyshev distance to the ideal point of the front's objective vectors
   (each coordinate scaled to [0, 1] between the front's best and worst
   values; Infinity coordinates are excluded). *)
idealPointCompromise[candidates_List, config_Association] := Module[
  {pool, vectors, ideal, nadir, scores},

  pool = Select[
    {#, CandidateObjectiveVector[#, config]} & /@ candidates,
    ListQ[Last[#]] && AllTrue[Last[#], NumericQ] &
  ];
  If[pool === {}, Return[Missing["NoCandidate"]]];

  vectors = Last /@ pool;
  ideal = Min /@ Transpose[vectors];
  nadir = Max /@ Transpose[vectors];
  scores = Function[vector,
    Max[0, MapThread[If[#3 == #2, 0, (#1 - #2)/(#3 - #2)] &, {vector, ideal, nadir}]]
  ] /@ vectors;

  pool[[First @ Ordering[scores, 1], 1]]["CandidateID"]
]


compromiseCandidate[searchFront_List, solutionFront_List, config_Association] :=
  Switch[
    Lookup[config, "CompromisePolicy", None],
    "IdealPointDistance",
      idealPointCompromise[If[solutionFront =!= {}, solutionFront, searchFront], config],
    _,
      Missing["NoMetricPreferencePolicy"]
  ]


frontMembership[candidates_List, searchFront_List, solutionFront_List] :=
  With[
    {
      search = Lookup[searchFront, "CandidateID", {}],
      solution = Lookup[solutionFront, "CandidateID", {}]
    },
    AssociationMap[
      Which[MemberQ[solution, #], "Solution", MemberQ[search, #], "Search", True, "None"] &,
      Lookup[candidates, "CandidateID", {}]
    ]
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


multisetComplement[a_List, b_List] := Module[{counts = Counts[b]},
  Select[
    a,
    Function[element,
      If[
        Lookup[counts, Key[element], 0] > 0,
        counts[element] = counts[element] - 1; False,
        True
      ]
    ]
  ]
]


ruleVariables[lhs_ -> rhs_] := DeleteDuplicates @ Flatten[{lhs, rhs}]


(* Exact mutation diff in the parent's labels (the parent rule is canonical;
   the proposal is the operator's raw output before canonicalization). *)
ruleDiff[old_Rule, new_Rule] := <|
  "LHSAdded" -> multisetComplement[new[[1]], old[[1]]],
  "LHSRemoved" -> multisetComplement[old[[1]], new[[1]]],
  "RHSAdded" -> multisetComplement[new[[2]], old[[2]]],
  "RHSRemoved" -> multisetComplement[old[[2]], new[[2]]],
  "VariablesAdded" -> Complement[ruleVariables[new], ruleVariables[old]],
  "VariablesRemoved" -> Complement[ruleVariables[old], ruleVariables[new]]
|>

ruleDiff[old_, new_] := <|
  "RulesAdded" -> multisetComplement[ruleList[new], ruleList[old]],
  "RulesRemoved" -> multisetComplement[ruleList[old], ruleList[new]]
|>


ProposeCandidate[
  parent_Association,
  strategy_String,
  round_Integer,
  trial_Integer,
  config_Association : <||>
] := withConfigUniverse[
  config,
  Block[{$operatorTrace = {}}, Module[
  {
    registryEntry, options, parentRule, memberIndex, target, mutated,
    proposedPart, details, proposedRule, canonicalRule
  },

  registryEntry = $MutationStrategyRegistry[strategy];
  options = Join[
    Lookup[registryEntry, "DefaultOptions", <||>],
    Lookup[Lookup[config, "StrategyOptions", <||>], strategy, <||>]
  ];

  parentRule = parent["Rule"];

  (* A strategy that is not rule-set aware mutates one member rule of a rule
     set; single-rule parents are mutated whole. *)
  {memberIndex, target} =
    If[
      ruleSetQ[parentRule] && !TrueQ[Lookup[registryEntry, "RuleSetAware", False]],
      With[{index = RandomInteger[{1, Length[parentRule]}]}, {index, parentRule[[index]]}],
      {None, parentRule}
    ];

  mutated =
    If[
      KeyExistsQ[registryEntry, "ContextMutationFunction"],
      registryEntry["ContextMutationFunction"][
        target,
        <|"Parent" -> parent, "Options" -> options, "Configuration" -> config|>
      ],
      registryEntry["MutationFunction"][target]
    ];
  If[FailureQ[mutated], Return[mutated]];

  (* Operators may return a bare rule or an association carrying provenance
     details (e.g. OrderedEdgePermutation's side/edge/permutation record). *)
  {proposedPart, details} = If[
    AssociationQ[mutated],
    {mutated["Rule"], Lookup[mutated, "Details", <||>]},
    {mutated, <||>}
  ];
  If[FailureQ[proposedPart], Return[proposedPart]];

  proposedRule =
    If[memberIndex === None, proposedPart, ReplacePart[parentRule, memberIndex -> proposedPart]];

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
      "AppliedOperators" -> $operatorTrace,
      "Parameters" -> options,
      "ProposedRule" -> proposedRule,
      "RuleSetMember" -> memberIndex,
      "Diff" -> ruleDiff[parentRule, proposedRule],
      "Details" -> details
    |>
  |>
  ]]
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


(* Mean/median/minimum/maximum of every numeric metric over the applicable
   ensemble states. *)
fitnessSummary[fitnessList_List] := Module[{metrics},
  metrics = DeleteDuplicates @ Catenate[Keys /@ fitnessList];
  AssociationMap[
    Function[metric,
      With[
        {
          values = Select[
            Lookup[fitnessList, metric, Missing[]] /. {True -> 1, False -> 0},
            NumericQ
          ]
        },
        If[
          values === {},
          Missing["NoNumericValues"],
          <|
            "Count" -> Length[values],
            "Mean" -> N @ Mean[values],
            "Median" -> N @ Median[values],
            "Minimum" -> Min[values],
            "Maximum" -> Max[values]
          |>
        ]
      ]
    ],
    metrics
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
            If[MissingQ[evaluated], Missing["NotApplicable"], evaluated["Runtime"]],
          "Fitness" ->
            If[MissingQ[evaluated], Missing["NotApplicable"], evaluated["Fitness"]]
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
    (* "FitnessMean", "FitnessMedian" and "FitnessVariance" are kept for
       schema compatibility: they summarize the multiway state count only.
       "FitnessSummary" summarizes every metric of the fitness vector. *)
    "FitnessMean" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], N @ Mean[stateCounts]],
    "FitnessMedian" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], N @ Median[stateCounts]],
    "FitnessVariance" ->
      If[Length[stateCounts] <= 1, Missing["InsufficientData"], N @ Variance[stateCounts]],
    "MultiwayStateCountMean" ->
      If[stateCounts === {}, Missing["NoApplicableStates"], N @ Mean[stateCounts]],
    "FitnessSummary" ->
      If[applicable === {}, Missing["NoApplicableStates"], fitnessSummary[Lookup[applicable, "Fitness"]]],
    "WorstCaseRuntime" ->
      If[runtimes === {}, Missing["NoApplicableStates"], Max[runtimes]],
    "PerStateResults" -> perState
  |>
]


EvaluateFinalistInitialStates[
  finalists_List,
  baseline_Association,
  config_Association
] := withConfigUniverse[
  config,
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
(*Candidate evaluation (sequential or parallel)*)


$parallelKernelsLoaded = {};

parallelKernelCount[setting_] :=
  Replace[setting, {True :> $ProcessorCount, n_Integer :> n, _ -> 0}]


(* Launch subkernels as needed and load this paclet on each kernel once. *)
ensureParallelKernels[count_Integer] := Module[{kernels, fresh},
  If[Length[Kernels[]] < count, Quiet @ LaunchKernels[count - Length[Kernels[]]]];
  kernels = Kernels[];
  fresh = Select[kernels, !MemberQ[$parallelKernelsLoaded, #["ID"]] &];
  If[
    fresh =!= {},
    With[{root = $pacletRoot},
      ParallelEvaluate[
        PacletDirectoryLoad[root];
        Needs["SamuelFrerichs`StructureAdaptiveEvolution`"],
        fresh
      ]
    ];
    $parallelKernelsLoaded = Join[$parallelKernelsLoaded, #["ID"] & /@ fresh]
  ];
  Length[kernels]
]


(* Proposals are generated sequentially (the random stream is identical to a
   sequential run) and evaluated afterwards, sequentially or in parallel;
   results keep proposal order, so a parallel run selects exactly like a
   sequential one except for wall-clock statuses. *)
evaluateProposals[proposals_List, config_Association] :=
  Which[
    proposals === {},
    {},

    parallelKernelCount[config["Parallelization"]] > 1 && Length[proposals] > 1,
    Module[{available, results},
      available = ensureParallelKernels @ Min[
        parallelKernelCount[config["Parallelization"]],
        Length[proposals]
      ];
      If[
        available < 2,
        EvaluateCandidate[#, config] & /@ proposals,
        results = ParallelMap[
          SamuelFrerichs`StructureAdaptiveEvolution`EvaluateCandidate[#, config] &,
          proposals,
          Method -> "FinestGrained"
        ];
        countStatistic["ParallelEvaluations", Length[results]];
        countStatistic["EvolutionTime", Total[Select[Lookup[results, "Runtime", 0], NumericQ]]];
        results
      ]
    ],

    True,
    EvaluateCandidate[#, config] & /@ proposals
  ]


(* ::Section:: *)
(*Main orchestration*)


buildConfigurationFromOptions[optionList_List] :=
  ValidateEvolutionConfiguration[Association[optionList]]


(* Fields that may differ between a run and its resumption. *)
$ResumeExemptFields = {
  "Rounds", "ResumeFrom", "Parallelization", "InitialStateDiagnostics", "ReuseEvaluations"
};

resumeIncompatibilities[previous_Association, config_Association] :=
  Select[
    Complement[Union[Keys[previous], Keys[config]], $ResumeExemptFields],
    Lookup[previous, #, Missing["Absent"]] =!= Lookup[config, #, Missing["Absent"]] &
  ]


stateEquivalenceTag[config_Association] :=
  Switch[
    {config["EdgeSymmetry"], Lookup[config, "CanonicalForm", "Exact"]},
    {"Ordered", "Native"}, "CanonicalHypergraph-OrderedMultiset",
    {"Ordered", "Exact"}, "ExactCanonical-OrderedMultiset",
    {"Declared", _}, "ExactCanonical-DeclaredMultiset",
    {_, "Exact"}, "ExactCanonical-UnorderedSimple",
    _, "CanonicalHypergraph-UnorderedSimple"
  ]


StructureAdaptiveEvolution[opts : OptionsPattern[]] := BlockRandom @ Module[
  {
    config, runID, startTime, startDate, previous, resumedQ, roundOffset,
    seed, strategies, weights, weightHistory, archive, allCandidates, seenIDs,
    lineageEdges, runLog, baseline, searchFront, solutionFront, diagnostics,
    proposalFailures = {}, frontHistory = {}, timings = <||>, roundTimings = {},
    randomStateAfterRounds, storedConfig, gitInformation
  },

  config = buildConfigurationFromOptions[
    Table[
      key -> OptionValue[StructureAdaptiveEvolution, {opts}, key],
      {key, Keys @ Association @ Options[StructureAdaptiveEvolution]}
    ]
  ];
  If[FailureQ[config], Return[config]];

  runID = CreateUUID[];
  startTime = AbsoluteTime[];
  startDate = DateString["ISODateTime"];

  previous = config["ResumeFrom"];
  resumedQ = AssociationQ[previous];

  (* An Automatic seed is drawn once and recorded, so every run can be
     replicated; a resumed run keeps the seed it was started with. *)
  If[
    config["RandomSeed"] === Automatic,
    config["RandomSeed"] = If[
      resumedQ,
      Lookup[Lookup[previous, "Configuration", <||>], "RandomSeed", Automatic],
      RandomInteger[{1, 2^31 - 1}]
    ]
  ];
  gitInformation = pacletGitInformation[];
  storedConfig = Append[
    config,
    "ResumeFrom" -> If[resumedQ, <|"RunID" -> Lookup[previous, "RunID", Missing["Unknown"]]|>, None]
  ];

  If[
    resumedQ,
    With[{bad = resumeIncompatibilities[Lookup[previous, "Configuration", <||>], storedConfig]},
      If[
        bad =!= {},
        Return @ Failure[
          "ResumeIncompatible",
          <|
            "Message" ->
              "A run can only be resumed with the configuration it was started with (Rounds, Parallelization, InitialStateDiagnostics and ReuseEvaluations may differ).",
            "Fields" -> bad
          |>
        ]
      ]
    ]
  ];

  If[IntegerQ[config["RandomSeed"]] && !resumedQ, SeedRandom[config["RandomSeed"]]];

  If[!TrueQ[config["ReuseEvaluations"]], ClearEvaluationCache[]];

  Block[
    {
      $evaluationStatistics = <|
        "FreshEvolutions" -> 0, "CacheHits" -> 0, "ParallelEvaluations" -> 0,
        "PreloadedHits" -> 0, "EvolutionTime" -> 0.
      |>,
      $PreloadedEvaluations = If[TrueQ[config["ReuseEvaluations"]], $PreloadedEvaluations, <||>]
    },

    strategies = config["MutationStrategies"];

    If[
      resumedQ,

      (* ---------------------------------------------------------- *)
      (* Resume: restore search state and the random stream         *)
      (* ---------------------------------------------------------- *)
      Module[{resumeState = previous["ResumeState"], byID},
        seed = previous["Seed"];
        baseline = previous["Baseline"];
        allCandidates = previous["Candidates"];
        byID = Association[#["CandidateID"] -> # & /@ allCandidates];
        seenIDs = AssociationThread[Keys[byID], True];
        archive = Lookup[byID, resumeState["ArchiveIDs"]];
        weights = previous["FinalStrategyWeights"];
        weightHistory = previous["StrategyWeightHistory"];
        lineageEdges = previous["LineageEdges"];
        proposalFailures = Lookup[previous, "ProposalFailures", {}];
        frontHistory = Lookup[previous, "FrontHistory", {}];
        runLog = Append[
          previous["RunLog"],
          <|
            "Event" -> "Resume",
            "Timestamp" -> startDate,
            "RunID" -> runID,
            "ResumedRunID" -> Lookup[previous, "RunID", Missing["Unknown"]],
            "RoundsCompleted" -> resumeState["RoundsCompleted"]
          |>
        ];
        roundOffset = resumeState["RoundsCompleted"];
        $RandomGeneratorState = resumeState["RandomGeneratorState"]
      ],

      (* ---------------------------------------------------------- *)
      (* Fresh run: seed, baseline, custom-metric checks            *)
      (* ---------------------------------------------------------- *)
      timings["SeedResolution"] = First @ AbsoluteTiming[
        seed = ResolveAndCanonicalizeSeed[config]
      ];
      If[FailureQ[seed], Return[seed]];

      weights = EqualStrategyWeights[strategies];
      weightHistory = {weights};

      timings["Baseline"] = First @ AbsoluteTiming[
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
              "Source" -> seed["Source"],
              "RegistryCode" -> seed["RegistryCode"]
            |>
          |>,
          config
        ]
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

      (* A numeric Maximize/Minimize constraint needs a Threshold; only a
         real value reveals whether a custom constraint is numeric. *)
      With[
        {
          missingThresholds = Select[
            Keys[config["CustomFitnessMetrics"]],
            With[{specification = config["CustomFitnessMetrics"][#]},
              specification["Stage"] === "Constraint" &&
                MatchQ[specification["Direction"], "Maximize" | "Minimize"] &&
                !KeyExistsQ[specification, "Threshold"] &&
                NumericQ[baseline["Fitness"][#]]
            ] &
          ]
        },
        If[
          missingThresholds =!= {},
          Return @ Failure[
            "ConstraintThresholdRequired",
            <|
              "Message" ->
                "A numeric \"Maximize\"/\"Minimize\" constraint needs a \"Threshold\" (value >= Threshold, respectively value <= Threshold).",
              "Metrics" -> missingThresholds
            |>
          ]
        ]
      ];

      allCandidates = {baseline};
      seenIDs = <|baseline["CandidateID"] -> True|>;
      archive = {baseline};
      lineageEdges = {};
      roundOffset = 0;
      runLog = {
        <|
          "Event" -> "RunStart",
          "Timestamp" -> startDate,
          "RunID" -> runID,
          "WolframVersion" -> $VersionNumber,
          "HypergraphPacletVersion" -> hypergraphVersionString[],
          "PacletVersion" -> pacletVersionString[],
          "EvaluatorVersion" -> $EvaluatorVersion,
          "RandomSeed" -> config["RandomSeed"],
          "SeedID" -> seed["SeedID"],
          "Backend" -> "CanonicalBFS",
          "StateEquivalence" -> stateEquivalenceTag[config],
          "RewriteSemantics" -> config["RewriteSemantics"]
        |>
      }
    ];

    searchFront = SearchParetoFront[allCandidates, config];
    solutionFront = SolutionParetoFront[allCandidates, config];

    Do[
      Module[
        {
          trials, invalidProposals = 0, duplicateProposals = 0, pending = {},
          newCandidates = {}, update, proposalTime, evaluationTime
        },

        trials = AssociationThread[strategies, 0];

        (* Proposal phase: every random draw of the round happens here. *)
        proposalTime = First @ AbsoluteTiming[
          Do[
            Module[{parent, strategy, proposal},
              parent = RandomChoice[archive];
              strategy = RandomChoice[Values[weights] -> Keys[weights]];
              trials[strategy]++;

              proposal = ProposeCandidate[parent, strategy, round, trial, config];

              Which[
                FailureQ[proposal],
                invalidProposals++;
                AppendTo[
                  proposalFailures,
                  <|
                    "Round" -> round,
                    "Trial" -> trial,
                    "Strategy" -> strategy,
                    "ParentID" -> parent["CandidateID"],
                    "Failure" -> proposal
                  |>
                ],

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
                AppendTo[pending, proposal]
              ]
            ],
            {trial, config["MutationBudget"]}
          ]
        ];

        (* Evaluation phase: each unique proposal is evolved once. *)
        evaluationTime = First @ AbsoluteTiming[
          newCandidates = evaluateProposals[pending, config]
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
        (* Fixed uniform weights (random-mutation baseline): the rates are
           still logged, the weights stay put. *)
        If[!TrueQ[config["AdaptiveWeights"]], update = Append[update, "Weights" -> weights]];

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
            "UpdatedWeights" -> update["Weights"],
            "AdaptiveWeights" -> config["AdaptiveWeights"]
          |>
        ];

        AppendTo[
          frontHistory,
          <|
            "Round" -> round,
            "SearchFrontIDs" -> Lookup[searchFront, "CandidateID", {}],
            "SolutionFrontIDs" -> Lookup[solutionFront, "CandidateID", {}]
          |>
        ];

        AppendTo[
          roundTimings,
          <|"Round" -> round, "Proposal" -> proposalTime, "Evaluation" -> evaluationTime|>
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
      {round, roundOffset + 1, roundOffset + config["Rounds"]}
    ];

    (* Saved before the diagnostics draw from the stream, so a resumed run
       continues exactly where these rounds stopped. *)
    randomStateAfterRounds = $RandomGeneratorState;

    timings["Diagnostics"] = First @ AbsoluteTiming[
      diagnostics = EvaluateFinalistInitialStates[
        If[
          config["InitialStateDiagnostics"] === "EveryCandidate",
          allCandidates,
          If[solutionFront =!= {}, solutionFront, searchFront]
        ],
        baseline,
        config
      ]
    ];

    <|
      "RunID" -> runID,
      "Configuration" -> storedConfig,
      "Seed" -> seed,
      "Baseline" -> baseline,
      "Candidates" -> allCandidates,
      "SearchParetoFront" -> searchFront,
      "SolutionParetoFront" -> solutionFront,
      "FrontMembership" -> frontMembership[allCandidates, searchFront, solutionFront],
      "FrontHistory" -> frontHistory,
      "MetricChampions" -> MetricChampions[allCandidates, config],
      "SolutionChampions" ->
        MetricChampions[Select[allCandidates, solutionEligibleQ[#, config] &], config],
      "CompromiseCandidate" -> compromiseCandidate[searchFront, solutionFront, config],
      "InitialStateDiagnostics" -> diagnostics,
      "StrategyWeightHistory" -> weightHistory,
      "FinalStrategyWeights" -> weights,
      "LineageEdges" -> lineageEdges,
      "ProposalFailures" -> proposalFailures,
      "RunLog" -> runLog,
      "Performance" -> With[
        {
          statistics = $evaluationStatistics,
          rounds = Select[runLog, #["Event"] === "Round" &]
        },
        <|
          "FreshEvaluations" ->
            statistics["FreshEvolutions"] + statistics["ParallelEvaluations"],
          "CacheHits" -> statistics["CacheHits"],
          "PreloadedHits" -> statistics["PreloadedHits"],
          "DuplicateProposals" -> Total[Lookup[rounds, "DuplicateProposals", {}]],
          "InvalidProposals" -> Total[Lookup[rounds, "InvalidProposals", {}]],
          "EvolutionTime" -> statistics["EvolutionTime"],
          "EvaluationsPerSecond" ->
            With[
              {
                n = statistics["FreshEvolutions"] + statistics["ParallelEvaluations"],
                t = statistics["EvolutionTime"]
              },
              If[TrueQ[t > 0], N[n/t], Missing["NoTiming"]]
            ],
          "PeakStateCount" -> Max[0, Length[Lookup[#, "States", {}]] & /@ allCandidates],
          "PeakFrontierSize" ->
            Max[0, Max[0, Length /@ Lookup[#, "Generations", {}]] & /@ allCandidates],
          "MaxMemoryUsed" -> MaxMemoryUsed[],
          "PhaseTimings" -> Join[
            timings,
            <|"Rounds" -> roundTimings, "Total" -> AbsoluteTime[] - startTime|>
          ],
          "Parallelization" -> config["Parallelization"]
        |>
      ],
      "Provenance" -> <|
        "RunID" -> runID,
        "ResumedFrom" -> If[resumedQ, Lookup[previous, "RunID", Missing["Unknown"]], None],
        "StartTime" -> startDate,
        "EndTime" -> DateString["ISODateTime"],
        "WolframVersion" -> $Version,
        "WolframVersionNumber" -> $VersionNumber,
        "SystemID" -> $SystemID,
        "ProcessorCount" -> $ProcessorCount,
        "PacletVersion" -> pacletVersionString[],
        "PacletGitCommit" -> Replace[gitInformation["Commit"], Null -> Missing["NotAvailable"]],
        "PacletGitDirty" -> Replace[gitInformation["Dirty"], Null -> Missing["NotAvailable"]],
        "HypergraphPacletVersion" -> hypergraphVersionString[],
        "EvaluatorVersion" -> $EvaluatorVersion,
        "RandomSeed" -> config["RandomSeed"],
        "StateEquivalence" -> stateEquivalenceTag[config],
        "RewriteSemantics" -> config["RewriteSemantics"],
        "RegistryCode" -> Lookup[seed, "RegistryCode", Missing["NotApplicable"]],
        "RegistryVersion" -> Lookup[seed, "RegistryVersion", Missing["NotApplicable"]]
      |>,
      "ResumeState" -> <|
        "RoundsCompleted" -> roundOffset + config["Rounds"],
        "ArchiveIDs" -> Lookup[archive, "CandidateID", {}],
        "RandomGeneratorState" -> randomStateAfterRounds
      |>
    |>
  ]
]
