(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ================================================================ *)
(* Default goal presets                                             *)
(* ================================================================ *)

$GoalPresets = <|

  "LargeFiniteTerminating" -> <|

    "MutationStrategies" -> {
      "GrowthBudget",
      "OverlappingMatch",
      "GrowThenConstrain",
      "DelayedTermination",
      "RuntimeThrottling",
      "VariableRewiring",
      "OrderedEdgePermutation"
    },

    "FitnessMetrics" -> {
      "HaltedWithinCapQ",
      "MultiwayStateCount",
      "MultiwayLifetime",
      "HGMaxVerticesCount",
      "HGMaxEdgesCount",
      "HGMaxEdgeToVertexRatio",
      "Runtime"
    }

  |>

|>;


(* ================================================================ *)
(* Defaults                                                         *)
(* ================================================================ *)

$DefaultEvolutionLimits = <|
  "MaxGenerations" -> 10,
  "MaxEvents" -> 1000,
  "TimeConstraint" -> 30.
|>;


Options[StructureAdaptiveEvolution] = {

  "Goal" -> "LargeFiniteTerminating",

  "EdgeSymmetry" -> "Unordered",
  "RewriteSemantics" -> "EdgeToken",

  "Rule" -> Automatic,
  "InitialState" -> Automatic,

  "MutationStrategies" -> Automatic,
  "FitnessMetrics" -> Automatic,
  "CustomFitnessMetrics" -> <||>,

  "Rounds" -> 1,
  "MutationBudget" -> 20,

  "EvolutionLimits" -> <||>,
  "RatioRange" -> {0., Infinity},

  "InitialStateDiagnostics" -> "Finalists",

  "RandomSeed" -> Automatic
};


(* ================================================================ *)
(* Small validation helpers                                         *)
(* ================================================================ *)

configurationFailure[field_, value_, message_] :=
  Failure[
    "InvalidConfiguration",
    <|
      "Message" -> message,
      "Field" -> field,
      "Value" -> value
    |>
  ];


validRuleQ[rule_] :=
  rule === Automatic || MatchQ[rule, _Rule];


validInitialStateQ[state_] :=
  state === Automatic || TrueQ[hypergraphStateQ[state]];


positiveIntegerOrInfinityQ[value_] :=
  value === Infinity ||
    (IntegerQ[value] && Positive[value]);


positiveNumberOrInfinityQ[value_] :=
  value === Infinity ||
    (NumericQ[value] && TrueQ[value > 0]);


validRatioRangeQ[{minimum_, maximum_}] :=
  NumericQ[minimum] &&
  TrueQ[minimum >= 0] &&
  (
    maximum === Infinity ||
    (
      NumericQ[maximum] &&
      TrueQ[maximum >= minimum]
    )
  );


validRatioRangeQ[_] := False;


validCallableQ[value_] :=
  MatchQ[value, _Function | _Symbol];


validCustomMetricSpecificationQ[
  specification_Association
] := Module[
  {
    function,
    direction,
    input,
    stage,
    validator,
    target
  },

  function =
    Lookup[
      specification,
      "Function",
      Missing["KeyAbsent", "Function"]
    ];

  direction =
    Lookup[
      specification,
      "Direction",
      Missing["KeyAbsent", "Direction"]
    ];

  input =
    Lookup[
      specification,
      "Input",
      "EvaluationContext"
    ];

  stage =
    Lookup[
      specification,
      "Stage",
      "Objective"
    ];

  validator =
    Lookup[
      specification,
      "Validator",
      NumericQ
    ];

  target =
    Lookup[
      specification,
      "Target",
      Missing["NotApplicable"]
    ];

  validCallableQ[function] &&

  MemberQ[
    {"Maximize", "Minimize", "Target"},
    direction
  ] &&

  MemberQ[
    $AllowedMetricInputs,
    input
  ] &&

  MemberQ[
    {"Objective", "Constraint", "Diagnostic"},
    stage
  ] &&

  validCallableQ[validator] &&

  (
    direction =!= "Target" ||
    NumericQ[target]
  )
];


validCustomMetricSpecificationQ[_] := False;


normalizeCustomMetricSpecification[
  specification_Association
] :=
  Join[
    <|
      "Input" -> "EvaluationContext",
      "Stage" -> "Objective",
      "Validator" -> NumericQ
    |>,
    specification
  ];


implementedStrategyQ[name_String] :=
  TrueQ[
    Lookup[
      Lookup[
        $MutationStrategyRegistry,
        name,
        <||>
      ],
      "ImplementedQ",
      False
    ]
  ];


(* A strategy without a RequiredEdgeSymmetry key works in every universe. *)
strategyEdgeSymmetryCompatibleQ[name_String, symmetry_String] :=
  With[
    {
      required = Lookup[
        Lookup[$MutationStrategyRegistry, name, <||>],
        "RequiredEdgeSymmetry",
        None
      ]
    },
    required === None || required === symmetry
  ];


(* ================================================================ *)
(* Main configuration validator                                     *)
(* ================================================================ *)

ValidateEvolutionConfiguration[
  suppliedConfiguration_Association
] := Module[
  {
    goal,
    preset,
    edgeSymmetry,
    rewriteSemantics,

    rule,
    initialState,

    requestedStrategies,
    recommendedStrategies,
    strategies,
    unavailableRecommendedStrategies,
    unknownStrategies,
    unimplementedStrategies,

    requestedMetrics,
    customMetrics,
    invalidCustomMetrics,
    normalizedCustomMetrics,
    conflictingMetricNames,
    requiredMetrics,
    metrics,
    unknownMetrics,

    rounds,
    mutationBudget,

    suppliedLimits,
    limits,
    unknownLimits,

    ratioRange,
    diagnostics,
    randomSeed
  },

  (* -------------------------------------------------------------- *)
  (* Goal                                                           *)
  (* -------------------------------------------------------------- *)

  goal =
    Lookup[
      suppliedConfiguration,
      "Goal",
      "LargeFiniteTerminating"
    ];

  preset =
    Lookup[
      $GoalPresets,
      goal,
      Missing["UnknownGoal"]
    ];

  If[
    MissingQ[preset],
    Return @ configurationFailure[
      "Goal",
      goal,
      "The requested goal preset is not defined."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Edge symmetry (universe)                                       *)
  (* -------------------------------------------------------------- *)

  edgeSymmetry =
    Lookup[
      suppliedConfiguration,
      "EdgeSymmetry",
      "Unordered"
    ];

  If[
    !MatchQ[edgeSymmetry, "Unordered" | "Ordered"],
    Return @ configurationFailure[
      "EdgeSymmetry",
      edgeSymmetry,
      "EdgeSymmetry must be \"Unordered\" or \"Ordered\"."
    ]
  ];

  rewriteSemantics =
    Lookup[
      suppliedConfiguration,
      "RewriteSemantics",
      "EdgeToken"
    ];

  If[
    !MatchQ[rewriteSemantics, "VertexDeletion" | "EdgeToken"],
    Return @ configurationFailure[
      "RewriteSemantics",
      rewriteSemantics,
      "RewriteSemantics must be \"VertexDeletion\" or \"EdgeToken\"."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Rule and initial state                                         *)
  (* -------------------------------------------------------------- *)

  rule =
    Lookup[
      suppliedConfiguration,
      "Rule",
      Automatic
    ];

  If[
    !validRuleQ[rule],
    Return @ configurationFailure[
      "Rule",
      rule,
      "Rule must be a single Rule expression or Automatic."
    ]
  ];

  initialState =
    Lookup[
      suppliedConfiguration,
      "InitialState",
      Automatic
    ];

  If[
    !validInitialStateQ[initialState],
    Return @ configurationFailure[
      "InitialState",
      initialState,
      "InitialState must be a valid hypergraph state or Automatic."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Mutation strategies                                            *)
  (* -------------------------------------------------------------- *)

  requestedStrategies =
    Lookup[
      suppliedConfiguration,
      "MutationStrategies",
      Automatic
    ];

  recommendedStrategies =
    preset["MutationStrategies"];

  strategies =
    If[
      requestedStrategies === Automatic,

      Select[
        recommendedStrategies,
        implementedStrategyQ[#] &&
          strategyEdgeSymmetryCompatibleQ[#, edgeSymmetry] &
      ],

      requestedStrategies
    ];

  If[
    !MatchQ[strategies, {__String}],
    Return @ configurationFailure[
      "MutationStrategies",
      strategies,
      "MutationStrategies must be Automatic or a nonempty list of names."
    ]
  ];

  strategies = DeleteDuplicates[strategies];

  unknownStrategies =
    Complement[
      strategies,
      Keys[$MutationStrategyRegistry]
    ];

  If[
    unknownStrategies =!= {},
    Return @ configurationFailure[
      "MutationStrategies",
      unknownStrategies,
      "One or more mutation strategies are unknown."
    ]
  ];

  unimplementedStrategies =
    Select[
      strategies,
      !implementedStrategyQ[#] &
    ];

  If[
    unimplementedStrategies =!= {},
    Return @ configurationFailure[
      "MutationStrategies",
      unimplementedStrategies,
      "One or more requested mutation strategies are not implemented."
    ]
  ];

  With[
    {
      incompatibleStrategies = Select[
        strategies,
        !strategyEdgeSymmetryCompatibleQ[#, edgeSymmetry] &
      ]
    },
    If[
      incompatibleStrategies =!= {},
      Return @ configurationFailure[
        "MutationStrategies",
        incompatibleStrategies,
        "One or more requested mutation strategies require a different \"EdgeSymmetry\" setting."
      ]
    ]
  ];

  unavailableRecommendedStrategies =
    Complement[
      recommendedStrategies,
      Select[
        recommendedStrategies,
        implementedStrategyQ[#] &&
          strategyEdgeSymmetryCompatibleQ[#, edgeSymmetry] &
      ]
    ];


  (* -------------------------------------------------------------- *)
  (* Custom fitness metrics                                         *)
  (* -------------------------------------------------------------- *)

  customMetrics =
    Lookup[
      suppliedConfiguration,
      "CustomFitnessMetrics",
      <||>
    ];

  If[
    !AssociationQ[customMetrics],
    Return @ configurationFailure[
      "CustomFitnessMetrics",
      customMetrics,
      "CustomFitnessMetrics must be an Association."
    ]
  ];

  conflictingMetricNames =
    Intersection[
      Keys[customMetrics],
      Keys[$FitnessMetricRegistry]
    ];

  If[
    conflictingMetricNames =!= {},
    Return @ configurationFailure[
      "CustomFitnessMetrics",
      conflictingMetricNames,
      "A custom fitness metric cannot replace an existing metric."
    ]
  ];

  invalidCustomMetrics =
    Select[
      Keys[customMetrics],
      !validCustomMetricSpecificationQ[
        customMetrics[#]
      ] &
    ];

  If[
    invalidCustomMetrics =!= {},
    Return @ configurationFailure[
      "CustomFitnessMetrics",
      invalidCustomMetrics,
      "One or more custom fitness metric specifications are invalid."
    ]
  ];

  normalizedCustomMetrics =
    Map[
      normalizeCustomMetricSpecification,
      customMetrics
    ];


  (* -------------------------------------------------------------- *)
  (* Selected and required metrics                                  *)
  (* -------------------------------------------------------------- *)

  requestedMetrics =
    Lookup[
      suppliedConfiguration,
      "FitnessMetrics",
      Automatic
    ];

  metrics =
    If[
      requestedMetrics === Automatic,
      preset["FitnessMetrics"],
      requestedMetrics
    ];

  If[
    !MatchQ[metrics, {__String}],
    Return @ configurationFailure[
      "FitnessMetrics",
      metrics,
      "FitnessMetrics must be Automatic or a nonempty list of names."
    ]
  ];

  requiredMetrics =
    DeleteDuplicates @ Flatten[
      Lookup[
        $MutationStrategyRegistry[#],
        "RequiredMetrics",
        {}
      ] & /@ strategies
    ];

  metrics =
    DeleteDuplicates @ Join[
      metrics,
      requiredMetrics,
      Keys[normalizedCustomMetrics]
    ];

  unknownMetrics =
    Complement[
      metrics,
      Join[
        Keys[$FitnessMetricRegistry],
        Keys[normalizedCustomMetrics]
      ]
    ];

  If[
    unknownMetrics =!= {},
    Return @ configurationFailure[
      "FitnessMetrics",
      unknownMetrics,
      "One or more requested fitness metrics are unknown."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Search parameters                                              *)
  (* -------------------------------------------------------------- *)

  rounds =
    Lookup[
      suppliedConfiguration,
      "Rounds",
      1
    ];

  If[
    !(IntegerQ[rounds] && Positive[rounds]),
    Return @ configurationFailure[
      "Rounds",
      rounds,
      "Rounds must be a positive integer."
    ]
  ];

  mutationBudget =
    Lookup[
      suppliedConfiguration,
      "MutationBudget",
      20
    ];

  If[
    !(IntegerQ[mutationBudget] && Positive[mutationBudget]),
    Return @ configurationFailure[
      "MutationBudget",
      mutationBudget,
      "MutationBudget must be a positive integer."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Evolution limits                                               *)
  (* -------------------------------------------------------------- *)

  suppliedLimits =
    Lookup[
      suppliedConfiguration,
      "EvolutionLimits",
      <||>
    ];

  If[
    !AssociationQ[suppliedLimits],
    Return @ configurationFailure[
      "EvolutionLimits",
      suppliedLimits,
      "EvolutionLimits must be an Association."
    ]
  ];

  unknownLimits =
    Complement[
      Keys[suppliedLimits],
      Keys[$DefaultEvolutionLimits]
    ];

  If[
    unknownLimits =!= {},
    Return @ configurationFailure[
      "EvolutionLimits",
      unknownLimits,
      "One or more evolution limits are unknown."
    ]
  ];

  limits =
    Join[
      $DefaultEvolutionLimits,
      suppliedLimits
    ];

  If[
    !(IntegerQ[limits["MaxGenerations"]] &&
      Positive[limits["MaxGenerations"]]),

    Return @ configurationFailure[
      "MaxGenerations",
      limits["MaxGenerations"],
      "MaxGenerations must be a positive integer."
    ]
  ];

  If[
    !positiveIntegerOrInfinityQ[limits["MaxEvents"]],

    Return @ configurationFailure[
      "MaxEvents",
      limits["MaxEvents"],
      "MaxEvents must be a positive integer or Infinity."
    ]
  ];

  If[
    !positiveNumberOrInfinityQ[limits["TimeConstraint"]],

    Return @ configurationFailure[
      "TimeConstraint",
      limits["TimeConstraint"],
      "TimeConstraint must be positive or Infinity."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Remaining options                                              *)
  (* -------------------------------------------------------------- *)

  ratioRange =
    Lookup[
      suppliedConfiguration,
      "RatioRange",
      {0., Infinity}
    ];

  If[
    !validRatioRangeQ[ratioRange],
    Return @ configurationFailure[
      "RatioRange",
      ratioRange,
      "RatioRange must be an ordered nonnegative numeric range."
    ]
  ];

  diagnostics =
    Lookup[
      suppliedConfiguration,
      "InitialStateDiagnostics",
      "Finalists"
    ];

  If[
    !MemberQ[
      {
        None,
        "Finalists",
        "SeedAndFinalists",
        "EveryCandidate"
      },
      diagnostics
    ],

    Return @ configurationFailure[
      "InitialStateDiagnostics",
      diagnostics,
      "InitialStateDiagnostics has an invalid setting."
    ]
  ];

  randomSeed =
    Lookup[
      suppliedConfiguration,
      "RandomSeed",
      Automatic
    ];

  If[
    !(randomSeed === Automatic || IntegerQ[randomSeed]),
    Return @ configurationFailure[
      "RandomSeed",
      randomSeed,
      "RandomSeed must be an integer or Automatic."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Return normalized configuration                                *)
  (* -------------------------------------------------------------- *)

  <|
    "Goal" -> goal,

    "EdgeSymmetry" -> edgeSymmetry,
    "RewriteSemantics" -> rewriteSemantics,

    "Rule" -> rule,
    "InitialState" -> initialState,

    "MutationStrategies" -> strategies,

    "RecommendedMutationStrategies" ->
      recommendedStrategies,

    "UnavailableRecommendedStrategies" ->
      unavailableRecommendedStrategies,

    "FitnessMetrics" -> metrics,
    "CustomFitnessMetrics" -> normalizedCustomMetrics,

    "Rounds" -> rounds,
    "MutationBudget" -> mutationBudget,

    "EvolutionLimits" -> limits,
    "RatioRange" -> ratioRange,

    "InitialStateDiagnostics" -> diagnostics,

    "RandomSeed" -> randomSeed
  |>
];


ValidateEvolutionConfiguration[other_] :=
  configurationFailure[
    "Configuration",
    other,
    "The configuration must be an Association."
  ];
