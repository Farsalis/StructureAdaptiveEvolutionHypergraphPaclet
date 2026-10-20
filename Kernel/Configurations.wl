(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ================================================================ *)
(* Default goal presets                                             *)
(* ================================================================ *)

(* A preset recommends mutation strategies and fitness metrics. Strategies
   that are not implemented or not compatible with the active universe are
   dropped under "MutationStrategies" -> Automatic and reported in
   "UnavailableRecommendedStrategies". Further presets are registered by the
   modules that implement their strategies and metrics. *)
$GoalPresets = <|

  "LargeFiniteTerminating" -> <|

    "Description" ->
      "Large multiway systems that verifiably halt within the explored limits.",

    "MutationStrategies" -> {
      "GrowthBudget",
      "OverlappingMatch",
      "GrowThenConstrain",
      "DelayedTermination",
      "RuntimeThrottling",
      "VariableRewiring",
      "OrderedEdgePermutation"
    },

    (* MultiwayLongestDerivation (exact longest derivation of a halted
       system) is the lifetime objective; the BFS discovery depth
       MultiwayLifetime is kept as a diagnostic. *)
    "FitnessMetrics" -> {
      "HaltedWithinCapQ",
      "MultiwayStateCount",
      "MultiwayTransitionCount",
      "MultiwayLongestDerivation",
      "MultiwayLifetime",
      "HGMaxVerticesCount",
      "HGMaxEdgesCount",
      "HGMaxEdgeToVertexRatio",
      "Runtime"
    }

  |>

|>;


registerGoalPresets[presets_Association] := (
  Scan[
    If[
      !(AssociationQ[#] && MatchQ[Lookup[#, "MutationStrategies"], {__String}] &&
        MatchQ[Lookup[#, "FitnessMetrics"], {__String}] &&
        MatchQ[Lookup[#, "MetricOverrides", <||>], _Association?(AllTrue[Values[#], AssociationQ] &)]),
      Throw[Failure["InvalidGoalPreset", <|"Preset" -> #|>], "registration"]
    ] &,
    Values[presets]
  ];
  $GoalPresets = Join[$GoalPresets, presets];
)


(* ================================================================ *)
(* Defaults                                                         *)
(* ================================================================ *)

$DefaultEvolutionLimits = <|
  "MaxGenerations" -> 10,
  "MaxEvents" -> 1000,
  "MaxStates" -> Infinity,
  "TimeConstraint" -> 30.
|>;


Options[StructureAdaptiveEvolution] = {

  "Goal" -> "LargeFiniteTerminating",

  "EdgeSymmetry" -> "Unordered",
  "SymmetryGroups" -> Automatic,
  "RewriteSemantics" -> "EdgeToken",
  "CanonicalForm" -> "Exact",

  "Rule" -> Automatic,
  "InitialState" -> Automatic,

  "MutationStrategies" -> Automatic,
  "StrategyOptions" -> <||>,
  "AdaptiveWeights" -> True,

  "FitnessMetrics" -> Automatic,
  "CustomFitnessMetrics" -> <||>,
  "MetricOverrides" -> <||>,
  "MissingObjectivePolicy" -> "Worst",
  "CompromisePolicy" -> None,

  "Rounds" -> 1,
  "MutationBudget" -> 20,

  "EvolutionLimits" -> <||>,
  "RatioRange" -> {0., Infinity},

  "EvolutionArtifacts" -> Automatic,
  "UpdateOrder" -> "Generational",
  "UpdateOrders" -> Automatic,

  "InitialStateDiagnostics" -> "Finalists",

  "Parallelization" -> False,
  "ReuseEvaluations" -> False,
  "ResumeFrom" -> None,

  "RandomSeed" -> Automatic
};


$DefaultUpdateOrders = {"Sequential", "LeastRecent", "MostRecent", {"Random", 1}};


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
  rule === Automatic || MatchQ[rule, _Rule | {__Rule}];


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


validRangeSpecQ[{minimum_, maximum_}] :=
  (NumericQ[minimum] || minimum === -Infinity) &&
  (NumericQ[maximum] || maximum === Infinity) &&
  TrueQ[minimum <= maximum];

validRangeSpecQ[_] := False;


validCallableQ[value_] :=
  MatchQ[value, _Function | _Symbol];


validUpdateOrderQ[order_] :=
  MatchQ[order, "Generational" | "Sequential" | "LeastRecent" | "MostRecent" | {"Random", _Integer}];


(* ================================================================ *)
(* Declared slot-symmetry groups                                    *)
(* ================================================================ *)

$MaxDeclaredGroupOrder = 720;


(* All elements of a slot-symmetry group of arity k as permutation lists, or
   $Failed. Named groups: "Trivial" (= "Ordered"), "Symmetric", "Cyclic",
   "Dihedral"; any permutation group object or list of Cycles generators
   acting on Range[k]. *)
symmetryGroupElements[k_Integer?NonNegative, spec_] := Module[{elements},
  elements = Switch[
    spec,
    "Trivial" | "Ordered", {Range[k]},
    "Symmetric", If[k > 6, $Failed, Permutations[Range[k]]],
    "Cyclic", Table[RotateLeft[Range[k], i], {i, 0, Max[k - 1, 0]}],
    "Dihedral",
      If[
        k <= 2,
        Permutations[Range[k]],
        Join[
          Table[RotateLeft[Range[k], i], {i, 0, k - 1}],
          Table[RotateLeft[Reverse[Range[k]], i], {i, 0, k - 1}]
        ]
      ],
    {___Cycles}, symmetryGroupElements[k, PermutationGroup[spec]],
    _PermutationGroup | _SymmetricGroup | _CyclicGroup | _DihedralGroup | _AlternatingGroup,
      Quiet @ Check[
        If[
          Max[0, PermutationMax /@ GroupGenerators[spec]] > k ||
            !TrueQ[GroupOrder[spec] <= $MaxDeclaredGroupOrder],
          $Failed,
          PermutationList[#, k] & /@ GroupElements[spec]
        ],
        $Failed
      ],
    (* The normalized form: all elements as permutation lists, accepted as
       given when they form a group, so validation is idempotent. *)
    _?(explicitGroupElementsQ[k, #] &), spec,
    _, $Failed
  ];
  If[
    ListQ[elements],
    DeleteDuplicates @ Prepend[elements, Range[k]],
    $Failed
  ]
]

symmetryGroupElements[___] := $Failed


explicitGroupElementsQ[k_Integer, spec_] :=
  MatchQ[spec, {{___Integer} ..}] &&
    AllTrue[spec, Sort[#] === Range[k] &] &&
    Length[spec] <= $MaxDeclaredGroupOrder &&
    With[{set = DeleteDuplicates[spec]},
      SubsetQ[set, Flatten[Outer[#1[[#2]] &, set, set, 1], 1]]
    ]


normalizeSymmetryGroups[spec_Association] := Module[{normalized, bad},
  bad = Select[
    Keys[spec],
    !(IntegerQ[#] && NonNegative[#]) && # =!= "Default" &
  ];
  If[
    bad =!= {},
    Return @ configurationFailure[
      "SymmetryGroups",
      bad,
      "SymmetryGroups keys must be arities (nonnegative integers) or \"Default\"."
    ]
  ];
  If[
    KeyExistsQ[spec, "Default"] &&
      !MemberQ[{"Trivial", "Ordered", "Symmetric", "Cyclic", "Dihedral"}, spec["Default"]],
    Return @ configurationFailure[
      "SymmetryGroups",
      spec["Default"],
      "The \"Default\" symmetry group must be a named group: \"Trivial\", \"Symmetric\", \"Cyclic\" or \"Dihedral\"."
    ]
  ];
  normalized = Association @ KeyValueMap[
    Function[{arity, group},
      arity -> If[arity === "Default", group, symmetryGroupElements[arity, group]]
    ],
    spec
  ];
  bad = Keys @ Select[normalized, # === $Failed &];
  If[
    bad =!= {},
    configurationFailure[
      "SymmetryGroups",
      KeyTake[spec, bad],
      "Each symmetry group must be \"Trivial\", \"Symmetric\", \"Cyclic\", \"Dihedral\", a permutation group or a list of Cycles acting on the slots of its arity (order at most " <>
        ToString[$MaxDeclaredGroupOrder] <> ")."
    ],
    KeySort[normalized]
  ]
]

normalizeSymmetryGroups[Automatic] := <||>

normalizeSymmetryGroups[other_] :=
  configurationFailure[
    "SymmetryGroups",
    other,
    "SymmetryGroups must be an Association arity -> group."
  ]


(* ================================================================ *)
(* Metric specifications                                            *)
(* ================================================================ *)

$AllowedMetricDirections = {"Maximize", "Minimize", "Target", "Range"};
$AllowedMetricStages = {"Objective", "Constraint", "Diagnostic"};
$AllowedMetricOverrideKeys = {
  "Stage", "Direction", "Target", "Tolerance", "Range", "Threshold", "Parameters"
};


(* Problems with a (merged) metric specification, as a list of messages.
   kind is "Registered" (value type known from the registry) or "Custom"
   (numeric Maximize/Minimize constraints without a Threshold are rejected
   on the baseline evaluation instead). *)
metricSpecificationProblems[specification_Association, kind_String] := Module[
  {problems = {}, direction, stage},

  direction = Lookup[specification, "Direction", Missing["KeyAbsent", "Direction"]];
  stage = Lookup[specification, "Stage", "Objective"];

  If[
    !MemberQ[$AllowedMetricDirections, direction],
    AppendTo[problems, "\"Direction\" must be \"Maximize\", \"Minimize\", \"Target\" or \"Range\"."]
  ];
  If[
    !MemberQ[$AllowedMetricStages, stage],
    AppendTo[problems, "\"Stage\" must be \"Objective\", \"Constraint\" or \"Diagnostic\"."]
  ];
  If[
    direction === "Target" && !NumericQ[Lookup[specification, "Target", Missing[]]],
    AppendTo[problems, "A \"Target\" direction needs a numeric \"Target\"."]
  ];
  If[
    KeyExistsQ[specification, "Range"] && !validRangeSpecQ[specification["Range"]],
    AppendTo[problems, "\"Range\" must be an ordered pair {min, max}."]
  ];
  If[
    KeyExistsQ[specification, "Tolerance"] &&
      !(NumericQ[specification["Tolerance"]] && TrueQ[specification["Tolerance"] >= 0]),
    AppendTo[problems, "\"Tolerance\" must be a nonnegative number."]
  ];
  If[
    KeyExistsQ[specification, "Threshold"] && !NumericQ[specification["Threshold"]],
    AppendTo[problems, "\"Threshold\" must be numeric."]
  ];
  If[
    stage === "Constraint" && direction === "Target" && !KeyExistsQ[specification, "Tolerance"],
    AppendTo[
      problems,
      "A \"Target\" constraint needs an explicit \"Tolerance\"; it holds when Abs[value - Target] <= Tolerance."
    ]
  ];
  If[
    kind === "Registered" && stage === "Constraint" &&
      MatchQ[direction, "Maximize" | "Minimize"] &&
      !KeyExistsQ[specification, "Threshold"] &&
      Lookup[specification, "ValueType", "Real"] =!= "Boolean",
    AppendTo[
      problems,
      "A numeric \"Maximize\"/\"Minimize\" constraint needs a \"Threshold\" (value >= Threshold, respectively value <= Threshold)."
    ]
  ];
  problems
]


validCustomMetricSpecificationQ[specification_Association] :=
  validCallableQ[Lookup[specification, "Function", Missing[]]] &&
    MemberQ[$AllowedMetricInputs, Lookup[specification, "Input", "EvaluationContext"]] &&
    validCallableQ[Lookup[specification, "Validator", NumericQ]] &&
    MatchQ[Lookup[specification, "Artifacts", {}], {___String}] &&
    SubsetQ[Keys[$ArtifactBuilders], Lookup[specification, "Artifacts", {}]] &&
    metricSpecificationProblems[normalizeCustomMetricSpecification[specification], "Custom"] === {}

validCustomMetricSpecificationQ[_] := False


normalizeCustomMetricSpecification[specification_Association] :=
  Join[
    <|
      "Input" -> "EvaluationContext",
      "Stage" -> "Objective",
      "Validator" -> NumericQ,
      "ValueType" -> Automatic,
      "Artifacts" -> {}
    |>,
    specification
  ];


(* ================================================================ *)
(* Strategies                                                       *)
(* ================================================================ *)

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
    required === None || MemberQ[Flatten[{required}], symmetry]
  ];


strategyRuleSetCompatibleQ[name_String, ruleSetQ_] :=
  !TrueQ[Lookup[Lookup[$MutationStrategyRegistry, name, <||>], "RequiresRuleSet", False]] || ruleSetQ


validateStrategyOptions[options_Association, strategies_List] := Module[{unknown, problems},
  unknown = Complement[Keys[options], Keys[$MutationStrategyRegistry]];
  If[
    unknown =!= {},
    Return @ configurationFailure[
      "StrategyOptions", unknown, "StrategyOptions names unknown mutation strategies."
    ]
  ];
  problems = Association @ KeyValueMap[
    Function[{strategy, values},
      strategy -> Module[{specs = Lookup[$MutationStrategyRegistry[strategy], "OptionSpecs", <||>]},
        Which[
          !AssociationQ[values], "the options must be an Association",
          !SubsetQ[Keys[specs], Keys[values]],
            "unknown options " <> ToString[Complement[Keys[values], Keys[specs]], InputForm],
          !AllTrue[Keys[values], TrueQ[specs[#][values[#]]] &],
            "invalid values for " <>
              ToString[Select[Keys[values], !TrueQ[specs[#][values[#]]] &], InputForm],
          True, None
        ]
      ]
    ],
    options
  ];
  problems = DeleteCases[problems, None];
  If[
    problems =!= <||>,
    configurationFailure["StrategyOptions", problems, "One or more strategy options are invalid."],
    options
  ]
]

validateStrategyOptions[other_, _] :=
  configurationFailure["StrategyOptions", other, "StrategyOptions must be an Association strategy -> options."]


(* ================================================================ *)
(* Main configuration validator                                     *)
(* ================================================================ *)

ValidateEvolutionConfiguration[
  suppliedConfiguration_Association
] := Module[
  {
    goal, preset, edgeSymmetry, symmetryGroups, rewriteSemantics, canonicalForm,
    rule, initialState,
    requestedStrategies, recommendedStrategies, strategies,
    unavailableRecommendedStrategies, unknownStrategies, unimplementedStrategies,
    strategyOptions, adaptiveWeights,
    requestedMetrics, customMetrics, invalidCustomMetrics, normalizedCustomMetrics,
    conflictingMetricNames, requiredMetrics, metrics, unknownMetrics,
    overrides, missingPolicy, compromisePolicy,
    rounds, mutationBudget,
    suppliedLimits, limits, unknownLimits,
    ratioRange, artifacts, updateOrder, updateOrders,
    diagnostics, parallelization, reuseEvaluations, resumeFrom, randomSeed
  },

  (* -------------------------------------------------------------- *)
  (* Goal                                                           *)
  (* -------------------------------------------------------------- *)

  goal = Lookup[suppliedConfiguration, "Goal", "LargeFiniteTerminating"];

  preset = Lookup[$GoalPresets, goal, Missing["UnknownGoal"]];

  If[
    MissingQ[preset],
    Return @ configurationFailure[
      "Goal",
      goal,
      "The requested goal preset is not defined. Defined presets: " <>
        StringRiffle[Keys[$GoalPresets], ", "] <> "."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Edge symmetry (universe)                                       *)
  (* -------------------------------------------------------------- *)

  edgeSymmetry = Lookup[suppliedConfiguration, "EdgeSymmetry", "Unordered"];

  If[
    !MatchQ[edgeSymmetry, "Unordered" | "Ordered" | "Declared"],
    Return @ configurationFailure[
      "EdgeSymmetry",
      edgeSymmetry,
      "EdgeSymmetry must be \"Unordered\", \"Ordered\" or \"Declared\"."
    ]
  ];

  symmetryGroups = Lookup[suppliedConfiguration, "SymmetryGroups", Automatic];

  Which[
    edgeSymmetry === "Declared" && !AssociationQ[symmetryGroups],
    Return @ configurationFailure[
      "SymmetryGroups",
      symmetryGroups,
      "The \"Declared\" universe needs \"SymmetryGroups\" -> <|arity -> group, ...|>."
    ],

    (* <||> is the normalized form of Automatic: validation is idempotent. *)
    edgeSymmetry =!= "Declared" && !MatchQ[symmetryGroups, Automatic | <||>],
    Return @ configurationFailure[
      "SymmetryGroups",
      symmetryGroups,
      "SymmetryGroups is only meaningful with \"EdgeSymmetry\" -> \"Declared\"."
    ],

    edgeSymmetry === "Declared",
    symmetryGroups = normalizeSymmetryGroups[symmetryGroups];
    If[FailureQ[symmetryGroups], Return[symmetryGroups]],

    True,
    symmetryGroups = <||>
  ];

  rewriteSemantics = Lookup[suppliedConfiguration, "RewriteSemantics", "EdgeToken"];

  If[
    !MatchQ[rewriteSemantics, "VertexDeletion" | "EdgeToken"],
    Return @ configurationFailure[
      "RewriteSemantics",
      rewriteSemantics,
      "RewriteSemantics must be \"VertexDeletion\" or \"EdgeToken\"."
    ]
  ];


  canonicalForm = Lookup[suppliedConfiguration, "CanonicalForm", "Exact"];

  If[
    !MatchQ[canonicalForm, "Native" | "Exact"],
    Return @ configurationFailure[
      "CanonicalForm",
      canonicalForm,
      "CanonicalForm must be \"Exact\" (complete, invariant canonical labelling; the default, and always used by the declared universe) or \"Native\" (WolframInstitute/Hypergraph CanonicalHypergraph)."
    ]
  ];

  If[edgeSymmetry === "Declared", canonicalForm = "Exact"];


  (* -------------------------------------------------------------- *)
  (* Rule and initial state                                         *)
  (* -------------------------------------------------------------- *)

  rule = Lookup[suppliedConfiguration, "Rule", Automatic];

  If[
    !validRuleQ[rule],
    Return @ configurationFailure[
      "Rule",
      rule,
      "Rule must be a single Rule expression, a list of rules (a rule set) or Automatic."
    ]
  ];

  initialState = Lookup[suppliedConfiguration, "InitialState", Automatic];

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

  requestedStrategies = Lookup[suppliedConfiguration, "MutationStrategies", Automatic];

  recommendedStrategies = preset["MutationStrategies"];

  strategies =
    If[
      requestedStrategies === Automatic,
      Select[
        recommendedStrategies,
        implementedStrategyQ[#] &&
          strategyEdgeSymmetryCompatibleQ[#, edgeSymmetry] &&
          strategyRuleSetCompatibleQ[#, ruleSetQ[rule]] &
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

  unknownStrategies = Complement[strategies, Keys[$MutationStrategyRegistry]];

  If[
    unknownStrategies =!= {},
    Return @ configurationFailure[
      "MutationStrategies",
      unknownStrategies,
      "One or more mutation strategies are unknown."
    ]
  ];

  unimplementedStrategies = Select[strategies, !implementedStrategyQ[#] &];

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
          strategyEdgeSymmetryCompatibleQ[#, edgeSymmetry] &&
          strategyRuleSetCompatibleQ[#, ruleSetQ[rule]] &
      ]
    ];

  strategyOptions = validateStrategyOptions[
    Lookup[suppliedConfiguration, "StrategyOptions", <||>],
    strategies
  ];
  If[FailureQ[strategyOptions], Return[strategyOptions]];

  adaptiveWeights = Lookup[suppliedConfiguration, "AdaptiveWeights", True];

  If[
    !BooleanQ[adaptiveWeights],
    Return @ configurationFailure[
      "AdaptiveWeights",
      adaptiveWeights,
      "AdaptiveWeights must be True (credit-based weights) or False (fixed uniform weights)."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Custom fitness metrics                                         *)
  (* -------------------------------------------------------------- *)

  customMetrics = Lookup[suppliedConfiguration, "CustomFitnessMetrics", <||>];

  If[
    !AssociationQ[customMetrics],
    Return @ configurationFailure[
      "CustomFitnessMetrics",
      customMetrics,
      "CustomFitnessMetrics must be an Association."
    ]
  ];

  conflictingMetricNames = Intersection[Keys[customMetrics], Keys[$FitnessMetricRegistry]];

  If[
    conflictingMetricNames =!= {},
    Return @ configurationFailure[
      "CustomFitnessMetrics",
      conflictingMetricNames,
      "A custom fitness metric cannot replace an existing metric."
    ]
  ];

  invalidCustomMetrics = Select[
    Keys[customMetrics],
    !validCustomMetricSpecificationQ[customMetrics[#]] &
  ];

  If[
    invalidCustomMetrics =!= {},
    Return @ configurationFailure[
      "CustomFitnessMetrics",
      Association @ Map[
        # -> If[
          AssociationQ[customMetrics[#]],
          metricSpecificationProblems[
            normalizeCustomMetricSpecification[customMetrics[#]],
            "Custom"
          ],
          {"The specification must be an Association."}
        ] &,
        invalidCustomMetrics
      ],
      "One or more custom fitness metric specifications are invalid."
    ]
  ];

  normalizedCustomMetrics = Map[normalizeCustomMetricSpecification, customMetrics];


  (* -------------------------------------------------------------- *)
  (* Metric overrides                                               *)
  (* -------------------------------------------------------------- *)

  overrides = Lookup[suppliedConfiguration, "MetricOverrides", <||>];

  If[
    !(AssociationQ[overrides] && AllTrue[Values[overrides], AssociationQ]),
    Return @ configurationFailure[
      "MetricOverrides",
      overrides,
      "MetricOverrides must be an Association metric -> <|key -> value, ...|>."
    ]
  ];

  (* An explicitly chosen goal preset may promote metrics through its own
     MetricOverrides. They apply when the preset also supplies the metric
     list; the user's fields win per metric, and every check below covers
     them. *)
  If[
    Lookup[suppliedConfiguration, "FitnessMetrics", Automatic] === Automatic,
    overrides = Merge[{Lookup[preset, "MetricOverrides", <||>], overrides}, Apply[Join]]
  ];

  With[{unknown = Complement[Keys[overrides], Keys[$FitnessMetricRegistry]]},
    If[
      unknown =!= {},
      Return @ configurationFailure[
        "MetricOverrides",
        unknown,
        "MetricOverrides applies to registered metrics only; set the fields of custom metrics directly."
      ]
    ]
  ];

  With[
    {
      badKeys = Select[overrides, !SubsetQ[$AllowedMetricOverrideKeys, Keys[#]] &],
      problems = DeleteCases[
        Association @ KeyValueMap[
          #1 -> metricSpecificationProblems[
            Join[$FitnessMetricRegistry[#1], #2],
            "Registered"
          ] &,
          overrides
        ],
        {}
      ]
    },
    If[
      badKeys =!= <||>,
      Return @ configurationFailure[
        "MetricOverrides",
        badKeys,
        "Overridable fields are " <> StringRiffle[$AllowedMetricOverrideKeys, ", "] <> "."
      ]
    ];
    If[
      problems =!= <||>,
      Return @ configurationFailure[
        "MetricOverrides",
        problems,
        "One or more metric overrides give an incoherent specification."
      ]
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Selected and required metrics                                  *)
  (* -------------------------------------------------------------- *)

  requestedMetrics = Lookup[suppliedConfiguration, "FitnessMetrics", Automatic];

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
      Lookup[$MutationStrategyRegistry[#], "RequiredMetrics", {}] & /@ strategies
    ];

  (* Overrides and custom metrics are explicit requests: they join the
     selected metrics. *)
  metrics =
    DeleteDuplicates @ Join[
      metrics,
      requiredMetrics,
      Keys[overrides],
      Keys[normalizedCustomMetrics]
    ];

  unknownMetrics =
    Complement[
      metrics,
      Join[Keys[$FitnessMetricRegistry], Keys[normalizedCustomMetrics]]
    ];

  If[
    unknownMetrics =!= {},
    Return @ configurationFailure[
      "FitnessMetrics",
      unknownMetrics,
      "One or more requested fitness metrics are unknown."
    ]
  ];

  missingPolicy = Lookup[suppliedConfiguration, "MissingObjectivePolicy", "Worst"];

  If[
    !MatchQ[missingPolicy, "Worst" | "Exclude"],
    Return @ configurationFailure[
      "MissingObjectivePolicy",
      missingPolicy,
      "MissingObjectivePolicy must be \"Worst\" (a Missing objective value counts as the worst value) or \"Exclude\" (the candidate leaves both fronts)."
    ]
  ];

  compromisePolicy = Lookup[suppliedConfiguration, "CompromisePolicy", None];

  If[
    !MatchQ[compromisePolicy, None | "IdealPointDistance"],
    Return @ configurationFailure[
      "CompromisePolicy",
      compromisePolicy,
      "CompromisePolicy must be None or \"IdealPointDistance\"."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Search parameters                                              *)
  (* -------------------------------------------------------------- *)

  rounds = Lookup[suppliedConfiguration, "Rounds", 1];

  If[
    !(IntegerQ[rounds] && Positive[rounds]),
    Return @ configurationFailure[
      "Rounds",
      rounds,
      "Rounds must be a positive integer."
    ]
  ];

  mutationBudget = Lookup[suppliedConfiguration, "MutationBudget", 20];

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

  suppliedLimits = Lookup[suppliedConfiguration, "EvolutionLimits", <||>];

  If[
    !AssociationQ[suppliedLimits],
    Return @ configurationFailure[
      "EvolutionLimits",
      suppliedLimits,
      "EvolutionLimits must be an Association."
    ]
  ];

  unknownLimits = Complement[Keys[suppliedLimits], Keys[$DefaultEvolutionLimits]];

  If[
    unknownLimits =!= {},
    Return @ configurationFailure[
      "EvolutionLimits",
      unknownLimits,
      "One or more evolution limits are unknown."
    ]
  ];

  limits = Join[$DefaultEvolutionLimits, suppliedLimits];

  If[
    !(IntegerQ[limits["MaxGenerations"]] && Positive[limits["MaxGenerations"]]),
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
    !positiveIntegerOrInfinityQ[limits["MaxStates"]],
    Return @ configurationFailure[
      "MaxStates",
      limits["MaxStates"],
      "MaxStates must be a positive integer or Infinity."
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
  (* Artifacts and update orders                                    *)
  (* -------------------------------------------------------------- *)

  artifacts = Lookup[suppliedConfiguration, "EvolutionArtifacts", Automatic];

  If[
    !(artifacts === Automatic ||
      (MatchQ[artifacts, {___String}] && SubsetQ[Keys[$ArtifactBuilders], artifacts])),
    Return @ configurationFailure[
      "EvolutionArtifacts",
      artifacts,
      "EvolutionArtifacts must be Automatic or a list of artifact names: " <>
        StringRiffle[Keys[$ArtifactBuilders], ", "] <> "."
    ]
  ];

  updateOrder = Lookup[suppliedConfiguration, "UpdateOrder", "Generational"];

  If[
    !validUpdateOrderQ[updateOrder],
    Return @ configurationFailure[
      "UpdateOrder",
      updateOrder,
      "UpdateOrder must be \"Generational\", \"Sequential\", \"LeastRecent\", \"MostRecent\" or {\"Random\", seed}."
    ]
  ];

  updateOrders = Replace[
    Lookup[suppliedConfiguration, "UpdateOrders", Automatic],
    Automatic -> $DefaultUpdateOrders
  ];

  If[
    !(ListQ[updateOrders] && Length[updateOrders] >= 2 && AllTrue[updateOrders, validUpdateOrderQ]),
    Return @ configurationFailure[
      "UpdateOrders",
      updateOrders,
      "UpdateOrders must be Automatic or a list of at least two update orders."
    ]
  ];


  (* -------------------------------------------------------------- *)
  (* Remaining options                                              *)
  (* -------------------------------------------------------------- *)

  ratioRange = Lookup[suppliedConfiguration, "RatioRange", {0., Infinity}];

  If[
    !validRatioRangeQ[ratioRange],
    Return @ configurationFailure[
      "RatioRange",
      ratioRange,
      "RatioRange must be an ordered nonnegative numeric range."
    ]
  ];

  diagnostics = Lookup[suppliedConfiguration, "InitialStateDiagnostics", "Finalists"];

  If[
    !MemberQ[{None, "Finalists", "SeedAndFinalists", "EveryCandidate"}, diagnostics],
    Return @ configurationFailure[
      "InitialStateDiagnostics",
      diagnostics,
      "InitialStateDiagnostics has an invalid setting."
    ]
  ];

  parallelization = Lookup[suppliedConfiguration, "Parallelization", False];

  If[
    !(BooleanQ[parallelization] || (IntegerQ[parallelization] && Positive[parallelization])),
    Return @ configurationFailure[
      "Parallelization",
      parallelization,
      "Parallelization must be False, True or a positive number of kernels."
    ]
  ];

  reuseEvaluations = Lookup[suppliedConfiguration, "ReuseEvaluations", False];

  If[
    !BooleanQ[reuseEvaluations],
    Return @ configurationFailure[
      "ReuseEvaluations",
      reuseEvaluations,
      "ReuseEvaluations must be True or False."
    ]
  ];

  resumeFrom = Lookup[suppliedConfiguration, "ResumeFrom", None];

  If[
    !(resumeFrom === None ||
      (AssociationQ[resumeFrom] && AssociationQ[Lookup[resumeFrom, "ResumeState", None]])),
    Return @ configurationFailure[
      "ResumeFrom",
      Short[resumeFrom],
      "ResumeFrom must be None or a StructureAdaptiveEvolution result."
    ]
  ];

  randomSeed = Lookup[suppliedConfiguration, "RandomSeed", Automatic];

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
    "SymmetryGroups" -> symmetryGroups,
    "RewriteSemantics" -> rewriteSemantics,
    "CanonicalForm" -> canonicalForm,

    "Rule" -> rule,
    "InitialState" -> initialState,

    "MutationStrategies" -> strategies,
    "RecommendedMutationStrategies" -> recommendedStrategies,
    "UnavailableRecommendedStrategies" -> unavailableRecommendedStrategies,
    "StrategyOptions" -> strategyOptions,
    "AdaptiveWeights" -> adaptiveWeights,

    "FitnessMetrics" -> metrics,
    "CustomFitnessMetrics" -> normalizedCustomMetrics,
    "MetricOverrides" -> overrides,
    "MissingObjectivePolicy" -> missingPolicy,
    "CompromisePolicy" -> compromisePolicy,

    "Rounds" -> rounds,
    "MutationBudget" -> mutationBudget,

    "EvolutionLimits" -> limits,
    "RatioRange" -> ratioRange,

    "EvolutionArtifacts" -> artifacts,
    "UpdateOrder" -> updateOrder,
    "UpdateOrders" -> updateOrders,

    "InitialStateDiagnostics" -> diagnostics,

    "Parallelization" -> parallelization,
    "ReuseEvaluations" -> reuseEvaluations,
    "ResumeFrom" -> resumeFrom,

    "RandomSeed" -> randomSeed
  |>
];


ValidateEvolutionConfiguration[other_] :=
  configurationFailure[
    "Configuration",
    other,
    "The configuration must be an Association."
  ];
