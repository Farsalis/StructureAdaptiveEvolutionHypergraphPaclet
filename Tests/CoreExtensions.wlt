(* Core extensions: StateCap, longest derivation, cycle witness, transition
   multiplicities, event records, rule sets, the declared-symmetry universe,
   cache identity, hard constraints, metric overrides, the missing-value
   policy, provenance, resume, fixed weights, parallel evaluation, phase
   schedules, event-level evolution and artifacts. *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";
$priv[name_String] := Symbol[$P <> name];

(* Evaluate expr with private dynamic universe variables set. *)
SetAttributes[withUniverse, HoldRest];
withUniverse[{symmetry_, groups_}, expr_] :=
  Block[
    {
      SamuelFrerichs`StructureAdaptiveEvolution`Private`$EdgeSymmetry = symmetry,
      SamuelFrerichs`StructureAdaptiveEvolution`Private`$SymmetryGroups = groups
    },
    expr
  ];

$contract = {{x, y}, {y, z}} -> {{x, z}};
$contract3 = {{x, y}, {y, z}, {z, w}} -> {{x, w}};
$grow = {{x, y}} -> {{x, z}, {z, y}};
$path3 = {{1, 2}, {2, 3}, {3, 4}};
$cycle4 = {{1, 2}, {2, 3}, {3, 4}, {4, 1}};


(* ::Section:: *)
(*StateCap*)


VerificationTest[
  Lookup[
    CanonicalMultiwayEvolution[$grow, {{1, 2}},
      <|"MaxGenerations" -> 10, "MaxEvents" -> Infinity, "MaxStates" -> 3|>],
    {"Status", "LimitsReached", "TerminalStates"}
  ],
  {"StateCap", {"MaxStates"}, {}},
  TestID -> "Core-StateCapStopsExploration"
]

VerificationTest[
  Length @ CanonicalMultiwayEvolution[$grow, {{1, 2}},
    <|"MaxGenerations" -> 10, "MaxEvents" -> Infinity, "MaxStates" -> 3|>]["States"],
  3,
  TestID -> "Core-StateCapBoundsStateCount"
]

(* A system with exactly three states halts under MaxStates -> 3; with
   MaxStates -> 2 the boundary state is never counted as terminal. *)
VerificationTest[
  {
    CanonicalMultiwayEvolution[$contract, $path3, <|"MaxStates" -> 3|>]["Status"],
    Lookup[
      CanonicalMultiwayEvolution[$contract, $path3, <|"MaxStates" -> 2|>],
      {"Status", "TerminalStates"}
    ]
  },
  {"Halted", {"StateCap", {}}},
  TestID -> "Core-StateCapBoundaryTerminals"
]

VerificationTest[
  {
    FailureQ @ ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"MaxStates" -> 0|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"MaxStates" -> 2.5|>|>],
    AssociationQ @ ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"MaxStates" -> 50|>|>]
  },
  {True, True, True},
  TestID -> "Core-MaxStatesValidation"
]


(* ::Section:: *)
(*Longest derivation, cycle witness, multiplicities, event records*)


(* Rule set {contract, contract3} on a 3-path: P3 -> P2 -> P1 and P3 -> P1.
   Breadth-first depth is 1, the longest derivation is 2. *)
VerificationTest[
  Module[{evolution, cfg, candidate},
    evolution = CanonicalMultiwayEvolution[{$contract, $contract3}, $path3];
    cfg = ValidateEvolutionConfiguration[<|
      "FitnessMetrics" -> {"MultiwayLifetime", "MultiwayLongestDerivation"},
      "MutationStrategies" -> {"VariableRewiring"}|>];
    $priv["ClearEvaluationCache"][];
    candidate = EvaluateCandidate[
      <|"CandidateID" -> "rs", "Rule" -> {$contract, $contract3}, "InitialState" -> $path3|>, cfg];
    {
      evolution["Status"],
      evolution["LongestDerivation"],
      evolution["LongestDerivationExactQ"],
      Length[evolution["States"]],
      candidate["Fitness"]
    }
  ],
  {"Halted", 2, True, 3, <|"MultiwayLifetime" -> 1, "MultiwayLongestDerivation" -> 2|>},
  TestID -> "Core-LongestDerivationExceedsBFSDepth"
]

VerificationTest[
  Module[{evolution = CanonicalMultiwayEvolution[{{x, y}} -> {{y, x}}, {{1, 2}}]},
    {
      evolution["Status"],
      evolution["LongestDerivation"],
      MatchQ[evolution["CycleWitness"], {DirectedEdge[s_, s_]}]
    }
  ],
  {"CycleDetected", Missing["CyclicStatesGraph"], True},
  TestID -> "Core-CycleWitnessAndUnboundedDerivation"
]

VerificationTest[
  Module[{evolution = CanonicalMultiwayEvolution[$contract, $cycle4]},
    {
      evolution["Status"],
      Total[Values[evolution["TransitionMultiplicities"]]] === evolution["EventCount"],
      Sort[Keys[evolution["TransitionMultiplicities"]]] === Sort[evolution["TransitionEdges"]]
    }
  ],
  {"Halted", True, True},
  TestID -> "Core-TransitionMultiplicitiesCountRawEvents"
]

VerificationTest[
  Module[{plain, recorded},
    plain = CanonicalMultiwayEvolution[$contract, $path3];
    recorded = CanonicalMultiwayEvolution[$contract, $path3, <||>, "RecordEvents" -> True];
    {
      MissingQ[plain["EventRecords"]],
      Length[recorded["EventRecords"]],
      AllTrue[recorded["EventRecords"], Length[#["Matches"]] === Length[#["Successors"]] &],
      Total[Length /@ Lookup[recorded["EventRecords"], "Matches"]] === recorded["EventCount"]
    }
  ],
  {True, 3, True, True},
  TestID -> "Core-RecordEvents"
]


(* ::Section:: *)
(*Rule sets*)


VerificationTest[
  {
    CanonicalRuleForm[{$contract, $grow}] === CanonicalRuleForm[{{{a, b}} -> {{a, c}, {c, b}}, {{p, q}, {q, r}} -> {{p, r}}}],
    CanonicalRuleForm[{$grow, {{a, b}} -> {{a, c}, {c, b}}}] === CanonicalRuleForm[$grow],
    MatchQ[CanonicalRuleForm[{$contract, $grow}], {_Rule, _Rule}],
    AssociationQ @ ValidateEvolutionConfiguration[<|"Rule" -> {$contract, $grow}|>],
    FailureQ @ CanonicalRuleForm[{$contract, 42}]
  },
  {True, True, True, True, True},
  TestID -> "Core-RuleSetCanonicalIdentity"
]

VerificationTest[
  {
    $priv["RuleApplicableQ"][{$contract, $grow}, {{1, 2}}],
    $priv["RuleApplicableQ"][{$contract, $contract3}, {{1, 2}}]
  },
  {True, False},
  TestID -> "Core-RuleSetApplicability"
]

VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> {$contract, $contract3},
      "InitialState" -> $cycle4,
      "MutationStrategies" -> {"GrowthBudget", "VariableRewiring"},
      "Rounds" -> 1,
      "MutationBudget" -> 5,
      "EvolutionLimits" -> <|"MaxGenerations" -> 4, "MaxEvents" -> 200, "TimeConstraint" -> 15.|>,
      "InitialStateDiagnostics" -> None,
      "RandomSeed" -> 8
    ];
    {
      AssociationQ[result],
      MatchQ[result["Baseline"]["Rule"], {__Rule}],
      AllTrue[
        Rest[result["Candidates"]],
        MatchQ[#["Provenance"]["RuleSetMember"], 1 | 2 | None] &
      ],
      AnyTrue[Rest[result["Candidates"]], IntegerQ[#["Provenance"]["RuleSetMember"]] &]
    }
  ],
  {True, True, True, True},
  TestID -> "Core-RuleSetSearchMutatesMembers"
]


(* ::Section:: *)
(*Declared slot-symmetry universe*)


$binaryStates = Subsets[DeleteDuplicates[Sort /@ Tuples[Range[4], 2]], {3}];

partitionBy[states_, f_] := Sort[Sort /@ GatherBy[states, f]];

VerificationTest[
  partitionBy[$binaryStates, CanonicalStateForm[#, "Unordered"] &] ===
    partitionBy[$binaryStates, CanonicalStateForm[#, "Declared", <|"Default" -> "Symmetric"|>] &],
  True,
  TestID -> "Core-DeclaredSymmetricMatchesUnordered"
]

$orderedStates = Subsets[Tuples[Range[3], 2], {2}];

VerificationTest[
  partitionBy[$orderedStates, CanonicalStateForm[#, "Ordered"] &] ===
    partitionBy[$orderedStates, CanonicalStateForm[#, "Declared", <||>] &],
  True,
  TestID -> "Core-DeclaredTrivialMatchesOrdered"
]

$cyclic = <|3 -> "Cyclic"|>;

VerificationTest[
  {
    CanonicalStateForm[{{1, 2, 3}, {1, 3, 2}}, "Declared", $cyclic] ===
      CanonicalStateForm[{{1, 2, 3}, {2, 3, 1}}, "Declared", $cyclic],
    CanonicalStateForm[{{1, 2, 3}, {3, 4, 5}}, "Declared", $cyclic] ===
      CanonicalStateForm[{{2, 3, 1}, {4, 5, 3}}, "Declared", $cyclic],
    CanonicalStateForm[{{1, 2, 3}, {3, 4, 5}}, "Ordered"] ===
      CanonicalStateForm[{{2, 3, 1}, {4, 5, 3}}, "Ordered"],
    CanonicalStateForm[{{1, 2, 3}, {1, 2, 3}}, "Declared", $cyclic] ===
      CanonicalStateForm[{{1, 2, 3}, {2, 3, 1}}, "Declared", $cyclic]
  },
  {False, True, False, True},
  TestID -> "Core-DeclaredCyclicEquivalence"
]

(* Completeness against brute force: equal canonical forms exactly when some
   vertex relabelling maps the multiset of edge orbits onto the other. *)
bruteCanonical[state_] := Module[{vertices = Union @ Flatten[state], forms},
  forms = Map[
    Function[perm,
      With[{relabel = AssociationThread[vertices, perm]},
        Sort[
          Function[edge, First @ Sort[Table[RotateLeft[relabel /@ edge, i], {i, 0, Length[edge] - 1}]]] /@ state
        ]
      ]
    ],
    Permutations[Range @ Length[vertices]]
  ];
  First @ Sort[forms]
];

VerificationTest[
  BlockRandom[
    SeedRandom[20261019];
    Module[{states},
      states = DeleteDuplicates @ Table[RandomInteger[{1, 4}, {RandomInteger[{1, 3}], 3}], {80}];
      partitionBy[states, CanonicalStateForm[#, "Declared", $cyclic] &] ===
        partitionBy[states, bruteCanonical]
    ]
  ],
  True,
  TestID -> "Core-DeclaredCyclicCompleteOnRandomStates"
]

VerificationTest[
  {
    CanonicalRuleForm[{{x, y, z}} -> {{y, z, w}}, "Declared", $cyclic] ===
      CanonicalRuleForm[{{b, c, a}} -> {{c, d, b}}, "Declared", $cyclic],
    CanonicalRuleForm[{{x, y, z}} -> {{y, z, w}}, "Declared", $cyclic] ===
      CanonicalRuleForm[{{x, y, z}} -> {{z, y, w}}, "Declared", $cyclic],
    CanonicalRuleForm[{{x, y, z}} -> {{y, z, w}}, "Declared", $cyclic] ===
      CanonicalRuleForm[{{x, y, z}} -> {{z, w, y}}, "Declared", $cyclic]
  },
  {True, False, True},
  TestID -> "Core-DeclaredRuleCanonicalization"
]

(* Matching respects the declared group: {x, x, y} matches (1, 2, 1) only
   when the slots are cyclically symmetric. *)
VerificationTest[
  {
    withUniverse[{"Ordered", <||>}, $priv["RuleApplicableQ"][{{x, x, y}} -> {}, {{1, 2, 1}}]],
    withUniverse[{"Declared", <|3 -> {{1, 2, 3}}|>}, $priv["RuleApplicableQ"][{{x, x, y}} -> {}, {{1, 2, 1}}]],
    withUniverse[{"Declared", <|3 -> {{1, 2, 3}, {2, 3, 1}, {3, 1, 2}}|>}, $priv["RuleApplicableQ"][{{x, x, y}} -> {}, {{1, 2, 1}}]]
  },
  {False, False, True},
  TestID -> "Core-DeclaredMatchingUsesOrbits"
]

VerificationTest[
  Module[{u, d, limits = <|"MaxGenerations" -> 3, "MaxEvents" -> Infinity|>},
    u = withUniverse[{"Unordered", <||>}, CanonicalMultiwayEvolution[$grow, {{1, 2}, {2, 3}}, limits]];
    d = withUniverse[{"Declared", <|2 -> {{1, 2}, {2, 1}}|>}, CanonicalMultiwayEvolution[$grow, {{1, 2}, {2, 3}}, limits]];
    {Length[u["States"]] === Length[d["States"]], u["Status"] === d["Status"], Length[u["States"]] > 1}
  ],
  {True, True, True},
  TestID -> "Core-DeclaredSymmetricEvolutionMatchesUnordered"
]

VerificationTest[
  {
    FailureQ @ ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared"|>],
    ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> $cyclic|>]["SymmetryGroups"],
    FailureQ @ ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> <|2 -> CyclicGroup[3]|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"SymmetryGroups" -> $cyclic|>],
    ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> <|2 -> {Cycles[{{1, 2}}]}|>|>]["SymmetryGroups"]
  },
  {True, <|3 -> {{1, 2, 3}, {2, 3, 1}, {3, 1, 2}}|>, True, True, <|2 -> {{1, 2}, {2, 1}}|>},
  TestID -> "Core-SymmetryGroupValidation"
]

VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{x, y, z}} -> {{x, y, w}, {w, y, z}}),
      "InitialState" -> {{1, 2, 3}},
      "EdgeSymmetry" -> "Declared",
      "SymmetryGroups" -> $cyclic,
      "Rounds" -> 1,
      "MutationBudget" -> 4,
      "EvolutionLimits" -> <|"MaxGenerations" -> 2, "MaxEvents" -> 100, "TimeConstraint" -> 15.|>,
      "InitialStateDiagnostics" -> None,
      "RandomSeed" -> 3
    ];
    {AssociationQ[result], result["Provenance"]["StateEquivalence"], MemberQ[result["Configuration"]["MutationStrategies"], "OrderedEdgePermutation"]}
  ],
  {True, "ExactCanonical-DeclaredMultiset", True},
  TestID -> "Core-DeclaredUniverseSearchRuns"
]


(* ::Section:: *)
(*Exact canonical forms*)


(* Brute-force canonical form: least sorted list of edge representatives
   over all vertex relabellings (orbit = all slot permutations for
   "Unordered", the tuple itself for "Ordered"). *)
bruteUniverseCanonical[state_, universe_] := Module[{vertices = Union @ Flatten[state], edges},
  edges = If[universe === "Unordered", DeleteDuplicates[Sort /@ state], state];
  First @ Sort @ Map[
    Function[perm,
      With[{relabel = AssociationThread[vertices, perm]},
        Sort[If[universe === "Unordered", Sort[relabel /@ #], relabel /@ #] & /@ edges]
      ]
    ],
    Permutations[Range @ Length[vertices]]
  ]
];

VerificationTest[
  BlockRandom[
    SeedRandom[42];
    Module[{states},
      states = DeleteDuplicates @ Table[RandomInteger[{1, 4}, {RandomInteger[{1, 4}], RandomInteger[{2, 3}]}], {120}];
      {
        partitionBy[states, CanonicalStateForm[#, "Unordered", "Exact"] &] === partitionBy[states, bruteUniverseCanonical[#, "Unordered"] &],
        partitionBy[states, CanonicalStateForm[#, "Ordered", "Exact"] &] === partitionBy[states, bruteUniverseCanonical[#, "Ordered"] &]
      }
    ]
  ],
  {True, True},
  TestID -> "Core-ExactCanonicalComplete"
]

VerificationTest[
  BlockRandom[
    SeedRandom[43];
    Table[
      With[{state = RandomInteger[{1, 6}, {5, 3}], perm = RandomSample[Range[6]]},
        With[{copy = RandomSample[state /. Thread[Range[6] -> perm]]},
          {
            CanonicalStateForm[state, "Unordered", "Exact"] === CanonicalStateForm[copy, "Unordered", "Exact"],
            CanonicalStateForm[state, "Ordered", "Exact"] === CanonicalStateForm[Map[Identity, copy], "Ordered", "Exact"]
          }
        ]
      ],
      {150}
    ] // Flatten // DeleteDuplicates
  ],
  {True},
  TestID -> "Core-ExactCanonicalInvariant"
]

(* The native backend splits some isomorphism classes of ternary states, but
   every native canonical form is an isomorphic copy of its input: keys never
   merge non-isomorphic states. *)
VerificationTest[
  {
    CanonicalStateForm[{{4, 3, 1}, {5, 5, 1}, {4, 3, 3}, {1, 1, 5}}, "Unordered", "Exact"] ===
      CanonicalStateForm[{{2, 4, 4}, {5, 5, 3}, {2, 4, 5}, {3, 3, 5}}, "Unordered", "Exact"],
    BlockRandom[
      SeedRandom[44];
      AllTrue[
        Table[RandomInteger[{1, 5}, {4, 3}], {60}],
        CanonicalStateForm[CanonicalStateForm[#, "Unordered", "Native"], "Unordered", "Exact"] ===
          CanonicalStateForm[#, "Unordered", "Exact"] &
      ]
    ]
  },
  {True, True},
  TestID -> "Core-NativeFormsAreIsomorphicCopies"
]

VerificationTest[
  {
    CanonicalRuleForm[{{x, y}, {y, z}} -> {{x, z}}, "Unordered", "Exact"] ===
      CanonicalRuleForm[{{b, c}, {a, b}} -> {{c, a}}, "Unordered", "Exact"],
    CanonicalRuleForm[{{x, y}, {y, z}} -> {{x, z}}, "Ordered", "Exact"] ===
      CanonicalRuleForm[{{b, c}, {a, b}} -> {{a, c}}, "Ordered", "Exact"],
    CanonicalRuleForm[{{x, y}, {y, z}} -> {{x, z}}, "Ordered", "Exact"] ===
      CanonicalRuleForm[{{x, y}, {y, z}} -> {{z, x}}, "Ordered", "Exact"]
  },
  {True, True, False},
  TestID -> "Core-ExactRuleCanonicalization"
]

VerificationTest[
  Module[{native, exact},
    native = ValidateEvolutionConfiguration[<|"CanonicalForm" -> "Native"|>];
    exact = ValidateEvolutionConfiguration[<||>];
    {
      exact["CanonicalForm"],
      native["CanonicalForm"],
      ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> $cyclic, "CanonicalForm" -> "Native"|>]["CanonicalForm"],
      FailureQ @ ValidateEvolutionConfiguration[<|"CanonicalForm" -> "Fast"|>],
      EvaluateCandidate[<|"CandidateID" -> "n", "Rule" -> $contract, "InitialState" -> $path3|>, native]["EvolutionKey"] =!=
        EvaluateCandidate[<|"CandidateID" -> "n", "Rule" -> $contract, "InitialState" -> $path3|>, exact]["EvolutionKey"]
    }
  ],
  {"Exact", "Native", "Exact", True, True},
  TestID -> "Core-CanonicalFormOption"
]


(* ::Section:: *)
(*Cache identity*)


VerificationTest[
  Module[{cfgA, cfgB, candidate, a, b},
    cfgA = ValidateEvolutionConfiguration[<|"FitnessMetrics" -> {"MultiwayStateCount"}, "MutationStrategies" -> {"VariableRewiring"}|>];
    cfgB = ValidateEvolutionConfiguration[<|"FitnessMetrics" -> {"MultiwayTransitionCount"}, "MutationStrategies" -> {"VariableRewiring"}|>];
    $priv["ClearEvaluationCache"][];
    candidate = <|"CandidateID" -> "k", "Rule" -> CanonicalRuleForm[$contract], "InitialState" -> CanonicalStateForm[$path3]|>;
    a = EvaluateCandidate[candidate, cfgA];
    b = EvaluateCandidate[candidate, cfgB];
    {
      Keys[a["Fitness"]],
      Keys[b["Fitness"]],
      a["EvolutionKey"] === b["EvolutionKey"],
      a["EvaluationID"] =!= b["EvaluationID"],
      Length @ $priv["$EvaluationCache"]
    }
  ],
  {{"MultiwayStateCount"}, {"MultiwayTransitionCount"}, True, True, 1},
  TestID -> "Core-FitnessCacheSeparatesMetricSets"
]

VerificationTest[
  Module[{identity = $priv["evolutionIdentity"][CanonicalRuleForm[$contract], CanonicalStateForm[$path3], <|"MaxGenerations" -> 3|>, False]},
    {
      MemberQ[identity, $priv["$EvaluatorVersion"]],
      MemberQ[identity, $priv["hypergraphVersionString"][]],
      MemberQ[identity, $priv["pacletVersionString"][]],
      MemberQ[identity, $VersionNumber],
      StringQ[$priv["hypergraphVersionString"][]]
    }
  ],
  {True, True, True, True, True},
  TestID -> "Core-EvolutionIdentityIncludesVersions"
]


(* ::Section:: *)
(*Hard constraints*)


VerificationTest[
  Module[{sat = $priv["constraintSatisfiedQ"], target, maximize, minimize, boolMin},
    target = <|"Direction" -> "Target", "Target" -> 5, "Tolerance" -> 1|>;
    maximize = <|"Direction" -> "Maximize", "Threshold" -> 3|>;
    minimize = <|"Direction" -> "Minimize", "Threshold" -> 3|>;
    boolMin = <|"Direction" -> "Minimize"|>;
    {
      sat[#, target, <||>] & /@ {4, 6, 6.01, 3.99, Missing["InsufficientStructure"]},
      sat[#, maximize, <||>] & /@ {3, 2.99},
      sat[#, minimize, <||>] & /@ {3, 3.01},
      sat[#, boolMin, <||>] & /@ {False, True}
    }
  ],
  {{True, True, False, False, False}, {True, False}, {True, False}, {True, False}},
  TestID -> "Core-ConstraintSemantics"
]

$targetMetric[target_, tolerance_] := <|
  "Function" -> VertexCount, "Input" -> "StatesGraph", "Direction" -> "Target",
  "Target" -> target, "Stage" -> "Constraint", "Tolerance" -> tolerance
|>;

VerificationTest[
  {
    FailureQ @ ValidateEvolutionConfiguration[<|"CustomFitnessMetrics" -> <|"T" -> KeyDrop[$targetMetric[3, 0], "Tolerance"]|>|>],
    AssociationQ @ ValidateEvolutionConfiguration[<|"CustomFitnessMetrics" -> <|"T" -> $targetMetric[3, 0]|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"CustomFitnessMetrics" -> <|"T" -> $targetMetric[3, -1]|>|>]
  },
  {True, True, True},
  TestID -> "Core-TargetConstraintNeedsTolerance"
]

$solutionOptions = {
  "Rule" -> $contract,
  "InitialState" -> $cycle4,
  "Rounds" -> 1,
  "MutationBudget" -> 6,
  "EvolutionLimits" -> <|"MaxGenerations" -> 6, "MaxEvents" -> 300, "TimeConstraint" -> 20.|>,
  "InitialStateDiagnostics" -> None,
  "RandomSeed" -> 77
};

VerificationTest[
  Module[{feasible, infeasible},
    feasible = StructureAdaptiveEvolution[Sequence @@ $solutionOptions,
      "CustomFitnessMetrics" -> <|"StateCountTarget" -> $targetMetric[4, 1]|>];
    infeasible = StructureAdaptiveEvolution[Sequence @@ $solutionOptions,
      "CustomFitnessMetrics" -> <|"StateCountTarget" -> $targetMetric[1000, 0]|>];
    {
      AllTrue[feasible["SolutionParetoFront"], Abs[#["Fitness"]["StateCountTarget"] - 4] <= 1 &],
      infeasible["SolutionParetoFront"]
    }
  ],
  {True, {}},
  TestID -> "Core-TargetConstraintEnforced"
]

VerificationTest[
  Module[{failure},
    failure = StructureAdaptiveEvolution[Sequence @@ $solutionOptions,
      "CustomFitnessMetrics" -> <|"Size" -> <|"Function" -> VertexCount, "Input" -> "StatesGraph",
        "Direction" -> "Maximize", "Stage" -> "Constraint"|>|>];
    {FailureQ[failure], failure[[1]]}
  ],
  {True, "ConstraintThresholdRequired"},
  TestID -> "Core-NumericConstraintNeedsThreshold"
]


(* ::Section:: *)
(*Metric overrides, defaults, missing-value policy*)


VerificationTest[
  Module[{cfg},
    cfg = ValidateEvolutionConfiguration[<|
      "MetricOverrides" -> <|"NonIsomorphicTerminalStateCount" -> <|"Stage" -> "Objective"|>|>|>];
    {
      MemberQ[cfg["FitnessMetrics"], "NonIsomorphicTerminalStateCount"],
      $priv["resolveMetricSpecifications"][cfg]["NonIsomorphicTerminalStateCount"]["Stage"],
      FailureQ @ ValidateEvolutionConfiguration[<|"MetricOverrides" -> <|"NoSuchMetric" -> <|"Stage" -> "Objective"|>|>|>],
      FailureQ @ ValidateEvolutionConfiguration[<|"MetricOverrides" -> <|"Runtime" -> <|"Function" -> (0 &)|>|>|>],
      FailureQ @ ValidateEvolutionConfiguration[<|"MetricOverrides" -> <|"MultiwayStateCount" -> <|"Stage" -> "Constraint"|>|>|>],
      AssociationQ @ ValidateEvolutionConfiguration[<|"MetricOverrides" -> <|"MultiwayStateCount" -> <|"Stage" -> "Constraint", "Threshold" -> 3|>|>|>],
      FailureQ @ ValidateEvolutionConfiguration[<|"MetricOverrides" -> <|"MultiwayStateCount" -> <|"Direction" -> "Target"|>|>|>]
    }
  ],
  {True, "Objective", True, True, True, True, True},
  TestID -> "Core-MetricOverrides"
]

VerificationTest[
  Module[{cfg = ValidateEvolutionConfiguration[<||>], registry = $priv["$FitnessMetricRegistry"]},
    {
      SubsetQ[cfg["FitnessMetrics"], {"MultiwayTransitionCount", "MultiwayLongestDerivation", "MultiwayLifetime"}],
      registry["MultiwayLongestDerivation"]["Stage"],
      registry["MultiwayLifetime"]["Stage"],
      registry["MultiwayTransitionCount"]["Stage"]
    }
  ],
  {True, "Objective", "Diagnostic", "Objective"},
  TestID -> "Core-DefaultPresetObjectives"
]

VerificationTest[
  Module[{base, worst, exclude, candidates},
    base = <|"FitnessMetrics" -> {"MultiwayStateCount", "MultiwayLongestDerivation"},
      "MutationStrategies" -> {"VariableRewiring"}|>;
    worst = ValidateEvolutionConfiguration[base];
    exclude = ValidateEvolutionConfiguration[Append[base, "MissingObjectivePolicy" -> "Exclude"]];
    candidates = {
      <|"CandidateID" -> "a", "ValidQ" -> True,
        "Fitness" -> <|"MultiwayStateCount" -> 5, "MultiwayLongestDerivation" -> Missing["CyclicStatesGraph"]|>|>,
      <|"CandidateID" -> "b", "ValidQ" -> True,
        "Fitness" -> <|"MultiwayStateCount" -> 3, "MultiwayLongestDerivation" -> 2|>|>
    };
    {
      Sort @ Lookup[$priv["SearchParetoFront"][candidates, worst], "CandidateID"],
      Lookup[$priv["SearchParetoFront"][candidates, exclude], "CandidateID"]
    }
  ],
  {{"a", "b"}, {"b"}},
  TestID -> "Core-MissingObjectivePolicy"
]


(* ::Section:: *)
(*Geometry and density policies*)


VerificationTest[
  {
    EffectiveDimensionEstimate[{{1, 2}, {2, 3}}],
    DimensionVariance[{{1, 2}, {2, 3}}],
    NumericQ @ EffectiveDimensionEstimate[List @@@ EdgeList[GridGraph[{6, 6}]]]
  },
  {Missing["InsufficientStructure"], Missing["InsufficientStructure"], True},
  TestID -> "Core-GeometryMissingPolicy"
]

(* Geometry ignores slot order in every universe. *)
VerificationTest[
  With[{state = List @@@ EdgeList[GridGraph[{5, 5}]]},
    withUniverse[{"Ordered", <||>}, EffectiveDimensionEstimate[Reverse /@ state]] ===
      withUniverse[{"Unordered", <||>}, EffectiveDimensionEstimate[state]]
  ],
  True,
  TestID -> "Core-GeometryIgnoresOrder"
]

VerificationTest[
  {
    withUniverse[{"Unordered", <||>}, $priv["HypergraphDensity"][{{1, 1}, {1, 2}, {2, 2}}]],
    withUniverse[{"Ordered", <||>}, $priv["HypergraphDensity"][{{1, 2}, {2, 1}}]],
    withUniverse[{"Declared", <|3 -> {{1, 2, 3}, {2, 3, 1}, {3, 1, 2}}|>}, $priv["HypergraphDensity"][{{1, 2, 3}}]],
    withUniverse[{"Ordered", <||>}, $priv["EdgeMultiplicityMax"][{{1, 2}, {1, 2}, {2, 3}}]],
    withUniverse[{"Unordered", <||>}, $priv["EdgeMultiplicityMax"][{{1, 2}, {2, 1}, {2, 3}}]]
  },
  {1., 0.5, N[1/11], 2, 1},
  TestID -> "Core-DensityPolicy"
]


(* ::Section:: *)
(*Provenance, front membership, performance*)


VerificationTest[
  Module[{result, registry = $priv["$MutationStrategyRegistry"], children},
    result = StructureAdaptiveEvolution[
      "Rule" -> $contract,
      "InitialState" -> $cycle4,
      "Rounds" -> 2,
      "MutationBudget" -> 6,
      "EvolutionLimits" -> <|"MaxGenerations" -> 5, "MaxEvents" -> 200, "TimeConstraint" -> 20.|>,
      "RandomSeed" -> 11
    ];
    children = Rest[result["Candidates"]];
    {
      StringQ[result["RunID"]],
      AllTrue[children, #["Provenance"]["AppliedOperators"] =!= {} &],
      AllTrue[children,
        SubsetQ[registry[#["Strategy"]]["Operators"], Lookup[#["Provenance"]["AppliedOperators"], "Operator"]] &],
      AllTrue[children, AssociationQ[#["Provenance"]["Diff"]] &],
      Sort[Keys[result["FrontMembership"]]] === Sort[Lookup[result["Candidates"], "CandidateID"]],
      Length[result["FrontHistory"]],
      SubsetQ[Keys[result["Performance"]],
        {"FreshEvaluations", "CacheHits", "EvaluationsPerSecond", "PeakStateCount", "PeakFrontierSize", "PhaseTimings"}],
      result["Performance"]["FreshEvaluations"] >= Length[result["Candidates"]],
      StringQ[result["Provenance"]["PacletVersion"]] && StringQ[result["Provenance"]["HypergraphPacletVersion"]],
      MatchQ[result["ProposalFailures"], {___Association}],
      AllTrue[result["Candidates"], StringQ[#["EvaluationID"]] && StringQ[#["EvolutionKey"]] &],
      AssociationQ[result["SolutionChampions"]]
    }
  ],
  {True, True, True, True, True, 2, True, True, True, True, True, True},
  TestID -> "Core-RunProvenance"
]

VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[Sequence @@ $solutionOptions, "CompromisePolicy" -> "IdealPointDistance"];
    MemberQ[
      Lookup[If[result["SolutionParetoFront"] =!= {}, result["SolutionParetoFront"], result["SearchParetoFront"]], "CandidateID"],
      result["CompromiseCandidate"]
    ]
  ],
  True,
  TestID -> "Core-CompromiseCandidate"
]


(* ::Section:: *)
(*Resume, fixed weights, parallel evaluation*)


$resumeOptions = {
  "Rule" -> $grow,
  "InitialState" -> {{1, 2}},
  "MutationBudget" -> 4,
  "EvolutionLimits" -> <|"MaxGenerations" -> 3, "MaxEvents" -> 150, "TimeConstraint" -> 15.|>,
  "InitialStateDiagnostics" -> None,
  "RandomSeed" -> 31
};

VerificationTest[
  Module[{full, half, resumed},
    full = StructureAdaptiveEvolution[Sequence @@ $resumeOptions, "Rounds" -> 4];
    half = StructureAdaptiveEvolution[Sequence @@ $resumeOptions, "Rounds" -> 2];
    resumed = StructureAdaptiveEvolution[Sequence @@ $resumeOptions, "Rounds" -> 2, "ResumeFrom" -> half];
    {
      Lookup[full["Candidates"], "CandidateID"] === Lookup[resumed["Candidates"], "CandidateID"],
      Max[Abs[Values[full["FinalStrategyWeights"]] - Values[resumed["FinalStrategyWeights"]]]] < 10^-12,
      resumed["ResumeState"]["RoundsCompleted"],
      resumed["Provenance"]["ResumedFrom"] === half["RunID"]
    }
  ],
  {True, True, 4, True},
  TestID -> "Core-ResumeContinuesExactly"
]

VerificationTest[
  Module[{half, failure},
    half = StructureAdaptiveEvolution[Sequence @@ $resumeOptions, "Rounds" -> 1];
    failure = StructureAdaptiveEvolution[
      Sequence @@ ReplaceAll[$resumeOptions, ("MutationBudget" -> _) -> ("MutationBudget" -> 5)],
      "Rounds" -> 1, "ResumeFrom" -> half];
    {FailureQ[failure], failure[[1]], failure[[2]]["Fields"]}
  ],
  {True, "ResumeIncompatible", {"MutationBudget"}},
  TestID -> "Core-ResumeRejectsChangedConfiguration"
]

VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[Sequence @@ $resumeOptions, "Rounds" -> 3, "AdaptiveWeights" -> False];
    {
      Length @ DeleteDuplicates[result["StrategyWeightHistory"]],
      AllTrue[Select[result["RunLog"], #["Event"] === "Round" &], AssociationQ[#["StrategyRates"]] &]
    }
  ],
  {1, True},
  TestID -> "Core-FixedUniformWeights"
]

VerificationTest[
  Module[{options, sequential, parallel, strip},
    options = Append[$resumeOptions, "Rounds" -> 1];
    sequential = StructureAdaptiveEvolution[Sequence @@ options];
    parallel = StructureAdaptiveEvolution[Sequence @@ options, "Parallelization" -> 2];
    strip = Function[result,
      {#["CandidateID"], #["Status"], KeyDrop[#["Fitness"], "Runtime"]} & /@ result["Candidates"]
    ];
    {strip[sequential] === strip[parallel], parallel["Performance"]["FreshEvaluations"] >= 1}
  ],
  {True, True},
  TestID -> "Core-ParallelMatchesSequential"
]


(* ::Section:: *)
(*Strategy options and phase schedules*)


VerificationTest[
  Module[{cfg, small, large, grow, constrain},
    cfg = ValidateEvolutionConfiguration[<|
      "MutationStrategies" -> {"GrowThenConstrain"},
      "StrategyOptions" -> <|"GrowThenConstrain" -> <|"PhaseSchedule" -> "Sequential", "TargetVertices" -> 10, "TargetEdges" -> 10|>|>|>];
    small = <|"CandidateID" -> "p", "Rule" -> CanonicalRuleForm[$grow], "InitialState" -> {{1, 2}},
      "Fitness" -> <|"HGMaxVerticesCount" -> 3, "HGMaxEdgesCount" -> 2|>|>;
    large = Append[small, "Fitness" -> <|"HGMaxVerticesCount" -> 40, "HGMaxEdgesCount" -> 40|>];
    grow = $priv["ProposeCandidate"][small, "GrowThenConstrain", 1, 1, cfg];
    constrain = $priv["ProposeCandidate"][large, "GrowThenConstrain", 1, 2, cfg];
    {
      grow["Provenance"]["Details"]["Phase"],
      First[grow["Provenance"]["AppliedOperators"]]["Operator"],
      constrain["Provenance"]["Details"]["Phase"],
      MemberQ[{"DeleteRHSEdge", "ReduceArity", "AddLHSCondition"}, First[constrain["Provenance"]["AppliedOperators"]]["Operator"]]
    }
  ],
  {"Grow", "AddRHSVariable", "Constrain", True},
  TestID -> "Core-SequentialPhaseSchedule"
]

VerificationTest[
  {
    FailureQ @ ValidateEvolutionConfiguration[<|"StrategyOptions" -> <|"GrowThenConstrain" -> <|"PhaseSchedule" -> "Sometimes"|>|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"StrategyOptions" -> <|"GrowThenConstrain" -> <|"NoSuchOption" -> 1|>|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"StrategyOptions" -> <|"NoSuchStrategy" -> <||>|>|>]
  },
  {True, True, True},
  TestID -> "Core-StrategyOptionValidation"
]


(* ::Section:: *)
(*Registry provenance*)


VerificationTest[
  Module[{seed = ResolveAndCanonicalizeSeed[ValidateEvolutionConfiguration[<||>]]},
    If[
      FailureQ[seed],
      seed[[1]] === "SeedResolutionFailed",  (* offline fallback accepted *)
      {
        StringQ[seed["RegistryCode"]] && StringStartsQ[seed["RegistryCode"], "wm"],
        AssociationQ[seed["RegistryMetadata"]],
        StringQ[seed["RegistryVersion"]]
      } === {True, True, True}
    ]
  ],
  True,
  TestID -> "Core-RegistryProvenance"
]


(* ::Section:: *)
(*Event-level evolution and artifacts*)


VerificationTest[
  Module[{evolution = RewriteEventEvolution[$grow, {{1, 2}}, <|"MaxGenerations" -> 3|>]},
    {
      evolution["Status"],
      evolution["EventCount"],
      Length[evolution["FinalState"]],
      evolution["MaxGeneration"],
      AcyclicGraphQ[evolution["CausalGraph"]],
      VertexCount[evolution["CausalGraph"]],
      DuplicateFreeQ[Catenate[Lookup[evolution["Events"], "Inputs"]]]
    }
  ],
  {"GenerationCap", 7, 8, 3, True, 7, True},
  TestID -> "Core-EventEvolutionGenerational"
]

(* A single-event path of a halting system ends in a terminal state of the
   multiway system. *)
VerificationTest[
  Module[{terminals = CanonicalMultiwayEvolution[$contract, $cycle4]["TerminalStates"]},
    Map[
      Function[order,
        With[{evolution = RewriteEventEvolution[$contract, $cycle4, <||>, "UpdateOrder" -> order]},
          evolution["Status"] === "Terminated" && MemberQ[terminals, evolution["CanonicalFinalState"]]
        ]
      ],
      {"Sequential", "LeastRecent", "MostRecent", {"Random", 3}}
    ]
  ],
  {True, True, True, True},
  TestID -> "Core-EventEvolutionEndsInMultiwayTerminal"
]

VerificationTest[
  Module[{graph = MultiwayEvolutionGraph[CanonicalMultiwayEvolution[{$contract, $contract3}, $path3]]},
    {VertexCount[graph], EdgeCount[graph], Sort[Last /@ VertexList[graph]]}
  ],
  {4, 3, {0, 1, 1, 2}},
  TestID -> "Core-MultiwayEvolutionGraph"
]

VerificationTest[
  Module[{cfg, candidate},
    cfg = ValidateEvolutionConfiguration[<|
      "MutationStrategies" -> {"VariableRewiring"},
      "FitnessMetrics" -> {"MultiwayStateCount"},
      "EvolutionLimits" -> <|"MaxGenerations" -> 3|>,
      "CustomFitnessMetrics" -> <|
        "CausalEvents" -> <|"Function" -> VertexCount, "Input" -> "CausalGraph", "Direction" -> "Maximize", "Stage" -> "Diagnostic"|>,
        "UnrolledSize" -> <|"Function" -> VertexCount, "Input" -> "EvolutionGraph", "Direction" -> "Maximize", "Stage" -> "Diagnostic"|>
      |>|>];
    $priv["ClearEvaluationCache"][];
    candidate = EvaluateCandidate[<|"CandidateID" -> "art", "Rule" -> CanonicalRuleForm[$grow], "InitialState" -> {{1, 2}}|>, cfg];
    KeyTake[candidate["Fitness"], {"CausalEvents", "UnrolledSize"}]
  ],
  <|"CausalEvents" -> 7, "UnrolledSize" -> 4|>,
  TestID -> "Core-ArtifactInputsAreBuilt"
]


(* ::Section:: *)
(*Automorphism pruning, spatial projection, idempotent validation*)


(* Symmetric inputs that defeat twin pruning alone (sibling subtrees, a
   vertex-transitive cube, edges of a star) are labelled quickly, and the
   labels are invariant. *)
VerificationTest[
  BlockRandom[
    SeedRandom[45];
    Module[{relabel, cases, timing, invariant},
      relabel[state_] := With[{vs = Union[Flatten[state]]},
        RandomSample[state /. Thread[vs -> RandomSample[Range[Length[vs]] + 500]]]];
      cases = {
        {List @@@ EdgeList[CompleteKaryTree[6]], "Unordered"},
        {List @@@ EdgeList[HypercubeGraph[4]], "Unordered"},
        {Table[{1, i, i + 100}, {i, 2, 13}], "Unordered"},
        {Table[{i, Mod[i, 24] + 1}, {i, 24}], "Ordered"}
      };
      {timing, invariant} = AbsoluteTiming @ Map[
        CanonicalStateForm[#[[1]], #[[2]], "Exact"] === CanonicalStateForm[relabel[#[[1]]], #[[2]], "Exact"] &,
        cases
      ];
      {invariant, timing < 30}
    ]
  ],
  {{True, True, True, True}, True},
  TestID -> "Core-ExactAutomorphismPruning"
]

VerificationTest[
  Length @ ConnectedComponents @
    Symbol["SamuelFrerichs`StructureAdaptiveEvolution`Private`ToSpatialGraph"][{{1, 2, 3}, {3, 4}, {5, 6}, {7}}],
  3,
  TestID -> "Core-SpatialGraphKeepsUnaryVertices"
]

VerificationTest[
  Module[{plain, declared},
    plain = ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"MaxGenerations" -> 4|>|>];
    declared = ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> <|3 -> "Cyclic"|>|>];
    {
      ValidateEvolutionConfiguration[plain] === plain,
      ValidateEvolutionConfiguration[declared] === declared,
      (* an explicit element list must be a group: rotation by one without its square is not *)
      FailureQ @ ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> <|3 -> {{1, 2, 3}, {2, 3, 1}}|>|>]
    }
  ],
  {True, True, True},
  TestID -> "Core-ValidationIdempotent"
]


(* ::Section:: *)
(*Goal presets with metric overrides; time budget inside a step*)


VerificationTest[
  Module[{plain, explicit, metric, userWins},
    plain = ValidateEvolutionConfiguration[<|"Goal" -> "HubPruning"|>];
    explicit = ValidateEvolutionConfiguration[<|"Goal" -> "HubPruning", "FitnessMetrics" -> {"MultiwayStateCount"}|>];
    metric = First @ Keys[plain["MetricOverrides"]];
    userWins = ValidateEvolutionConfiguration[
      <|"Goal" -> "HubPruning", "MetricOverrides" -> <|metric -> <|"Stage" -> "Diagnostic"|>|>|>
    ];
    {
      Length[plain["MetricOverrides"]] > 0,
      AllTrue[Values[plain["MetricOverrides"]], #["Stage"] === "Objective" &],
      explicit["MetricOverrides"] === <||>,
      userWins["MetricOverrides"][metric]["Stage"],
      ValidateEvolutionConfiguration[plain] === plain
    }
  ],
  {True, True, True, "Diagnostic", True},
  TestID -> "Core-PresetMetricOverrides"
]

(* A step that matches a large state stays within the time constraint. *)
VerificationTest[
  Module[{time, run},
    {time, run} = AbsoluteTiming @ RewriteEventEvolution[
      {{3, 4}} -> {{1, 5}, {2, 5}, {3, 5}, {4, 5}},
      {{1, 2}, {2, 3}, {3, 4}},
      <|"MaxGenerations" -> 3, "MaxEvents" -> 150, "TimeConstraint" -> 3.|>
    ];
    {MemberQ[{"TimedOut", "GenerationCap", "EventCap"}, run["Status"]], time < 15}
  ],
  {True, True},
  TestID -> "Core-EventStepWithinTimeConstraint"
]


(* ::Section:: *)
(*Recorded seeds, git provenance, clearing preloads*)


VerificationTest[
  Module[{options, first, again},
    options = {
      "Rule" -> ({{1, 2}, {2, 3}} -> {{1, 3}}), "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
      "Rounds" -> 1, "MutationBudget" -> 3, "EvolutionLimits" -> <|"MaxGenerations" -> 4|>,
      "InitialStateDiagnostics" -> None
    };
    first = StructureAdaptiveEvolution @@ options;
    again = StructureAdaptiveEvolution @@ Append[options, "RandomSeed" -> first["Provenance"]["RandomSeed"]];
    {
      IntegerQ[first["Provenance"]["RandomSeed"]],
      Lookup[first["Candidates"], "CandidateID"] === Lookup[again["Candidates"], "CandidateID"],
      MatchQ[first["Provenance"]["PacletGitCommit"], _String | _Missing],
      MatchQ[first["Provenance"]["PacletGitDirty"], True | False | _Missing]
    }
  ],
  {True, True, True, True},
  TestID -> "Core-AutomaticSeedRecorded"
]

VerificationTest[
  Module[{priv = "SamuelFrerichs`StructureAdaptiveEvolution`Private`"},
    Symbol[priv <> "preloadEvaluations"][<|"example" -> <|"Status" -> "Halted"|>|>];
    {ClearPreloadedEvaluations[], Symbol[priv <> "$PreloadedEvaluations"]}
  ],
  {Null, <||>},
  TestID -> "Core-ClearPreloadedEvaluations"
]


(* ::Section:: *)
(*Unordered rule identity: duplicate right-hand edges*)


VerificationTest[
  {
    CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {2, 3}, {2, 3}}] === CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {2, 3}}],
    CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {3, 1}}] === CanonicalRuleForm[{{1, 2}} -> {{1, 3}}],
    CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {2, 3}, {2, 3}}, "Unordered", "Native"] ===
      CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {2, 3}}, "Unordered", "Native"],
    (* multiplicity is semantic in the ordered universe, and left-hand duplicates are kept *)
    CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {2, 3}, {2, 3}}, "Ordered"] === CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {2, 3}}, "Ordered"],
    CanonicalRuleForm[{{1, 2}, {1, 2}} -> {{1, 2}}] === CanonicalRuleForm[{{1, 2}} -> {{1, 2}}],
    (* the two rules evolve identically *)
    CanonicalMultiwayEvolution[{{1, 2}} -> {{1, 3}, {2, 3}, {2, 3}}, {{1, 2}}, <|"MaxGenerations" -> 3|>]["States"] ===
      CanonicalMultiwayEvolution[{{1, 2}} -> {{1, 3}, {2, 3}}, {{1, 2}}, <|"MaxGenerations" -> 3|>]["States"]
  },
  {True, True, True, False, False, True},
  TestID -> "Core-UnorderedRuleIgnoresDuplicateRHSEdges"
]
