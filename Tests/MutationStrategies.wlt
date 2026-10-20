PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

$testRule = {{x, y}} -> {{x, z}, {z, y}};

$validRuleQ = Symbol[$P <> "validHypergraphRuleQ"];

$mutationFunctions = {
  GrowthBudgetMutation,
  GrowThenConstrainMutation,
  OverlappingMatchMutation,
  DelayedTerminationMutation,
  RuntimeThrottlingMutation,
  AddLHSConditionMutation,
  IdentifyVariablesMutation,
  SplitVariableMutation,
  VariableRewiringMutation
};

(* Every strategy returns a supported rule or a Failure. *)
VerificationTest[
  SeedRandom[11];
  AllTrue[
    Table[#[$testRule], {25}] & /@ $mutationFunctions // Catenate,
    $validRuleQ[#] || FailureQ[#] &
  ],
  True,
  TestID -> "Strat-OutputRuleOrFailure"
]

(* The input rule is not mutated in place. *)
VerificationTest[
  SeedRandom[12];
  Scan[#[$testRule] &, $mutationFunctions];
  $testRule,
  {{x, y}} -> {{x, z}, {z, y}},
  TestID -> "Strat-InputNotMutated"
]

(* Deterministic modulo the fresh-variable name under SeedRandom. *)
VerificationTest[
  Module[{a, b},
    SeedRandom[77]; a = CanonicalRuleForm @ GrowthBudgetMutation[$testRule];
    SeedRandom[77]; b = CanonicalRuleForm @ GrowthBudgetMutation[$testRule];
    a === b
  ],
  True,
  TestID -> "Strat-DeterministicUnderSeedRandom"
]

(* GrowthBudget adds a fresh RHS-only variable and 1-2 RHS edges. *)
VerificationTest[
  SeedRandom[13];
  Module[{mutated = GrowthBudgetMutation[$testRule], newVars},
    newVars = Complement[
      DeleteDuplicates @ Flatten[{mutated[[1]], mutated[[2]]}],
      DeleteDuplicates @ Flatten[{$testRule[[1]], $testRule[[2]]}]
    ];
    {mutated[[1]] === $testRule[[1]],
     Length[mutated[[2]]] - Length[$testRule[[2]]],
     Length[newVars]}
  ],
  {True, _Integer?(1 <= # <= 2 &), 1},
  SameTest -> MatchQ,
  TestID -> "Strat-GrowthBudgetAddsFreshVariable"
]

(* Insufficient-variables edge case: arity exceeds the variable pool. *)
VerificationTest[
  SeedRandom[14];
  Module[{mutated = GrowthBudgetMutation[{{x, x, x}} -> {{x, x, x}, {x, x, x}}]},
    $validRuleQ[mutated]
  ],
  True,
  TestID -> "Strat-GrowthBudgetInsufficientVariables"
]

VerificationTest[
  FailureQ @ GrowthBudgetMutation[{} -> {}],
  True,
  TestID -> "Strat-GrowthBudgetDegenerateFails"
]

(* GrowThenConstrain phases. The constrain phase either shrinks the RHS or
   makes the LHS more specific. *)
VerificationTest[
  SeedRandom[15];
  Module[{grown = GrowThenConstrainMutation[$testRule, "Grow"],
          constrained = GrowThenConstrainMutation[$testRule, "Constrain"]},
    {Length[grown[[2]]] > Length[$testRule[[2]]],
     Length[constrained[[2]]] < Length[$testRule[[2]]] ||
       Length[constrained[[1]]] > Length[$testRule[[1]]]}
  ],
  {True, True},
  TestID -> "Strat-GrowThenConstrainPhases"
]

(* OverlappingMatch weakens the LHS. *)
VerificationTest[
  SeedRandom[16];
  Module[{mutated = OverlappingMatchMutation[{{x, y}, {y, z}} -> {{x, z}}]},
    {mutated[[2]], Length[mutated[[1]]]}
  ],
  {{{x, z}}, 1},
  TestID -> "Strat-OverlappingMatchWeakensLHS"
]

VerificationTest[
  FailureQ @ OverlappingMatchMutation[{{q}} -> {{q, q}}],
  True,
  TestID -> "Strat-OverlappingMatchDegenerateFails"
]

(* RuntimeThrottling reduces the RHS. *)
VerificationTest[
  SeedRandom[17];
  Module[{mutated = RuntimeThrottlingMutation[$testRule]},
    {mutated[[1]], Length[mutated[[2]]]}
  ],
  {{{x, y}}, 1},
  TestID -> "Strat-RuntimeThrottlingReducesRHS"
]

VerificationTest[
  FailureQ @ RuntimeThrottlingMutation[{{x, y}} -> {}],
  True,
  TestID -> "Strat-RuntimeThrottlingDegenerateFails"
]

(* DelayedTermination adds exactly one edge, on the RHS (growth) or the LHS
   (condition), leaving the other side unchanged. *)
VerificationTest[
  SeedRandom[18];
  Module[{mutated = DelayedTerminationMutation[$testRule]},
    {
      Length[mutated[[1]]] + Length[mutated[[2]]] -
        Length[$testRule[[1]]] - Length[$testRule[[2]]],
      Length[mutated[[1]]] === Length[$testRule[[1]]] ||
        Length[mutated[[2]]] === Length[$testRule[[2]]]
    }
  ],
  {1, True},
  TestID -> "Strat-DelayedTerminationAddsOneEdge"
]

(* Registry: the seven core strategies are present (modules may add more);
   every strategy is implemented with a mutation function and operators. *)
VerificationTest[
  Module[{registry = Symbol[$P <> "$MutationStrategyRegistry"]},
    {SubsetQ[Keys[registry], {"GrowthBudget", "OverlappingMatch", "GrowThenConstrain",
       "DelayedTermination", "RuntimeThrottling", "VariableRewiring",
       "OrderedEdgePermutation"}],
     AllTrue[Values[registry], TrueQ[#["ImplementedQ"]] &],
     AllTrue[Values[registry], MatchQ[#["MutationFunction"], _Symbol] &],
     AllTrue[Values[registry], MatchQ[#["Operators"], {__String}] &]}
  ],
  {True, True, True, True},
  TestID -> "Strat-RegistryComplete"
]

(* Fresh RHS variables are inert symbols with no attached values. *)
VerificationTest[
  SeedRandom[19];
  Module[{mutated = GrowthBudgetMutation[$testRule], newVars},
    newVars = Complement[
      DeleteDuplicates @ Flatten[{mutated[[1]], mutated[[2]]}],
      DeleteDuplicates @ Flatten[{$testRule[[1]], $testRule[[2]]}]
    ];
    AllTrue[newVars, Function[v, OwnValues[v] === {} && DownValues[v] === {}, HoldAll]]
  ],
  True,
  TestID -> "Strat-FreshVariablesInert"
]

(* AddLHSCondition adds exactly one LHS edge over existing LHS variables and
   leaves the RHS untouched. *)
VerificationTest[
  SeedRandom[20];
  Module[{rule = {{x, y}, {y, z}} -> {{x, z}}, results, proposals},
    results = Table[AddLHSConditionMutation[rule], {10}];
    proposals = Select[results, !FailureQ[#] &];
    {
      proposals =!= {},
      AllTrue[proposals, Length[#[[1]]] === Length[rule[[1]]] + 1 &],
      AllTrue[proposals, #[[2]] === rule[[2]] &],
      AllTrue[proposals, SubsetQ[{x, y, z}, DeleteDuplicates @ Flatten[#[[1]]]] &]
    }
  ],
  {True, True, True, True},
  TestID -> "Strat-AddLHSConditionAddsOneLHSEdge"
]

VerificationTest[
  FailureQ @ AddLHSConditionMutation[{} -> {{x, y}}],
  True,
  TestID -> "Strat-AddLHSConditionDegenerateFails"
]

(* IdentifyVariables merges two variables without introducing new ones. *)
VerificationTest[
  SeedRandom[21];
  Module[{mutated = IdentifyVariablesMutation[$testRule], oldVars, newVars},
    oldVars = DeleteDuplicates @ Flatten[{$testRule[[1]], $testRule[[2]]}];
    newVars = DeleteDuplicates @ Flatten[{mutated[[1]], mutated[[2]]}];
    {Length[newVars] < Length[oldVars], SubsetQ[oldVars, newVars]}
  ],
  {True, True},
  TestID -> "Strat-IdentifyVariablesMergesVariables"
]

VerificationTest[
  FailureQ @ IdentifyVariablesMutation[{{q, q}} -> {{q}}],
  True,
  TestID -> "Strat-IdentifyVariablesDegenerateFails"
]

(* SplitVariable introduces exactly one fresh variable while preserving the
   total number of variable occurrences. *)
VerificationTest[
  SeedRandom[22];
  Module[{mutated = SplitVariableMutation[$testRule], oldVars, newVars},
    oldVars = DeleteDuplicates @ Flatten[{$testRule[[1]], $testRule[[2]]}];
    newVars = DeleteDuplicates @ Flatten[{mutated[[1]], mutated[[2]]}];
    {
      Length[newVars] - Length[oldVars],
      Length[Flatten[{mutated[[1]], mutated[[2]]}]] ===
        Length[Flatten[{$testRule[[1]], $testRule[[2]]}]]
    }
  ],
  {1, True},
  TestID -> "Strat-SplitVariableAddsFreshVariable"
]

VerificationTest[
  FailureQ @ SplitVariableMutation[{{x, y}} -> {}],
  True,
  TestID -> "Strat-SplitVariableDegenerateFails"
]

(* VariableRewiring always yields a valid rule when either point mutation is
   applicable. *)
VerificationTest[
  SeedRandom[23];
  AllTrue[Table[VariableRewiringMutation[$testRule], {20}], $validRuleQ],
  True,
  TestID -> "Strat-VariableRewiringValidOnTestRule"
]
