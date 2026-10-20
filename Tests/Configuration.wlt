PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

VerificationTest[
  AssociationQ @ ValidateEvolutionConfiguration[<||>],
  True,
  TestID -> "Config-DefaultSucceeds"
]

VerificationTest[
  ValidateEvolutionConfiguration[<||>]["MutationStrategies"],
  {"GrowthBudget", "OverlappingMatch", "GrowThenConstrain",
   "DelayedTermination", "RuntimeThrottling", "VariableRewiring"},
  TestID -> "Config-AutomaticStrategiesAllImplemented"
]

VerificationTest[
  FailureQ @ ValidateEvolutionConfiguration[<|"Goal" -> "NoSuchGoal"|>],
  True,
  TestID -> "Config-UnknownGoalFails"
]

VerificationTest[
  FailureQ @ ValidateEvolutionConfiguration[
    <|"MutationStrategies" -> {"NoSuchStrategy"}|>],
  True,
  TestID -> "Config-UnknownStrategyFails"
]

VerificationTest[
  FailureQ @ ValidateEvolutionConfiguration[
    <|"FitnessMetrics" -> {"NoSuchMetric"}|>],
  True,
  TestID -> "Config-UnknownMetricFails"
]

(* Strategy-required metrics are unioned into the selection. *)
VerificationTest[
  SubsetQ[
    ValidateEvolutionConfiguration[
      <|"FitnessMetrics" -> {"MultiwayStateCount"},
        "MutationStrategies" -> {"RuntimeThrottling"}|>]["FitnessMetrics"],
    {"MultiwayStateCount", "Runtime"}
  ],
  True,
  TestID -> "Config-RequiredMetricsUnioned"
]

VerificationTest[
  FailureQ @ ValidateEvolutionConfiguration[
    <|"CustomFitnessMetrics" -> <|"Bad" -> <|"Direction" -> "Maximize"|>|>|>],
  True,
  TestID -> "Config-InvalidCustomMetricFails"
]

VerificationTest[
  FailureQ @ ValidateEvolutionConfiguration[
    <|"CustomFitnessMetrics" ->
      <|"MultiwayStateCount" ->
        <|"Function" -> (0 &), "Direction" -> "Maximize"|>|>|>],
  True,
  TestID -> "Config-CustomMetricNameCollisionFails"
]

VerificationTest[
  AssociationQ @ ValidateEvolutionConfiguration[
    <|"CustomFitnessMetrics" ->
      <|"MyMetric" ->
        <|"Function" -> (1 &), "Direction" -> "Maximize", "Input" -> "EvaluationContext"|>|>|>],
  True,
  TestID -> "Config-ValidCustomMetricSucceeds"
]

VerificationTest[
  FailureQ /@ {
    ValidateEvolutionConfiguration[<|"Rounds" -> 0|>],
    ValidateEvolutionConfiguration[<|"Rounds" -> 1.5|>],
    ValidateEvolutionConfiguration[<|"MutationBudget" -> -3|>],
    ValidateEvolutionConfiguration[<|"RatioRange" -> {2., 1.}|>],
    ValidateEvolutionConfiguration[<|"RatioRange" -> {-1., 2.}|>],
    ValidateEvolutionConfiguration[<|"RandomSeed" -> 1.5|>],
    ValidateEvolutionConfiguration[<|"InitialStateDiagnostics" -> "Bogus"|>],
    ValidateEvolutionConfiguration[<|"Rule" -> 42|>],
    ValidateEvolutionConfiguration[<|"InitialState" -> {{1, {2}}}|>]
  },
  ConstantArray[True, 9],
  TestID -> "Config-InvalidScalarOptionsFail"
]

VerificationTest[
  FailureQ /@ {
    ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"NoSuchLimit" -> 5|>|>],
    ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"MaxGenerations" -> 0|>|>],
    ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"MaxEvents" -> -1|>|>],
    ValidateEvolutionConfiguration[<|"EvolutionLimits" -> <|"TimeConstraint" -> 0|>|>]
  },
  ConstantArray[True, 4],
  TestID -> "Config-InvalidLimitsFail"
]

VerificationTest[
  ValidateEvolutionConfiguration[
    <|"EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>]["EvolutionLimits"],
  <|"MaxGenerations" -> 3, "MaxEvents" -> 1000, "MaxStates" -> Infinity, "TimeConstraint" -> 30.|>,
  TestID -> "Config-LimitsMergedWithDefaults"
]

(* Private registries must not leak into the public context. *)
VerificationTest[
  Names["SamuelFrerichs`StructureAdaptiveEvolution`$*"],
  {},
  TestID -> "Config-RegistriesArePrivate"
]

VerificationTest[
  Names["Global`$MutationStrategyRegistry"] === {} &&
    Names["Global`$FitnessMetricRegistry"] === {} &&
    Names["Global`$GoalPresets"] === {},
  True,
  TestID -> "Config-NoGlobalRegistryLeakage"
]
