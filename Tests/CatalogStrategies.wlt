(* Catalog strategies (handoff section 22: catalog 3, 4, 5, 7, 8, 10, 12,
   13, 14, 15): registration, opt-in goal presets, every new operator on
   hand-written rules, exact-operator provenance, rule-set operators, and one
   small search per preset. The presets and searches need the metrics of
   Kernel/ExtendedMetrics.wl. *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";
$priv[name_String] := Symbol[$P <> name];

SetAttributes[withUniverse, HoldRest];
withUniverse[symmetry_, expr_] :=
  Block[{SamuelFrerichs`StructureAdaptiveEvolution`Private`$EdgeSymmetry = symmetry}, expr];

$registry = $priv["$MutationStrategyRegistry"];
$presets = $priv["$GoalPresets"];
$validSpecQ = $priv["validRuleSpecQ"];

$catalogNames = {
  "SymmetryConfluence", "BoundaryPreservation", "TerminalDiversity", "MeshDensity",
  "Homogenizing", "LocalStability", "DegreeBalancing", "HubSeeding", "HubPruning",
  "CausalInvarianceStyle"
};

(* The input rule of each catalog example. *)
$catalogExamples = <|
  "SymmetryConfluence" -> ({{x, y}} -> {{x, z}, {z, y}, {z, w}}),
  "BoundaryPreservation" -> ({{x, y}} -> {{z, w}, {w, u}}),
  "TerminalDiversity" -> ({{x, y}} -> {{x, z}, {z, y}}),
  "MeshDensity" -> ({{x, y}} -> {{x, z}, {z, y}}),
  "Homogenizing" -> ({{x, y}} -> {{x, z}, {z, y}, {z, w}}),
  "LocalStability" -> ({{x, y}} -> {{x, z}, {z, y}}),
  "DegreeBalancing" -> ({{x, y}} -> {{x, w}, {w, y}, {w, z}, {w, u}}),
  "HubSeeding" -> ({{x, y}} -> {{x, z}, {z, y}}),
  "HubPruning" -> ({{x, y}} -> {{x, w}, {w, y}, {w, z}}),
  "CausalInvarianceStyle" -> ({{x, y}, {y, z}} -> {{x, w}, {w, z}})
|>;

proposalRule[proposal_Association] := proposal["Rule"];
proposalRule[proposal_] := proposal;

parentOf[rule_, symmetry_ : "Unordered"] :=
  <|"CandidateID" -> "parent", "Rule" -> CanonicalRuleForm[rule, symmetry], "InitialState" -> {{1, 2}, {2, 3}}|>;

appliedOperators[proposal_Association] := Lookup[proposal["Provenance"]["AppliedOperators"], "Operator"];

rhsDegree[rule_, var_] := Count[rule[[2]], edge_ /; MemberQ[edge, var]];

ruleVariables[rule_] := DeleteDuplicates @ Flatten[{rule[[1]], rule[[2]]}];


(* ::Section:: *)
(*Registration and opt-in presets*)


VerificationTest[
  {
    SubsetQ[Keys[$registry], $catalogNames],
    Lookup[$registry[#], "Catalog"] & /@ $catalogNames,
    AllTrue[$catalogNames,
      SubsetQ[Keys[$registry[#]], {"ImplementedQ", "MutationFunction", "Operators", "DefaultOptions", "RequiredMetrics"}] &],
    AllTrue[$catalogNames, TrueQ[$registry[#]["ImplementedQ"]] &],
    AllTrue[$catalogNames, MatchQ[$registry[#]["MutationFunction"], _Symbol] &],
    AllTrue[$catalogNames, MatchQ[$registry[#]["Operators"], {__String}] &],
    Select[$catalogNames, TrueQ[Lookup[$registry[#], "RuleSetAware", False]] &],
    Select[$catalogNames, TrueQ[Lookup[$registry[#], "RequiresRuleSet", False]] &]
  },
  {True, {3, 4, 5, 7, 8, 10, 12, 13, 14, 15}, True, True, True, True, {"HubPruning", "CausalInvarianceStyle"}, {}},
  TestID -> "Catalog-RegistryEntries"
]

VerificationTest[
  {
    Lookup[$registry[#], "Operators"] & /@ $catalogNames,
    AllTrue[$catalogNames, Keys[$registry[#]["PrimaryObjectives"]] === $registry[#]["RequiredMetrics"] &]
  },
  {
    {
      {"IdentifyVariables", "SymmetrizeRHS", "PermuteRHS"},
      {"BoundaryPreserveRHS", "DeleteDisconnectedRHS"},
      {"SplitVariable", "AddMotif", "PermuteEdgeOrder"},
      {"AddCycleMotif", "AddChainMotif", "ConservationMutate"},
      {"SymmetrizeRHS", "BoundaryPreserveRHS"},
      {"PreserveMotif", "AddStableSubstructure"},
      {"SplitVariable", "ReduceVariableReuse"},
      {"IdentifyVariables", "AddStarMotif"},
      {"AddRule", "ContractionRule", "DeleteRule"},
      {"SymmetrizeRHS", "BoundaryPreserveRHS", "AddInverseRule"}
    },
    True
  },
  TestID -> "Catalog-OperatorsAndRequiredMetrics"
]

(* Every catalog quantity maps to a registered metric (needs ExtendedMetrics.wl). *)
VerificationTest[
  Complement[
    Union @ Flatten @ Map[
      Join[Keys[$registry[#]["PrimaryObjectives"]], Keys[$registry[#]["SupplementalObjectives"]], $registry[#]["RequiredMetrics"]] &,
      $catalogNames
    ],
    Keys[$priv["$FitnessMetricRegistry"]]
  ],
  {},
  TestID -> "Catalog-ObjectivesAreRegisteredMetrics"
]

(* Opt-in: the default goal recommends none of the catalog strategies. *)
VerificationTest[
  {
    Intersection[$presets["LargeFiniteTerminating"]["MutationStrategies"], $catalogNames],
    Intersection[ValidateEvolutionConfiguration[<||>]["MutationStrategies"], $catalogNames],
    ValidateEvolutionConfiguration[<||>]["Goal"]
  },
  {{}, {}, "LargeFiniteTerminating"},
  TestID -> "Catalog-StrategiesAreOptIn"
]

VerificationTest[
  {
    SubsetQ[Keys[$presets], $catalogNames],
    AllTrue[$catalogNames, $presets[#]["MutationStrategies"] === {#} &],
    AllTrue[$catalogNames,
      $presets[#]["FitnessMetrics"] ===
        Join[Keys[$registry[#]["PrimaryObjectives"]], {"HaltedWithinCapQ", "MultiwayStateCount"}] &],
    AllTrue[$catalogNames, $presets[#]["Catalog"] === $registry[#]["Catalog"] &],
    AllTrue[$catalogNames, Keys[$presets[#]["MetricOverrides"]] === Keys[$registry[#]["PrimaryObjectives"]] &],
    AllTrue[$catalogNames, StringQ[$presets[#]["Description"]] &]
  },
  {True, True, True, True, True, True},
  TestID -> "Catalog-PresetsRegistered"
]

(* Every preset validates, selects exactly its strategy and keeps its
   metrics (needs ExtendedMetrics.wl). *)
VerificationTest[
  Map[
    Function[name,
      With[{config = ValidateEvolutionConfiguration[<|"Goal" -> name|>]},
        If[
          AssociationQ[config],
          {config["MutationStrategies"] === {name}, SubsetQ[config["FitnessMetrics"], $presets[name]["FitnessMetrics"]]},
          config
        ]
      ]
    ],
    $catalogNames
  ],
  ConstantArray[{True, True}, 10],
  TestID -> "Catalog-PresetsValidate"
]

(* Presets cannot carry MetricOverrides into the configuration yet; passed
   explicitly, the preset's overrides make the primary objectives Pareto
   objectives in the catalog's direction. *)
VerificationTest[
  Map[
    Function[name,
      Module[{config, specifications},
        config = ValidateEvolutionConfiguration[<|"Goal" -> name, "MetricOverrides" -> $presets[name]["MetricOverrides"]|>];
        If[
          !AssociationQ[config],
          config,
          specifications = $priv["resolveMetricSpecifications"][config];
          AllTrue[
            Normal @ $registry[name]["PrimaryObjectives"],
            specifications[First[#]]["Stage"] === "Objective" && specifications[First[#]]["Direction"] === Last[#] &
          ]
        ]
      ]
    ],
    $catalogNames
  ],
  ConstantArray[True, 10],
  TestID -> "Catalog-PresetOverridesPromoteObjectives"
]

VerificationTest[
  {
    FailureQ @ ValidateEvolutionConfiguration[<|"MutationStrategies" -> {"MeshDensity"},
      "StrategyOptions" -> <|"MeshDensity" -> <|"MaxRHSDegree" -> 0|>|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"MutationStrategies" -> {"HubSeeding"},
      "StrategyOptions" -> <|"HubSeeding" -> <|"StarEdges" -> {3, 1}|>|>|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"MutationStrategies" -> {"HubPruning"},
      "StrategyOptions" -> <|"HubPruning" -> <|"ContractionDegree" -> 1|>|>|>],
    AssociationQ @ ValidateEvolutionConfiguration[<|"MutationStrategies" -> {"MeshDensity", "HubSeeding", "HubPruning"},
      "StrategyOptions" -> <|
        "MeshDensity" -> <|"MaxRHSDegree" -> Infinity|>,
        "HubSeeding" -> <|"StarEdges" -> {2, 3}|>,
        "HubPruning" -> <|"ContractionDegree" -> 3|>
      |>|>]
  },
  {True, True, True, True},
  TestID -> "Catalog-StrategyOptionsValidated"
]


(* ::Section:: *)
(*Operators on hand-written rules*)


(* SymmetrizeRHS: z and w are interchangeable RHS-only variables; the images
   of the RHS under z <-> w that are missing are added. *)
VerificationTest[
  $priv["symmetrizeRHSDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}, {z, w}}],
  {{x, y}} -> {{x, z}, {z, y}, {z, w}, {x, w}, {w, y}},
  TestID -> "Catalog-SymmetrizeRHSClosesExchange"
]

(* x <-> y maps the unordered LHS onto itself, so the RHS is closed under it. *)
VerificationTest[
  $priv["symmetrizeRHSDraw"]["T"][{{x, y}} -> {{x, z}}],
  {{x, y}} -> {{x, z}, {y, z}},
  TestID -> "Catalog-SymmetrizeRHSUsesLHSAutomorphism"
]

(* No exchange breaks the RHS symmetry: z gets a fresh twin (repeated
   template). *)
VerificationTest[
  {
    CanonicalRuleForm @ $priv["symmetrizeRHSDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}],
    FailureQ @ $priv["symmetrizeRHSDraw"]["T"][{{x, y}} -> {{y, x}}]
  },
  {CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}, {x, u}, {u, y}}], True},
  TestID -> "Catalog-SymmetrizeRHSTwin"
]

VerificationTest[
  BlockRandom[
    SeedRandom[3];
    AllTrue[
      Table[$priv["boundaryPreserveRHSDraw"]["T"][{{x, y}} -> {{z, w}, {w, u}}], {12}],
      Function[rule,
        rule[[1]] === {{x, y}} &&
          SubsetQ[rule[[2]], {{z, w}, {w, u}}] &&
          SubsetQ[Flatten[rule[[2]]], {x, y}] &&
          AllTrue[$priv["catalogComponents"][rule[[2]]], Intersection[#, {x, y}] =!= {} &]
      ]
    ]
  ],
  True,
  TestID -> "Catalog-BoundaryPreserveRHSConnectsEveryComponent"
]

VerificationTest[
  {
    $priv["deleteDisconnectedRHSDraw"]["T"][{{x, y}} -> {{x, z}, {u, w}, {w, v}}],
    FailureQ @ $priv["deleteDisconnectedRHSDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}],
    FailureQ @ $priv["boundaryPreserveRHSDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}]
  },
  {{{x, y}} -> {{x, z}}, True, True},
  TestID -> "Catalog-DeleteDisconnectedRHS"
]

VerificationTest[
  BlockRandom[
    SeedRandom[5];
    AllTrue[
      Table[$priv["addMotifDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}], {12}],
      Function[rule,
        rule[[1]] === {{x, y}} &&
          Take[rule[[2]], 2] === {{x, z}, {z, y}} &&
          1 <= Length[rule[[2]]] - 2 <= 2 &&
          MemberQ[{x, y, z}, rule[[2, 3, 1]]]
      ]
    ]
  ],
  True,
  TestID -> "Catalog-AddMotifAttachesAtOneVertex"
]

(* The catalog-7 example: x -> z -> y is closed by y -> x. *)
VerificationTest[
  $priv["addCycleMotifDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}],
  {{x, y}} -> {{x, z}, {z, y}, {y, x}},
  TestID -> "Catalog-AddCycleMotifCatalogExample"
]

VerificationTest[
  {
    CanonicalRuleForm @ $priv["addChainMotifDraw"]["T"][{{x, y}} -> {{x, y}}],
    CanonicalRuleForm @ $priv["addCycleMotifDraw"]["T"][{{x, y}} -> {{x, y}}]
  },
  {
    CanonicalRuleForm[{{x, y}} -> {{x, u}, {u, y}}],
    CanonicalRuleForm[{{x, y}} -> {{x, y}, {x, a}, {a, b}, {b, x}}]
  },
  TestID -> "Catalog-AddChainMotifSubdividesAndFreshCycle"
]

(* ConservationMutate keeps the LHS, the RHS edge count and the number of
   created (RHS-only) variables. *)
VerificationTest[
  BlockRandom[
    SeedRandom[6];
    Module[{rule = {{x, y}} -> {{x, z}, {z, y}, {z, w}}, results, created},
      created[r_] := Length @ Complement[DeleteDuplicates @ Flatten[r[[2]]], Flatten[r[[1]]]];
      results = Table[$priv["catalogOperator"]["T", $priv["conservationMutateDraw"]["T"], 8][rule], {15}];
      results = Select[results, !FailureQ[#] &];
      {
        results =!= {},
        AllTrue[results, #[[1]] === rule[[1]] && Length[#[[2]]] === 3 && created[#] === 2 &],
        AllTrue[results, CanonicalRuleForm[#] =!= CanonicalRuleForm[rule] &]
      }
    ]
  ],
  {True, True, True},
  TestID -> "Catalog-ConservationMutateConservesGrowthBudget"
]

VerificationTest[
  BlockRandom[
    SeedRandom[7];
    AllTrue[
      Table[MeshDensityMutation[{{x, y}} -> {{x, z}, {z, y}}, <|"MaxRHSDegree" -> 2|>], {15}],
      FailureQ[#] || $priv["catalogMaxDegree"][#[[2]]] <= 2 &
    ]
  ],
  True,
  TestID -> "Catalog-MeshDensityDegreeCap"
]

VerificationTest[
  {
    $priv["preserveMotifDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}],
    FailureQ @ $priv["preserveMotifDraw"]["T"][{{x, y}} -> {{y, x}, {y, z}}]
  },
  {{{x, y}} -> {{x, z}, {z, y}, {x, y}}, True},
  TestID -> "Catalog-PreserveMotif"
]

(* The catalog-10 shape: a new LHS edge over LHS variables (here a loop,
   since {x, y} is already required) is written back unchanged. *)
VerificationTest[
  BlockRandom[
    SeedRandom[8];
    Module[{rule = {{x, y}} -> {{x, z}, {z, y}}, results},
      results = Table[$priv["catalogOperator"]["T", $priv["addStableSubstructureDraw"]["T"], 6][rule], {10}];
      results = Select[results, !FailureQ[#] &];
      {
        results =!= {},
        SubsetQ[{{x, x}, {y, y}}, Union[Last /@ results[[All, 1]]]],
        AllTrue[results, Most[#[[1]]] === rule[[1]] && #[[2]] === Append[rule[[2]], Last[#[[1]]]] &]
      }
    ]
  ],
  {True, True, True},
  TestID -> "Catalog-AddStableSubstructure"
]

$hubRule = {{x, y}} -> {{x, w}, {w, y}, {w, z}, {w, u}};

VerificationTest[
  BlockRandom[
    SeedRandom[9];
    AllTrue[
      Table[$priv["splitHubDraw"]["T"][$hubRule], {8}],
      #[[1]] === $hubRule[[1]] && rhsDegree[#, w] === 3 &&
        Length[Complement[ruleVariables[#], ruleVariables[$hubRule]]] === 1 &
    ]
  ],
  True,
  TestID -> "Catalog-SplitVariableAtHub"
]

(* The catalog-12 move: one hub edge is rerouted to a least-used variable. *)
VerificationTest[
  BlockRandom[
    SeedRandom[10];
    AllTrue[
      Table[$priv["catalogOperator"]["T", $priv["reduceVariableReuseDraw"]["T"], 6][$hubRule], {8}],
      #[[1]] === $hubRule[[1]] && rhsDegree[#, w] === 3 && Length[#[[2]]] === 4 &&
        SubsetQ[ruleVariables[$hubRule], ruleVariables[#]] &&
        $priv["catalogMaxDegree"][#[[2]]] === 3 &
    ]
  ],
  True,
  TestID -> "Catalog-ReduceVariableReuse"
]

VerificationTest[
  BlockRandom[
    SeedRandom[11];
    AllTrue[
      Table[$priv["identifyIntoHubDraw"]["T"][$hubRule], {8}],
      Length[ruleVariables[#]] === 4 && MemberQ[ruleVariables[#], w] && rhsDegree[#, w] === 4 &&
        Length[#[[1]]] === 1 && Length[DeleteDuplicates @ Flatten[#[[1]]]] === 2 &
    ]
  ],
  True,
  TestID -> "Catalog-IdentifyVariablesIntoHub"
]

(* The catalog-13 example. *)
VerificationTest[
  CanonicalRuleForm @ $priv["addStarMotifDraw"]["T", {2, 2}][{{x, y}} -> {{x, z}, {z, y}}],
  CanonicalRuleForm[{{x, y}} -> {{x, w}, {w, y}, {w, z}, {w, u}}],
  TestID -> "Catalog-AddStarMotifCatalogExample"
]

(* The catalog-14 example: the growth rule gets the cleanup rule
   {{x, y}, {x, z}, {x, u}} -> {{y, z}, {z, u}}. *)
VerificationTest[
  {
    CanonicalRuleForm @ HubPruningMutation[{{x, y}} -> {{x, w}, {w, y}, {w, z}}],
    MemberQ[
      CanonicalRuleForm @ HubPruningMutation[{{x, y}} -> {{x, w}, {w, y}, {w, z}}, <|"ContractionDegree" -> 2|>],
      CanonicalRuleForm[{{x, y}, {x, z}} -> {{y, z}}]
    ]
  },
  {
    CanonicalRuleForm[{{{x, y}} -> {{x, w}, {w, y}, {w, z}}, {{x, y}, {x, z}, {x, u}} -> {{y, z}, {z, u}}}],
    True
  },
  TestID -> "Catalog-ContractionRuleCatalogExample"
]

VerificationTest[
  BlockRandom[
    SeedRandom[12];
    Module[{growth = {{x, y}} -> {{x, w}, {w, y}, {w, z}}, cleanup = {{a, b}, {a, c}, {a, d}} -> {{b, c}, {c, d}}, third = {{p, q}} -> {{q, p}}},
      {
        FailureQ @ $priv["deleteRuleDraw"]["T"][growth],
        MemberQ[{growth, cleanup}, $priv["deleteRuleDraw"]["T"][{growth, cleanup}]],
        Length @ $priv["deleteRuleDraw"]["T"][{growth, cleanup, third}],
        FailureQ @ $priv["deleteRuleDraw"]["T"][{growth, {{s, t}} -> {{s, r}, {r, t}, {r, o}}}]
      }
    ]
  ],
  {True, True, 2, True},
  TestID -> "Catalog-DeleteRuleNeverEmpties"
]

(* AddInverseRule; the catalog-15 example rule is its own inverse up to
   isomorphism, so the operator does not apply to it alone. *)
VerificationTest[
  {
    CanonicalRuleForm @ $priv["addInverseRuleDraw"]["T"][{{x, y}} -> {{x, z}, {z, y}}],
    FailureQ @ $priv["addInverseRuleDraw"]["T"][{{x, y}, {y, z}} -> {{x, w}, {w, z}}],
    FailureQ @ $priv["addInverseRuleDraw"]["T"][{{x, y}} -> {}]
  },
  {CanonicalRuleForm[{{{x, y}} -> {{x, z}, {z, y}}, {{a, b}, {b, c}} -> {{a, c}}}], True, True},
  TestID -> "Catalog-AddInverseRule"
]

(* Slot permutations exist only in the ordered and declared universes. *)
VerificationTest[
  Module[{rule = {{x, y}} -> {{x, z}, {z, y}}, unordered, ordered, permuted},
    unordered = BlockRandom[SeedRandom[13];
      Table[$priv["ProposeCandidate"][parentOf[rule], #, 1, i], {i, 15}] & /@ {"SymmetryConfluence", "TerminalDiversity"}];
    ordered = BlockRandom[SeedRandom[13];
      Table[$priv["ProposeCandidate"][parentOf[rule, "Ordered"], #, 1, i, <|"EdgeSymmetry" -> "Ordered"|>], {i, 30}] & /@
        {"SymmetryConfluence", "TerminalDiversity"}];
    permuted = Select[ordered[[1]], appliedOperators[#] === {"PermuteRHS"} &];
    {
      FailureQ @ $priv["catalogPermutationOperator"]["T", "PermuteRHS", "Right"][rule],
      FreeQ[Map[appliedOperators, unordered, {2}], "PermuteRHS" | "PermuteEdgeOrder"],
      permuted =!= {},
      MemberQ[Map[appliedOperators, ordered[[2]]], {"PermuteEdgeOrder"}],
      AllTrue[permuted,
        Function[p, With[{old = parentOf[rule, "Ordered"]["Rule"], new = p["Provenance"]["ProposedRule"]},
          new[[1]] === old[[1]] && Sort[Sort /@ new[[2]]] === Sort[Sort /@ old[[2]]]]]]
    }
  ],
  {True, True, True, True, True},
  TestID -> "Catalog-PermutationsOnlyInOrderedUniverses"
]


(* ::Section:: *)
(*Strategies*)


VerificationTest[
  BlockRandom[
    SeedRandom[2026];
    AssociationMap[
      Function[name,
        Module[{rule = $catalogExamples[name], results, proposals},
          results = Table[$registry[name]["MutationFunction"][rule], {15}];
          proposals = proposalRule /@ Select[results, !FailureQ[#] &];
          {
            proposals =!= {},
            AllTrue[proposals, $validSpecQ],
            AllTrue[proposals, CanonicalRuleForm[#] =!= CanonicalRuleForm[rule] &],
            AllTrue[Select[results, FailureQ], #[[1]] === "MutationNotApplicable" &]
          }
        ]
      ],
      $catalogNames
    ]
  ],
  AssociationThread[$catalogNames, ConstantArray[{True, True, True, True}, 10]],
  TestID -> "Catalog-StrategiesProposeValidNewRules"
]

VerificationTest[
  AssociationMap[
    Function[name,
      With[{f = $registry[name]["MutationFunction"], rule = $catalogExamples[name]},
        BlockRandom[SeedRandom[99]; CanonicalRuleForm @ proposalRule @ f[rule]] ===
          BlockRandom[SeedRandom[99]; CanonicalRuleForm @ proposalRule @ f[rule]]
      ]
    ],
    $catalogNames
  ],
  AssociationThread[$catalogNames, ConstantArray[True, 10]],
  TestID -> "Catalog-DeterministicUnderSeedRandom"
]

(* Exact-operator provenance through ProposeCandidate: every child names the
   operators that ran, all from the strategy's declared operators. *)
VerificationTest[
  BlockRandom[
    SeedRandom[14];
    AssociationMap[
      Function[name,
        Module[{parent = parentOf[$catalogExamples[name]], proposals},
          proposals = Table[$priv["ProposeCandidate"][parent, name, 1, i], {i, 8}];
          proposals = Select[proposals, !FailureQ[#] &];
          {
            proposals =!= {},
            AllTrue[proposals, appliedOperators[#] =!= {} &],
            AllTrue[proposals, SubsetQ[$registry[name]["Operators"], appliedOperators[#]] &],
            AllTrue[proposals, #["Rule"] =!= parent["Rule"] && #["Strategy"] === name &]
          }
        ]
      ],
      $catalogNames
    ]
  ],
  AssociationThread[$catalogNames, ConstantArray[{True, True, True, True}, 10]],
  TestID -> "Catalog-ProposeCandidateOperatorProvenance"
]

(* A failed operator records nothing: PreserveMotif cannot apply (the LHS
   edge survives), so only AddStableSubstructure is recorded. *)
VerificationTest[
  BlockRandom[
    SeedRandom[15];
    DeleteDuplicates @ Table[
      appliedOperators @ $priv["ProposeCandidate"][parentOf[{{x, y}} -> {{y, x}, {y, z}}], "LocalStability", 1, i],
      {i, 8}
    ]
  ],
  {{"AddStableSubstructure"}},
  TestID -> "Catalog-FailedOperatorsRecordNothing"
]

VerificationTest[
  BlockRandom[
    SeedRandom[16];
    Module[{proposals},
      proposals = Table[
        $priv["ProposeCandidate"][parentOf[{{x, y}} -> {{x, z}, {z, y}}], "HubSeeding", 1, i,
          <|"StrategyOptions" -> <|"HubSeeding" -> <|"StarEdges" -> {3, 3}|>|>|>],
        {i, 12}
      ];
      {
        Lookup[proposals[[1]]["Provenance"]["Parameters"], "StarEdges"],
        AllTrue[
          Select[proposals, appliedOperators[#] === {"AddStarMotif"} &],
          Length[First[#["Provenance"]["AppliedOperators"]]["Details"]["Edges"]] === 3 &
        ]
      }
    ]
  ],
  {{3, 3}, True},
  TestID -> "Catalog-StrategyOptionsReachOperators"
]

VerificationTest[
  {
    FailureQ @ SymmetryConfluenceMutation[42],
    FailureQ @ MeshDensityMutation[{x} -> {y}],
    FailureQ @ HubPruningMutation[{}],
    FailureQ @ CausalInvarianceStyleMutation[{{{x}} -> {{x, x}}, 7}],
    FailureQ @ BoundaryPreservationMutation[{{x, y}} -> {{x, z}, {z, y}}]
  },
  {True, True, True, True, True},
  TestID -> "Catalog-InvalidOrInapplicableInputFails"
]

(* Multiset universes: ordered, and declared with symmetric binary slots. *)
VerificationTest[
  BlockRandom[
    SeedRandom[20];
    Map[
      Function[universe,
        AllTrue[
          $catalogNames,
          Function[name,
            Module[{config, parent, proposals},
              config = universe;
              parent = <|
                "CandidateID" -> "parent",
                "Rule" -> Block[
                  {
                    SamuelFrerichs`StructureAdaptiveEvolution`Private`$EdgeSymmetry = config["EdgeSymmetry"],
                    SamuelFrerichs`StructureAdaptiveEvolution`Private`$SymmetryGroups = Lookup[config, "SymmetryGroups", <||>]
                  },
                  CanonicalRuleForm[$catalogExamples[name]]
                ],
                "InitialState" -> {{1, 2}, {2, 3}}
              |>;
              proposals = Select[Table[$priv["ProposeCandidate"][parent, name, 1, i, config], {i, 6}], !FailureQ[#] &];
              proposals =!= {} &&
                AllTrue[proposals, SubsetQ[$registry[name]["Operators"], appliedOperators[#]] && appliedOperators[#] =!= {} &] &&
                AllTrue[proposals, #["Rule"] =!= parent["Rule"] && $validSpecQ[#["Rule"]] &]
            ]
          ]
        ]
      ],
      {
        <|"EdgeSymmetry" -> "Ordered"|>,
        <|"EdgeSymmetry" -> "Declared", "SymmetryGroups" -> <|2 -> {{1, 2}, {2, 1}}|>|>
      }
    ]
  ],
  {True, True},
  TestID -> "Catalog-MultisetUniverses"
]


(* ::Section:: *)
(*Rule sets*)


$growth = {{x, y}} -> {{x, w}, {w, y}, {w, z}};
$cleanup = {{a, b}, {a, c}, {a, d}} -> {{b, c}, {c, d}};

(* Rule-set aware strategies receive the whole set; DeleteRule never empties
   it. *)
VerificationTest[
  BlockRandom[
    SeedRandom[17];
    Module[{parent = parentOf[{$growth, $cleanup}], proposals},
      proposals = Table[$priv["ProposeCandidate"][parent, "HubPruning", 1, i], {i, 10}];
      {
        AllTrue[proposals, !FailureQ[#] &],
        AllTrue[proposals, MatchQ[#["Rule"], _Rule | {_Rule, _Rule, _Rule}] &],
        AllTrue[proposals, #["Provenance"]["RuleSetMember"] === None &],
        Sort @ Union[appliedOperators /@ proposals]
      }
    ]
  ],
  {True, True, True, Sort[{{"ContractionRule", "AddRule"}, {"DeleteRule"}}]},
  TestID -> "Catalog-HubPruningOnRuleSets"
]

VerificationTest[
  BlockRandom[
    SeedRandom[18];
    Module[{rules = {{{x, y}} -> {{x, z}, {z, y}}, {{a, b}, {b, c}} -> {{a, c}}}, results, members},
      results = Table[CausalInvarianceStyleMutation[rules], {20}];
      members = Select[results, AssociationQ];
      {
        AllTrue[results, !FailureQ[#] &],
        members =!= {},
        AllTrue[members, MemberQ[{1, 2}, #["Details"]["RuleSetMember"]] && Length[#["Rule"]] === 2 &],
        AllTrue[Select[results, ListQ], Length[#] === 3 &],
        AllTrue[proposalRule /@ results, $validSpecQ]
      }
    ]
  ],
  {True, True, True, True, True},
  TestID -> "Catalog-CausalInvarianceStyleOnRuleSets"
]

(* Strategies that are not rule-set aware mutate one member rule. *)
VerificationTest[
  BlockRandom[
    SeedRandom[19];
    Module[{parent = parentOf[{$growth, $cleanup}], proposals},
      proposals = Table[$priv["ProposeCandidate"][parent, "MeshDensity", 1, i], {i, 6}];
      {
        AllTrue[proposals, MatchQ[#["Provenance"]["RuleSetMember"], 1 | 2] &],
        AllTrue[proposals, MatchQ[#["Rule"], {_Rule, _Rule}] &]
      }
    ]
  ],
  {True, True},
  TestID -> "Catalog-MemberMutationOfRuleSets"
]


(* ::Section:: *)
(*One small search per preset*)


(* Each preset with its objectives promoted by the preset's MetricOverrides
   (passed explicitly). Only proposal failures of inapplicable operators are
   expected. MaxEvents stays small: the event-level artifacts (MotifPersistence,
   local lifetimes, update-order runs) only detect the generation cap after
   matching the next step, which is slow on the large states of hub-growing
   mutants. *)
$presetRunLimits = <|"MaxGenerations" -> 3, "MaxEvents" -> 20, "TimeConstraint" -> 5.|>;

presetRun[name_String] := StructureAdaptiveEvolution[
  "Goal" -> name,
  "MetricOverrides" -> $presets[name]["MetricOverrides"],
  "Rule" -> $catalogExamples[name],
  "InitialState" -> {{1, 2}, {2, 3}, {3, 4}},
  "Rounds" -> 1,
  "MutationBudget" -> 3,
  "EvolutionLimits" -> $presetRunLimits,
  "InitialStateDiagnostics" -> None,
  "RandomSeed" -> 17
];

presetRunSummary[name_String] := With[{result = presetRun[name]},
  If[
    !AssociationQ[result],
    result,
    {
      result["Configuration"]["MutationStrategies"],
      AllTrue[result["Candidates"], TrueQ[#["ValidQ"]] &],
      AllTrue[result["ProposalFailures"], #["Failure"][[1]] === "MutationNotApplicable" &],
      AllTrue[Rest[result["Candidates"]], #["Strategy"] === name &],
      SubsetQ[Keys[result["Candidates"][[1]]["Fitness"]], $presets[name]["FitnessMetrics"]]
    }
  ]
];

VerificationTest[presetRunSummary["SymmetryConfluence"], {{"SymmetryConfluence"}, True, True, True, True}, TestID -> "Catalog-PresetRun-SymmetryConfluence"]
VerificationTest[presetRunSummary["BoundaryPreservation"], {{"BoundaryPreservation"}, True, True, True, True}, TestID -> "Catalog-PresetRun-BoundaryPreservation"]
VerificationTest[presetRunSummary["TerminalDiversity"], {{"TerminalDiversity"}, True, True, True, True}, TestID -> "Catalog-PresetRun-TerminalDiversity"]
VerificationTest[presetRunSummary["MeshDensity"], {{"MeshDensity"}, True, True, True, True}, TestID -> "Catalog-PresetRun-MeshDensity"]
VerificationTest[presetRunSummary["Homogenizing"], {{"Homogenizing"}, True, True, True, True}, TestID -> "Catalog-PresetRun-Homogenizing"]
VerificationTest[presetRunSummary["LocalStability"], {{"LocalStability"}, True, True, True, True}, TestID -> "Catalog-PresetRun-LocalStability"]
VerificationTest[presetRunSummary["DegreeBalancing"], {{"DegreeBalancing"}, True, True, True, True}, TestID -> "Catalog-PresetRun-DegreeBalancing"]
VerificationTest[presetRunSummary["HubSeeding"], {{"HubSeeding"}, True, True, True, True}, TestID -> "Catalog-PresetRun-HubSeeding"]
VerificationTest[presetRunSummary["HubPruning"], {{"HubPruning"}, True, True, True, True}, TestID -> "Catalog-PresetRun-HubPruning"]
VerificationTest[presetRunSummary["CausalInvarianceStyle"], {{"CausalInvarianceStyle"}, True, True, True, True}, TestID -> "Catalog-PresetRun-CausalInvarianceStyle"]

(* The plain preset (no overrides) also runs. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Goal" -> "HubPruning",
      "Rule" -> $catalogExamples["HubPruning"],
      "InitialState" -> {{1, 2}, {2, 3}},
      "Rounds" -> 1,
      "MutationBudget" -> 2,
      "EvolutionLimits" -> $presetRunLimits,
      "InitialStateDiagnostics" -> None,
      "RandomSeed" -> 3
    ];
    {AssociationQ[result], result["Configuration"]["Goal"], result["Configuration"]["MutationStrategies"]}
  ],
  {True, "HubPruning", {"HubPruning"}},
  TestID -> "Catalog-PlainPresetRuns"
]


(* GrowthBudget (catalog 1) with its third catalog operator, ConservationMutate.
   GrowthBudgetMutation removes duplicate drawn edges, so "AddedEdgesRange" is
   checked over several seeds: {1, 1} always adds one edge, {2, 2} sometimes two. *)
VerificationTest[
  Module[{private = "SamuelFrerichs`StructureAdaptiveEvolution`Private`", parent, cfg, propose, conserve, edgeCounts},
    parent = <|"CandidateID" -> "p", "Rule" -> CanonicalRuleForm[{{1, 2}} -> {{1, 3}, {3, 2}}], "InitialState" -> {{1, 2}}|>;
    cfg[options_] := ValidateEvolutionConfiguration[
      <|"MutationStrategies" -> {"GrowthBudget"}, "StrategyOptions" -> <|"GrowthBudget" -> options|>|>];
    propose[options_, seed_] := BlockRandom[SeedRandom[seed];
      Symbol[private <> "ProposeCandidate"][parent, "GrowthBudget", 1, 1, cfg[options]]];
    conserve = propose[<|"ConservationProbability" -> 1|>, 3];
    edgeCounts[range_] := Table[
      With[{proposal = propose[<|"ConservationProbability" -> 0, "AddedEdgesRange" -> range|>, seed]},
        If[Lookup[proposal["Provenance"]["AppliedOperators"], "Operator"] === {"AddRHSVariable", "AddRHSEdge"},
          Length[Last[proposal["Provenance"]["AppliedOperators"]]["Details"]["Edges"]],
          $Failed
        ]
      ],
      {seed, 8}
    ];
    {
      MemberQ[Symbol[private <> "$MutationStrategyRegistry"]["GrowthBudget"]["Operators"], "ConservationMutate"],
      Lookup[conserve["Provenance"]["AppliedOperators"], "Operator"],
      Length[Last[conserve["Rule"]]],
      Union[edgeCounts[{1, 1}]],
      Max[edgeCounts[{2, 2}]],
      FailureQ @ ValidateEvolutionConfiguration[<|"StrategyOptions" -> <|"GrowthBudget" -> <|"ConservationProbability" -> 2|>|>|>]
    }
  ],
  {True, {"ConservationMutate"}, 2, {1}, 2, True},
  TestID -> "Catalog-GrowthBudgetConservationMutate"
]


(* Local stability optimizes the persistence of the rule's kept motif;
   hub-seeding follows hub vertices (HubPersistence). *)
VerificationTest[
  {
    Keys @ ValidateEvolutionConfiguration[<|"Goal" -> "HubSeeding"|>]["MetricOverrides"],
    Keys @ ValidateEvolutionConfiguration[<|"Goal" -> "LocalStability"|>]["MetricOverrides"],
    $priv["$MutationStrategyRegistry"]["HubSeeding"]["RequiredMetrics"]
  },
  {
    {"MaxVertexDegree", "HubPersistence"},
    {"LocalComponentLifetimeMean", "LocalComponentLifetimeMax", "MotifPersistence"},
    {"MaxVertexDegree", "HubPersistence"}
  },
  TestID -> "Catalog-PersistenceObjectives"
]
