PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

(* Evaluate an expression inside the ordered universe. *)
$inOrdered = ToExpression[
  "Function[expr, Block[{" <> $P <> "$EdgeSymmetry = \"Ordered\"}, expr], HoldAll]"];

$fastLimits = <|"MaxGenerations" -> 3, "MaxEvents" -> 150, "TimeConstraint" -> 15.|>;

(* 1. Ordered canonicalization distinguishes positional structure. The
   unordered control uses the path-versus-fan pair, which unordered
   semantics genuinely collapses. *)
VerificationTest[
  {
    CanonicalStateForm[{{1, 1, 2}}, "Ordered"] =!= CanonicalStateForm[{{1, 2, 2}}, "Ordered"],
    CanonicalStateForm[{{1, 2}, {2, 3}}, "Ordered"] =!= CanonicalStateForm[{{1, 2}, {3, 2}}, "Ordered"],
    CanonicalStateForm[{{1, 2}, {2, 3}}, "Unordered"] === CanonicalStateForm[{{1, 2}, {3, 2}}, "Unordered"]
  },
  {True, True, True},
  TestID -> "Ordered-CanonDistinguishesPositions"
]

(* 2. Global vertex relabelings are still quotiented in the ordered universe. *)
VerificationTest[
  {
    CanonicalStateForm[{{7, 8}, {8, 9}}, "Ordered"] ===
      CanonicalStateForm[{{101, 202}, {202, 303}}, "Ordered"],
    CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}}, "Ordered"] ===
      CanonicalRuleForm[{{a, b}} -> {{a, c}, {c, b}}, "Ordered"],
    CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}}, "Ordered"] =!=
      CanonicalRuleForm[{{x, y}} -> {{x, z}, {y, z}}, "Ordered"]
  },
  {True, True, True},
  TestID -> "Ordered-RelabelEquivalence"
]

(* 3. Multiset semantics: exact duplicates are semantic, collection order is
   not, and canonicalization is idempotent. *)
VerificationTest[
  Module[{duplicated = CanonicalStateForm[{{1, 2}, {1, 2}}, "Ordered"]},
    {
      Length[duplicated],
      duplicated =!= CanonicalStateForm[{{1, 2}}, "Ordered"],
      Length @ CanonicalStateForm[{{1, 2}, {1, 2}}, "Unordered"],
      CanonicalStateForm[{{1, 2}, {3, 3}}, "Ordered"] ===
        CanonicalStateForm[{{3, 3}, {1, 2}}, "Ordered"],
      CanonicalStateForm[CanonicalStateForm[{{1, 2}, {3, 2}}, "Ordered"], "Ordered"] ===
        CanonicalStateForm[{{1, 2}, {3, 2}}, "Ordered"]
    }
  ],
  {2, True, 1, True, True},
  TestID -> "Ordered-MultisetSemantics"
]

(* 4. Permutation conservation contract: edge counts, arities, and the
   vertex-occurrence multiset are unchanged; only the selected edge moves. *)
VerificationTest[
  SeedRandom[31];
  Module[{rule = {{x, y}, {y, z}} -> {{z, y, x}}, out, mutated, details, restored},
    out = $inOrdered[OrderedEdgePermutationMutation[rule]];
    mutated = out["Rule"];
    details = out["Details"];
    restored = If[
      details["Side"] === "Left",
      ReplacePart[mutated[[1]], details["EdgeIndex"] -> details["OldEdge"]] -> mutated[[2]],
      mutated[[1]] -> ReplacePart[mutated[[2]], details["EdgeIndex"] -> details["OldEdge"]]
    ];
    {
      AssociationQ[out],
      Length[mutated[[1]]] === 2 && Length[mutated[[2]]] === 1,
      (Length /@ mutated[[1]]) === {2, 2} && (Length /@ mutated[[2]]) === {3},
      Sort @ Flatten[{mutated[[1]], mutated[[2]]}] === Sort @ Flatten[{rule[[1]], rule[[2]]}],
      details["NewEdge"] === details["OldEdge"][[details["Permutation"]]],
      details["NewEdge"] =!= details["OldEdge"],
      restored === rule
    }
  ],
  {True, True, True, True, True, True, True},
  TestID -> "Ordered-PermutationConservation"
]

(* 5. Nonidentity requirement: arity-1 edges and all-identical-symbol edges
   cannot produce a candidate. *)
VerificationTest[
  $inOrdered[{
    FailureQ @ OrderedEdgePermutationMutation[{{x}} -> {{x}}],
    FailureQ @ OrderedEdgePermutationMutation[{{x, x}} -> {{x, x}}]
  }],
  {True, True},
  TestID -> "Ordered-PermutationRequiresPermutableEdge"
]

(* 6. Side targeting mutates only the requested side. *)
VerificationTest[
  SeedRandom[32];
  Module[{rule = {{x, y}, {y, z}} -> {{z, y, x}}, left, right},
    left = $inOrdered[OrderedEdgePermutationMutation[rule, "Left"]];
    right = $inOrdered[OrderedEdgePermutationMutation[rule, "Right"]];
    {
      left["Details"]["Side"], left["Rule"][[2]] === rule[[2]],
      right["Details"]["Side"], right["Rule"][[1]] === rule[[1]]
    }
  ],
  {"Left", True, "Right", True},
  TestID -> "Ordered-PermutationSideTargeting"
]

(* 7. Canonical no-ops are rejected: permuting the only edge of a
   single-edge LHS is a global relabeling in disguise. *)
VerificationTest[
  SeedRandom[33];
  FailureQ @ $inOrdered[OrderedEdgePermutationMutation[{{x, y}} -> {}]],
  True,
  TestID -> "Ordered-PermutationCanonicalNoOpRejected"
]

(* 8. Gating: the operator and the configuration both reject unordered use. *)
VerificationTest[
  {
    FailureQ @ OrderedEdgePermutationMutation[{{x, y}, {y, z}} -> {{z, y, x}}],
    FailureQ @ ValidateEvolutionConfiguration[
      <|"MutationStrategies" -> {"OrderedEdgePermutation"}|>],
    AssociationQ @ ValidateEvolutionConfiguration[
      <|"MutationStrategies" -> {"OrderedEdgePermutation"},
        "EdgeSymmetry" -> "Ordered"|>],
    FailureQ @ ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Sideways"|>]
  },
  {True, True, True, True},
  TestID -> "Ordered-GatingAndValidation"
]

(* Automatic strategy resolution follows the universe. *)
VerificationTest[
  {
    ValidateEvolutionConfiguration[<||>]["EdgeSymmetry"],
    MemberQ[ValidateEvolutionConfiguration[<||>]["MutationStrategies"],
      "OrderedEdgePermutation"],
    MemberQ[
      ValidateEvolutionConfiguration[<|"EdgeSymmetry" -> "Ordered"|>]["MutationStrategies"],
      "OrderedEdgePermutation"],
    MemberQ[ValidateEvolutionConfiguration[<||>]["UnavailableRecommendedStrategies"],
      "OrderedEdgePermutation"]
  },
  {"Unordered", False, True, True},
  TestID -> "Ordered-AutomaticStrategyResolutionByMode"
]

(* 9. Determinism: a fixed seed reproduces the candidate and its provenance. *)
VerificationTest[
  Module[{rule = {{x, y}, {y, z}} -> {{z, y, x}}, first, second},
    SeedRandom[34]; first = $inOrdered[OrderedEdgePermutationMutation[rule]];
    SeedRandom[34]; second = $inOrdered[OrderedEdgePermutationMutation[rule]];
    first === second
  ],
  True,
  TestID -> "Ordered-PermutationDeterministic"
]

(* 10. The behavior cache separates the two universes. *)
VerificationTest[
  Module[{key = Symbol[$P <> "CandidateEvaluationKey"]},
    $inOrdered[key[{{1, 2}} -> {{1, 3}, {3, 2}}, {{1, 2}}, <|"MaxGenerations" -> 3|>]] =!=
      key[{{1, 2}} -> {{1, 3}, {3, 2}}, {{1, 2}}, <|"MaxGenerations" -> 3|>]
  ],
  True,
  TestID -> "Ordered-CacheKeySeparatesUniverses"
]

(* 11. Dispatch smoke test: the operator runs through the normal pipeline,
   deterministically, with full provenance details. *)
VerificationTest[
  Module[{run, first, second, permutationCandidates},
    run[] := StructureAdaptiveEvolution[
      "EdgeSymmetry" -> "Ordered",
      "Rule" -> ({{x, y}, {y, z}} -> {{x, z, y}}),
      "InitialState" -> {{1, 2}, {2, 3}, {3, 1}},
      "MutationStrategies" -> {"OrderedEdgePermutation", "GrowthBudget"},
      "Rounds" -> 2,
      "MutationBudget" -> 6,
      "EvolutionLimits" -> $fastLimits,
      "RandomSeed" -> 41
    ];
    first = run[];
    second = run[];
    permutationCandidates = Select[
      Rest @ first["Candidates"],
      #["Strategy"] === "OrderedEdgePermutation" &
    ];
    {
      AssociationQ[first],
      first["Configuration"]["EdgeSymmetry"],
      First[first["RunLog"]]["StateEquivalence"],
      Lookup[first["Candidates"], "CandidateID"] ===
        Lookup[second["Candidates"], "CandidateID"],
      permutationCandidates =!= {},
      AllTrue[
        permutationCandidates,
        MatchQ[
          #["Provenance"]["Details"],
          KeyValuePattern[{
            "Side" -> "Left" | "Right",
            "EdgeIndex" -> _Integer,
            "OldEdge" -> _List,
            "NewEdge" -> _List,
            "Permutation" -> {__Integer}
          }]
        ] &
      ]
    }
  ],
  {True, "Ordered", "CanonicalHypergraph-OrderedMultiset", True, True, True},
  TestID -> "Ordered-DispatchSmokeTest"
]

(* 12. Ordered evaluation keeps multiedge initial states; unordered collapses
   them. *)
VerificationTest[
  Module[{orderedConfig, unorderedConfig, evaluate, orderedCandidate, unorderedCandidate},
    orderedConfig = ValidateEvolutionConfiguration[
      <|"EdgeSymmetry" -> "Ordered", "EvolutionLimits" -> <|"MaxGenerations" -> 2|>|>];
    unorderedConfig = ValidateEvolutionConfiguration[
      <|"EvolutionLimits" -> <|"MaxGenerations" -> 2|>|>];
    Symbol[$P <> "ClearEvaluationCache"][];
    evaluate[config_] := EvaluateCandidate[
      <|"CandidateID" -> "multiedge",
        "Rule" -> ({{1, 2}} -> {{1, 3}, {3, 2}}),
        "InitialState" -> {{1, 2}, {1, 2}}|>,
      config];
    orderedCandidate = evaluate[orderedConfig];
    unorderedCandidate = evaluate[unorderedConfig];
    {
      Length @ First @ First @ orderedCandidate["Generations"],
      Length @ First @ First @ unorderedCandidate["Generations"],
      orderedCandidate["ValidQ"],
      unorderedCandidate["ValidQ"],
      orderedCandidate["EvolutionKey"] =!= unorderedCandidate["EvolutionKey"]
    }
  ],
  {2, 1, True, True, True},
  TestID -> "Ordered-MultiedgeEvaluation"
]
