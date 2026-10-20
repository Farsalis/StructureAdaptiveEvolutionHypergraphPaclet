PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

$vdConfig = ValidateEvolutionConfiguration[
  <|"RewriteSemantics" -> "VertexDeletion",
    "EvolutionLimits" -> <|"MaxGenerations" -> 4|>|>];
$etConfig = ValidateEvolutionConfiguration[
  <|"EvolutionLimits" -> <|"MaxGenerations" -> 4|>|>];

(* 1. Configuration surface: edge-token is the default, vertex deletion is
   opt-in, anything else fails. *)
VerificationTest[
  {
    ValidateEvolutionConfiguration[<||>]["RewriteSemantics"],
    $vdConfig["RewriteSemantics"],
    FailureQ @ ValidateEvolutionConfiguration[<|"RewriteSemantics" -> "Bogus"|>]
  },
  {"EdgeToken", "VertexDeletion", True},
  TestID -> "Semantics-ConfigurationSurface"
]

(* 2. The two semantics produce different evolutions for a vertex-dropping
   rule: under opt-in vertex deletion the bystander edge loses a vertex and
   the system starves early; under the default edge-token semantics it
   stays intact and evolution continues one generation longer. *)
VerificationTest[
  Module[{evaluate, vd, et},
    Symbol[$P <> "ClearEvaluationCache"][];
    evaluate[config_] := EvaluateCandidate[
      <|"CandidateID" -> "semantics",
        "Rule" -> ({{x, y}} -> {}),
        "InitialState" -> {{1, 2}, {2, 3}}|>,
      config];
    vd = evaluate[$vdConfig];
    et = evaluate[$etConfig];
    {
      vd["Status"], et["Status"],
      Max[0, Length[DeleteCases[vd["Generations"], {}]] - 1],
      Max[0, Length[DeleteCases[et["Generations"], {}]] - 1],
      (* vertex deletion mutates the untouched edge down to arity 1 *)
      AnyTrue[vd["States"], MemberQ[#, _List?(Length[#] < 2 &)] &],
      (* edge-token keeps every edge at its original arity *)
      AllTrue[et["States"], AllTrue[#, Length[#] >= 2 &] &],
      (* the behavior cache separates the two semantics *)
      vd["EvolutionKey"] =!= et["EvolutionKey"]
    }
  ],
  {"Halted", "Halted", 1, 2, True, True, True},
  TestID -> "Semantics-EdgeTokenPreservesBystanderEdges"
]

(* 3. Edge-token semantics composes with the ordered universe. *)
VerificationTest[
  Module[{config, candidate},
    config = ValidateEvolutionConfiguration[
      <|"RewriteSemantics" -> "EdgeToken", "EdgeSymmetry" -> "Ordered",
        "EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>];
    Symbol[$P <> "ClearEvaluationCache"][];
    candidate = EvaluateCandidate[
      <|"CandidateID" -> "orderedEdgeToken",
        "Rule" -> ({{1, 2}} -> {{2, 1}, {1, 3}}),
        "InitialState" -> {{1, 2}, {2, 3}}|>,
      config];
    {
      candidate["ValidQ"],
      AllTrue[candidate["States"], AllTrue[#, Length[#] >= 2 &] &]
    }
  ],
  {True, True},
  TestID -> "Semantics-EdgeTokenComposesWithOrdered"
]

(* 4. Full pipeline under edge-token semantics: deterministic, provenance
   recorded in the run log, default behavior untouched elsewhere. *)
VerificationTest[
  Module[{run, first, second},
    run[] := StructureAdaptiveEvolution[
      "RewriteSemantics" -> "EdgeToken",
      "Rule" -> ({{x, y}, {y, z}} -> {{x, z}}),
      "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
      "MutationStrategies" -> {"GrowthBudget", "GrowThenConstrain"},
      "Rounds" -> 1,
      "MutationBudget" -> 4,
      "EvolutionLimits" -> <|"MaxGenerations" -> 3, "MaxEvents" -> 150, "TimeConstraint" -> 15.|>,
      "RandomSeed" -> 61
    ];
    first = run[];
    second = run[];
    {
      AssociationQ[first],
      First[first["RunLog"]]["RewriteSemantics"],
      Lookup[first["Candidates"], "CandidateID"] ===
        Lookup[second["Candidates"], "CandidateID"],
      Length[first["SearchParetoFront"]] >= 1
    }
  ],
  {True, "EdgeToken", True, True},
  TestID -> "Semantics-EdgeTokenPipelineDeterministic"
]
