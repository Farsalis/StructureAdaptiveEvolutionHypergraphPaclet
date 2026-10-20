PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

VerificationTest[
  hypergraphStateQ[{{1, 2}, {2, 3}}] && hypergraphStateQ[{}] && !hypergraphStateQ[{{1, {2}}}] && !hypergraphStateQ["x"],
  True,
  TestID -> "Repr-hypergraphStateQ"
]

VerificationTest[
  CanonicalStateForm[{{2, 1}, {3, 2}}],
  CanonicalStateForm[{{10, 20}, {20, 30}}],
  TestID -> "Canon-RelabeledStatesIdentical"
]

VerificationTest[
  CanonicalStateForm[{{1, 2}, {2, 3}}],
  CanonicalStateForm[{{3, 2}, {2, 1}}],
  TestID -> "Canon-ReorderedUnorderedEdgesIdentical"
]

VerificationTest[
  CanonicalStateForm[{{1, 2}, {2, 3}}] =!= CanonicalStateForm[{{1, 2}, {3, 4}}],
  True,
  TestID -> "Canon-NonIsomorphicStatesDiffer"
]

VerificationTest[
  CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}}],
  CanonicalRuleForm[{{a, b}} -> {{a, c}, {c, b}}],
  TestID -> "Canon-RenamedRulesIdentical"
]

VerificationTest[
  CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}}] =!=
    CanonicalRuleForm[{{x, y}} -> {{x, z}}],
  True,
  TestID -> "Canon-DifferentRulesDiffer"
]

(* Duplicate hyperedges are removed; self-loops are preserved. *)
VerificationTest[
  CanonicalStateForm[{{1, 2}, {2, 1}, {1, 1}}],
  CanonicalStateForm[{{1, 2}, {1, 1}}],
  TestID -> "Canon-DuplicateEdgesRemoved"
]

VerificationTest[
  MemberQ[CanonicalStateForm[{{1, 1}, {1, 2}}], {v_, v_}],
  True,
  TestID -> "Canon-SelfLoopPreserved"
]

VerificationTest[
  Symbol[$P <> "SeedIDFromCanonicalForms"][
    CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}}],
    CanonicalStateForm[{{1, 2}}]
  ],
  Symbol[$P <> "SeedIDFromCanonicalForms"][
    CanonicalRuleForm[{{p, q}} -> {{p, r}, {r, q}}],
    CanonicalStateForm[{{7, 9}}]
  ],
  TestID -> "Canon-SeedIDStableUnderRelabeling"
]

VerificationTest[
  Symbol[$P <> "SeedIDFromCanonicalForms"][
    CanonicalRuleForm[{{x, y}} -> {{x, z}, {z, y}}],
    CanonicalStateForm[{{1, 2}}]
  ] =!= Symbol[$P <> "SeedIDFromCanonicalForms"][
    CanonicalRuleForm[{{x, y}} -> {{x, z}}],
    CanonicalStateForm[{{1, 2}}]
  ],
  True,
  TestID -> "Canon-SeedIDChangesWithRule"
]

VerificationTest[
  Module[{seedA, seedB, cfgA, cfgB},
    cfgA = ValidateEvolutionConfiguration[
      <|"Rule" -> ({{x, y}} -> {{x, z}, {z, y}}), "InitialState" -> {{1, 2}}|>];
    cfgB = ValidateEvolutionConfiguration[
      <|"Rule" -> ({{a, b}} -> {{a, c}, {c, b}}), "InitialState" -> {{5, 8}}|>];
    seedA = ResolveAndCanonicalizeSeed[cfgA];
    seedB = ResolveAndCanonicalizeSeed[cfgB];
    {seedA["SeedID"] === seedB["SeedID"],
     seedA["Rule"] === seedB["Rule"],
     seedA["InitialState"] === seedB["InitialState"],
     seedA["InitiallyApplicableQ"]}
  ],
  {True, True, True, True},
  TestID -> "Seed-RelabeledSeedsIdentical"
]

VerificationTest[
  Module[{seed},
    seed = ResolveAndCanonicalizeSeed[
      ValidateEvolutionConfiguration[
        <|"Rule" -> ({{x, y}} -> {{x, z}, {z, y}}), "InitialState" -> Automatic|>]];
    {seed["Source"], seed["InitiallyApplicableQ"],
     seed["InitialState"] === First[seed["Rule"]]}
  ],
  {"RuleInput", True, True},
  TestID -> "Seed-AutomaticStateUsesLHS"
]

VerificationTest[
  FailureQ @ ResolveAndCanonicalizeSeed["not a config"],
  True,
  TestID -> "Seed-InvalidConfigurationFails"
]

VerificationTest[
  Module[{seed},
    seed = ResolveAndCanonicalizeSeed[
      ValidateEvolutionConfiguration[
        <|"Rule" -> ({{x, y, z}} -> {{x, y}}), "InitialState" -> {{1, 2}}|>]];
    seed["InitiallyApplicableQ"]
  ],
  False,
  TestID -> "Seed-InapplicabilityRecorded"
]
