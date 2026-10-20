PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

(* Immediate genuine halt: the rule never applies. *)
VerificationTest[
  Module[{ev = CanonicalMultiwayEvolution[{{x, y, z}} -> {{x, y}}, {{1, 2}}]},
    {ev["Status"], ev["Generations"], ev["TerminalStates"], ev["CycleDetectedQ"]}
  ],
  {"Halted", {{{{1, 2}}}, {}}, {{{1, 2}}}, False},
  TestID -> "Eval-ImmediateHalt"
]

(* Nontrivial halt after several steps. *)
VerificationTest[
  Module[{ev = CanonicalMultiwayEvolution[
      {{x, y}, {y, z}} -> {{x, z}}, {{1, 2}, {2, 3}, {3, 4}}]},
    {ev["Status"], Last[ev["Generations"]], Length[ev["TerminalStates"]] >= 1}
  ],
  {"Halted", {}, True},
  TestID -> "Eval-DelayedHalt"
]

(* Growth stopped only by the generation cap; frontier states are not
   reported as terminal. *)
VerificationTest[
  Module[{ev = CanonicalMultiwayEvolution[
      {{x, y}} -> {{x, z}, {z, y}}, {{1, 2}}, <|"MaxGenerations" -> 3|>]},
    {ev["Status"], Length[ev["Generations"]], ev["TerminalStates"],
     ev["Frontier"] =!= {}}
  ],
  {"GenerationCap", 4, {}, True},
  TestID -> "Eval-GenerationCapNotTerminal"
]

(* Event cap. *)
VerificationTest[
  CanonicalMultiwayEvolution[
    {{x, y}} -> {{x, z}, {z, y}}, {{1, 2}},
    <|"MaxGenerations" -> 50, "MaxEvents" -> 5|>]["Status"],
  "EventCap",
  TestID -> "Eval-EventCap"
]

(* Timeout. *)
VerificationTest[
  CanonicalMultiwayEvolution[
    {{x, y}} -> {{x, z}, {z, y}}, {{1, 2}},
    <|"MaxGenerations" -> 100, "MaxEvents" -> Infinity,
      "TimeConstraint" -> 1.*^-6|>]["Status"],
  "TimedOut",
  TestID -> "Eval-TimedOut"
]

(* Finite-state cycle that never halts: exhausted frontier is not a halt. *)
VerificationTest[
  Module[{ev = CanonicalMultiwayEvolution[{{x, y}} -> {{y, x}}, {{1, 2}}]},
    {ev["Status"], ev["CycleDetectedQ"], Last[ev["Generations"]] =!= {}}
  ],
  {"CycleDetected", True, True},
  TestID -> "Eval-CycleNotHalted"
]

(* Multiple verified terminal branches. *)
VerificationTest[
  Module[{ev = CanonicalMultiwayEvolution[
      {{x, y}} -> {}, {{1, 2}, {2, 3}, {4, 5}}]},
    {ev["Status"], Length[ev["TerminalStates"]] >= 1,
     AllTrue[ev["TerminalStates"],
       Symbol[$P <> "RuleApplicableQ"][{{x, y}} -> {}, #] === False &]}
  ],
  {"Halted", True, True},
  TestID -> "Eval-TerminalStatesVerified"
]

(* Invalid rule/state input. *)
VerificationTest[
  FailureQ @ CanonicalMultiwayEvolution["junk", {{1, 2}}],
  True,
  TestID -> "Eval-InvalidInputFails"
]

(* HaltedWithinCapQ is True only for genuine halts. *)
VerificationTest[
  Module[{cfg, mk},
    cfg = ValidateEvolutionConfiguration[
      <|"EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>];
    Symbol[$P <> "ClearEvaluationCache"][];
    mk[rule_, state_] := EvaluateCandidate[
      <|"CandidateID" -> "t", "Rule" -> rule, "InitialState" -> state|>, cfg];
    {
      mk[{{1, 2}, {2, 3}} -> {{1, 3}}, {{1, 2}, {2, 3}, {3, 4}}]["Fitness"]["HaltedWithinCapQ"],
      mk[{{1, 2}} -> {{1, 3}, {3, 2}}, {{1, 2}}]["Fitness"]["HaltedWithinCapQ"]
    }
  ],
  {True, False},
  TestID -> "Eval-HaltedWithinCapQOnlyGenuine"
]

(* Cache: one evolution per behavioral key; strategy excluded from the key. *)
VerificationTest[
  Module[{cfg, c1, c2, cacheSize},
    cfg = ValidateEvolutionConfiguration[
      <|"EvolutionLimits" -> <|"MaxGenerations" -> 3|>|>];
    Symbol[$P <> "ClearEvaluationCache"][];
    c1 = EvaluateCandidate[
      <|"CandidateID" -> "a", "Strategy" -> "GrowthBudget",
        "Rule" -> ({{1, 2}} -> {{1, 3}, {3, 2}}), "InitialState" -> {{1, 2}}|>, cfg];
    c2 = EvaluateCandidate[
      <|"CandidateID" -> "b", "Strategy" -> "OverlappingMatch",
        "Rule" -> ({{1, 2}} -> {{1, 3}, {3, 2}}), "InitialState" -> {{1, 2}}|>, cfg];
    cacheSize = Length @ Symbol[$P <> "$EvaluationCache"];
    {cacheSize, c1["Runtime"] === c2["Runtime"],
     c1["EvolutionKey"] === c2["EvolutionKey"],
     c1["Strategy"], c2["Strategy"]}
  ],
  {1, True, True, "GrowthBudget", "OverlappingMatch"},
  TestID -> "Eval-CacheSharedAcrossStrategies"
]

(* Different limits produce different cache keys. *)
VerificationTest[
  Symbol[$P <> "CandidateEvaluationKey"][
    {{1, 2}} -> {{1, 3}, {3, 2}}, {{1, 2}}, <|"MaxGenerations" -> 3|>] =!=
  Symbol[$P <> "CandidateEvaluationKey"][
    {{1, 2}} -> {{1, 3}, {3, 2}}, {{1, 2}}, <|"MaxGenerations" -> 4|>],
  True,
  TestID -> "Eval-KeyIncludesLimits"
]

(* Evaluation context carries the artifacts metrics need. *)
VerificationTest[
  Module[{cfg, cand},
    cfg = ValidateEvolutionConfiguration[
      <|"EvolutionLimits" -> <|"MaxGenerations" -> 2|>|>];
    Symbol[$P <> "ClearEvaluationCache"][];
    cand = EvaluateCandidate[
      <|"CandidateID" -> "ctx", "Rule" -> ({{1, 2}} -> {{1, 3}, {3, 2}}),
        "InitialState" -> {{1, 2}}|>, cfg];
    {GraphQ[cand["StatesGraph"]], ListQ[cand["Generations"]],
     ListQ[cand["States"]], ListQ[cand["FinalStates"]],
     NumericQ[cand["Runtime"]], cand["ValidQ"]}
  ],
  {True, True, True, True, True, True},
  TestID -> "Eval-ContextArtifacts"
]
