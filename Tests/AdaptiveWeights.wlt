PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

$equalWeights = Symbol[$P <> "EqualStrategyWeights"];
$update = Symbol[$P <> "UpdateStrategyWeights"];

mkRoundCandidate[id_, strategy_, status_ : "Halted"] := <|
  "CandidateID" -> id,
  "Strategy" -> strategy,
  "Status" -> status,
  "ValidQ" -> status =!= "Invalid"
|>;

VerificationTest[
  $equalWeights[{"A", "B", "C", "D"}],
  <|"A" -> 0.25, "B" -> 0.25, "C" -> 0.25, "D" -> 0.25|>,
  TestID -> "Weights-EqualInitialization"
]

(* A successful strategy gains relative allocation; the result stays a
   valid probability distribution. *)
VerificationTest[
  Module[{old, new},
    old = $equalWeights[{"A", "B"}];
    new = $update[
      old,
      <|"A" -> 2, "B" -> 2|>,
      {
        mkRoundCandidate["a1", "A", "Halted"],
        mkRoundCandidate["a2", "A", "Halted"],
        mkRoundCandidate["b1", "B", "GenerationCap"],
        mkRoundCandidate["b2", "B", "Invalid"]
      },
      {mkRoundCandidate["a1", "A"], mkRoundCandidate["b1", "B", "GenerationCap"]},
      {mkRoundCandidate["a1", "A"]}
    ]["Weights"];
    {
      new["A"] > old["A"],
      new["B"] < old["B"],
      AllTrue[Values[new], # >= 0 &],
      Abs[Total[Values[new]] - 1] < 1.*^-12
    }
  ],
  {True, True, True, True},
  TestID -> "Weights-SuccessGainsAllocation"
]

(* All-zero credit retains the previous weights. *)
VerificationTest[
  Module[{old = <|"A" -> 0.7, "B" -> 0.3|>},
    $update[
      old,
      <|"A" -> 2, "B" -> 1|>,
      {
        mkRoundCandidate["a1", "A", "Invalid"],
        mkRoundCandidate["b1", "B", "Invalid"]
      },
      {}, {}
    ]["Weights"] === old
  ],
  True,
  TestID -> "Weights-ZeroCreditRetains"
]

(* No trials at all retains the previous weights. *)
VerificationTest[
  Module[{old = <|"A" -> 0.6, "B" -> 0.4|>},
    $update[old, <|"A" -> 0, "B" -> 0|>, {}, {}, {}]["Weights"] === old
  ],
  True,
  TestID -> "Weights-NoTrialsRetains"
]

(* Untried strategies produce no division-by-zero and keep a positive floor. *)
VerificationTest[
  Module[{new},
    new = $update[
      $equalWeights[{"A", "B", "C"}],
      <|"A" -> 3, "B" -> 0, "C" -> 0|>,
      {mkRoundCandidate["a1", "A", "Halted"]},
      {mkRoundCandidate["a1", "A"]},
      {mkRoundCandidate["a1", "A"]}
    ]["Weights"];
    {AllTrue[Values[new], # > 0 &], Abs[Total[Values[new]] - 1] < 1.*^-12}
  ],
  {True, True},
  TestID -> "Weights-UntriedStrategiesSafe"
]

(* Weight history is logged per round and weights stay valid across rounds. *)
VerificationTest[
  Module[{result},
    result = StructureAdaptiveEvolution[
      "Rule" -> ({{1, 2}} -> {{1, 3}, {3, 2}}),
      "InitialState" -> {{1, 2}},
      "Rounds" -> 2,
      "MutationBudget" -> 4,
      "MutationStrategies" -> {"GrowthBudget", "RuntimeThrottling"},
      "EvolutionLimits" ->
        <|"MaxGenerations" -> 3, "MaxEvents" -> 100, "TimeConstraint" -> 10.|>,
      "RandomSeed" -> 5
    ];
    {
      Length[result["StrategyWeightHistory"]],
      AllTrue[
        result["StrategyWeightHistory"],
        AllTrue[Values[#], NonNegative] && Abs[Total[Values[#]] - 1] < 1.*^-9 &
      ],
      Count[result["RunLog"], KeyValuePattern["Event" -> "Round"]]
    }
  ],
  {3, True, 2},
  TestID -> "Weights-HistoryLoggedPerRound"
]
