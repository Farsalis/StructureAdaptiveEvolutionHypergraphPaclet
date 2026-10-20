PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";

$dominatesQ = Symbol[$P <> "DominatesQ"];
$normalize = Symbol[$P <> "NormalizedObjectiveValue"];
$searchFront = Symbol[$P <> "SearchParetoFront"];
$solutionFront = Symbol[$P <> "SolutionParetoFront"];

$cfg = ValidateEvolutionConfiguration[
  <|"FitnessMetrics" ->
      {"MultiwayStateCount", "HGMaxVerticesCount", "HGMaxEdgeToVertexRatio"},
    "MutationStrategies" -> {"OverlappingMatch"},
    "RatioRange" -> {0., 2.}|>];

(* Candidate factory for hand-built fitness vectors. *)
mkCandidate[id_, states_, vertices_, status_ : "Halted", transitions_ : 2, ratio_ : 1.] := <|
  "CandidateID" -> id,
  "Status" -> status,
  "ValidQ" -> True,
  "TransitionCount" -> transitions,
  "Fitness" -> <|
    "MultiwayStateCount" -> states,
    "HGMaxVerticesCount" -> vertices,
    "HGMaxEdgeToVertexRatio" -> ratio
  |>
|>;

VerificationTest[
  {$dominatesQ[{1, 1}, {2, 2}], $dominatesQ[{1, 2}, {2, 1}],
   $dominatesQ[{1, 1}, {1, 1}], $dominatesQ[{1, 1}, {1, 2}]},
  {True, False, False, True},
  TestID -> "Pareto-DominatesQ"
]

(* Direction transformations into minimization coordinates. *)
VerificationTest[
  {
    $normalize[5, <|"Direction" -> "Maximize"|>, $cfg],
    $normalize[5, <|"Direction" -> "Minimize"|>, $cfg],
    $normalize[5, <|"Direction" -> "Target", "Target" -> 3|>, $cfg],
    $normalize[5, <|"Direction" -> "Range", "Range" -> {0., 2.}|>, $cfg],
    $normalize[1, <|"Direction" -> "Range", "Range" -> {0., 2.}|>, $cfg],
    $normalize[True, <|"Direction" -> "Maximize"|>, $cfg],
    $normalize[False, <|"Direction" -> "Maximize"|>, $cfg]
  },
  {-5, 5, 2, 3., 0., 0, 1},
  TestID -> "Pareto-Normalization"
]

VerificationTest[
  MissingQ @ $normalize["junk", <|"Direction" -> "Maximize"|>, $cfg],
  True,
  TestID -> "Pareto-NonNumericRejected"
]

(* Hand-built 2D front: maximize both metrics. *)
VerificationTest[
  Sort @ Lookup[
    $searchFront[
      {
        mkCandidate["a", 10, 2],
        mkCandidate["b", 5, 5],
        mkCandidate["c", 3, 3],   (* dominated by b *)
        mkCandidate["d", 10, 1]   (* dominated by a *)
      },
      $cfg
    ],
    "CandidateID"
  ],
  {"a", "b"},
  TestID -> "Pareto-2DFront"
]

(* Duplicate objective vectors all survive. *)
VerificationTest[
  Sort @ Lookup[
    $searchFront[
      {mkCandidate["a", 4, 4], mkCandidate["b", 4, 4]},
      $cfg
    ],
    "CandidateID"
  ],
  {"a", "b"},
  TestID -> "Pareto-DuplicateVectorsRetained"
]

(* Invalid or missing metric values never enter the front. *)
VerificationTest[
  Lookup[
    $searchFront[
      {
        Append[mkCandidate["good", 2, 2], "ValidQ" -> True],
        Append[mkCandidate["invalid", 99, 99], "ValidQ" -> False],
        MapAt[KeyDrop["MultiwayStateCount"], mkCandidate["incomplete", 99, 99], "Fitness"]
      },
      $cfg
    ],
    "CandidateID"
  ],
  {"good"},
  TestID -> "Pareto-InvalidValuesExcluded"
]

(* Solution front: verified halt, nontriviality, and constraints. *)
VerificationTest[
  Sort @ Lookup[
    $solutionFront[
      {
        mkCandidate["halted", 5, 5, "Halted"],
        mkCandidate["capped", 50, 50, "GenerationCap"],
        mkCandidate["cycling", 50, 50, "CycleDetected"],
        mkCandidate["trivial", 1, 2, "Halted", 0],
        (* dominates on objectives, but violates the ratio-range constraint *)
        mkCandidate["offRatio", 50, 50, "Halted", 2, 5.]
      },
      $cfg
    ],
    "CandidateID"
  ],
  {"halted"},
  TestID -> "Pareto-SolutionFrontFiltering"
]

(* Empty solution front when nothing verified halts. *)
VerificationTest[
  $solutionFront[{mkCandidate["capped", 5, 5, "GenerationCap"]}, $cfg],
  {},
  TestID -> "Pareto-EmptySolutionFront"
]
