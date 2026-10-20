(* Experimental-protocol layer: lossless export/import with a run manifest,
   the experiment store and cross-run reuse, Wilson intervals, multi-seed
   replication, budget-matched baselines, robustness and cap sensitivity,
   discovery reports with claim discipline and the verified seed corpus. *)

PacletDirectoryLoad[ParentDirectory[DirectoryName[$TestFileName]]];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];

$P = "SamuelFrerichs`StructureAdaptiveEvolution`Private`";
$priv[name_String] := Symbol[$P <> name];

$xtRoot = FileNameJoin[{$TemporaryDirectory, "SAE-ExperimentsTests-" <> CreateUUID[]}];
CreateDirectory[$xtRoot];

$xtContract = {{x, y}, {y, z}} -> {{x, z}};
$xtCycle4 = {{1, 2}, {2, 3}, {3, 4}, {4, 1}};
$xtLimits = <|"MaxGenerations" -> 5, "MaxEvents" -> 200, "TimeConstraint" -> 20.|>;

(* Seed 11 gives a Halted solution, CycleDetected candidates with witnesses
   and a Missing longest derivation. *)
$xtOptions = {
  "Rule" -> $xtContract,
  "InitialState" -> $xtCycle4,
  "Rounds" -> 1,
  "MutationBudget" -> 4,
  "EvolutionLimits" -> $xtLimits,
  "InitialStateDiagnostics" -> None,
  "RandomSeed" -> 11
};

$xtCustom = <|
  "StateCountCopy" -> <|"Function" -> Function[Length[#["States"]]], "Direction" -> "Maximize", "Stage" -> "Diagnostic"|>
|>;

$xtResult = StructureAdaptiveEvolution[
  Sequence @@ DeleteCases[$xtOptions, "InitialStateDiagnostics" -> _],
  "InitialStateDiagnostics" -> "Finalists",
  "CustomFitnessMetrics" -> $xtCustom
];

$xtExportDirectory = FileNameJoin[{$xtRoot, "export"}];
$xtExported = ExportEvolutionResult[$xtResult, $xtExportDirectory];
$xtManifest = Import[FileNameJoin[{$xtExportDirectory, "manifest.json"}], "RawJSON"];

$xtSolutionID = First[Lookup[$xtResult["SolutionParetoFront"], "CandidateID"]];
$xtCycleID = SelectFirst[$xtResult["Candidates"], #["Status"] === "CycleDetected" &]["CandidateID"];

(* A six-edge path contracts to one edge in six generations: under
   MaxGenerations 3 the seed is capped, under twice the limits it halts. *)
$xtCapped = StructureAdaptiveEvolution[
  "Rule" -> $xtContract,
  "InitialState" -> Table[{i, i + 1}, {i, 6}],
  "Rounds" -> 1,
  "MutationBudget" -> 2,
  "EvolutionLimits" -> <|"MaxGenerations" -> 3, "MaxEvents" -> 500, "TimeConstraint" -> 20.|>,
  "InitialStateDiagnostics" -> None,
  "RandomSeed" -> 5
];
$xtCappedID = $xtCapped["Baseline"]["CandidateID"];

$xtDiscoveryFields = {
  "Candidate ID / evaluation ID", "Canonical rule", "Initial state", "Edge symmetry",
  "Rewrite semantics", "Backend and versions", "Limits and random seed",
  "Status and cycle evidence", "Constraint satisfaction", "State / transition / raw-event counts",
  "Lifetime (longest derivation and BFS depth) and maximum frontier",
  "Maximum state size and density", "Terminal-state summary", "Runtime",
  "Search-front / solution-front membership", "Initial-state robustness summary",
  "Mutation lineage", "Interpretation with evidence level"
};


(* ::Section:: *)
(*Wilson intervals*)


VerificationTest[
  Module[{none = WilsonInterval[0, 10], half = WilsonInterval[5, 10], all = WilsonInterval[10, 10]},
    {
      Abs[none[[1]]] < 10^-12, Abs[none[[2]] - 0.2775328] < 10^-6,
      Abs[half[[1]] - 0.2365931] < 10^-6, Abs[half[[2]] - 0.7634069] < 10^-6,
      Abs[all[[1]] - 0.7224672] < 10^-6, all[[2]] == 1.,
      WilsonInterval[0, 0]
    }
  ],
  {True, True, True, True, True, True, {0., 1.}},
  TestID -> "Experiments-WilsonKnownValues"
]

VerificationTest[
  {
    With[{w95 = WilsonInterval[5, 10], w99 = WilsonInterval[5, 10, 0.99]}, w99[[1]] < w95[[1]] && w99[[2]] > w95[[2]]],
    FailureQ[WilsonInterval[3, 2]],
    FailureQ[WilsonInterval[-1, 5]],
    FailureQ[WilsonInterval[1, 5, 1.5]]
  },
  {True, True, True, True},
  TestID -> "Experiments-WilsonLevelAndValidation"
]


(* ::Section:: *)
(*Export and import*)


VerificationTest[
  Module[{imported = ImportEvolutionResult[$xtExportDirectory]},
    {
      Sort[FileNameTake /@ $xtExported["Files"]],
      AllTrue[$xtExported["Files"], FileExistsQ],
      $xtExported["WXFHash"] === FileHash[FileNameJoin[{$xtExportDirectory, "result.wxf"}], "SHA256", All, "HexString"],
      imported === $xtResult,
      BinarySerialize[imported] === BinarySerialize[$xtResult]
    }
  ],
  {{"manifest.json", "result.wxf", "summary.md"}, True, True, True, True},
  TestID -> "Experiments-ExportImportLossless"
]

VerificationTest[
  Module[{m = $xtManifest, config = $xtResult["Configuration"], rows},
    rows = m["Candidates"];
    {
      m["RunID"] === $xtResult["RunID"],
      m["WXFSHA256"] === $xtExported["WXFHash"] === m["Files"]["result.wxf"]["SHA256"],
      MatchQ[m["PacletGitCommit"], Null | _String?(StringMatchQ[#, RegularExpression["[0-9a-f]{40}"]] &)] &&
        MemberQ[{True, False, Null}, m["PacletGitDirty"]] && MemberQ[{True, False, Null}, m["PacletGitRootIsPacletRoot"]],
      m["Provenance"]["EvaluatorVersion"] === $xtResult["Provenance"]["EvaluatorVersion"],
      m["Universe"] === <|
        "EdgeSymmetry" -> "Unordered", "SymmetryGroups" -> <||>, "RewriteSemantics" -> "EdgeToken",
        "CanonicalForm" -> "Exact", "StateEquivalence" -> $xtResult["Provenance"]["StateEquivalence"]
      |>,
      m["EvolutionLimits"],
      m["RandomSeed"],
      m["Seed"]["OriginalRule"],
      m["Seed"]["CanonicalRule"] === ToString[$xtResult["Seed"]["CanonicalRule"], InputForm],
      m["Seed"]["CanonicalInitialState"] === $xtResult["Seed"]["CanonicalInitialState"],
      Lookup[m["Strategies"]["Weights"], "Strategy"] === config["MutationStrategies"],
      Lookup[m["MetricSpecifications"], "Name"] === config["FitnessMetrics"],
      StringQ[m["Configuration"]["CustomFitnessMetrics"]["StateCountCopy"]["Function"]],
      Length[rows] === Length[$xtResult["Candidates"]],
      Lookup[rows, "CandidateID"] === Lookup[$xtResult["Candidates"], "CandidateID"],
      AllTrue[rows,
        SubsetQ[Keys[#], {
          "CandidateID", "EvaluationID", "EvolutionKey", "ParentID", "Strategy", "AppliedOperators",
          "CanonicalRule", "Status", "CycleWitnessPresent", "LimitsReached", "Fitness",
          "FitnessMissingReasons", "Runtime", "FrontMembership"
        }] &],
      Lookup[rows, "FrontMembership"] === Values[$xtResult["FrontMembership"]],
      Lookup[m["Solutions"], "CandidateID"] ===
        Lookup[Select[$xtResult["Candidates"], $priv["solutionEligibleQ"][#, config] &], "CandidateID"],
      AllTrue[m["Solutions"], Length[#["VerifiedTerminalStates"]] === #["TerminalStateCount"] && #["TerminalStateCount"] >= 1 &],
      m["InitialStateDiagnostics"]["Requested"]
    }
  ],
  {
    True, True, True, True, True,
    <|"MaxGenerations" -> 5, "MaxEvents" -> 200, "MaxStates" -> "Infinity", "TimeConstraint" -> 20.|>,
    11, "{{x, y}, {y, z}} -> {{x, z}}",
    True, True, True, True, True, True, True, True, True, True, True, True
  },
  TestID -> "Experiments-ManifestContents"
]

VerificationTest[
  Module[{row},
    row = SelectFirst[$xtManifest["Candidates"], #["CandidateID"] === $xtCycleID &];
    {
      row["Status"],
      row["CycleWitnessPresent"],
      row["Fitness"]["MultiwayLongestDerivation"],
      row["FitnessMissingReasons"],
      row["CanonicalRule"] === ToString[
        SelectFirst[$xtResult["Candidates"], #["CandidateID"] === $xtCycleID &]["Rule"], InputForm]
    }
  ],
  {"CycleDetected", True, Null, <|"MultiwayLongestDerivation" -> "CyclicStatesGraph"|>, True},
  TestID -> "Experiments-ManifestMissingAsNullWithReason"
]

VerificationTest[
  Module[{summary = Import[FileNameJoin[{$xtExportDirectory, "summary.md"}], "Text"]},
    StringContainsQ[summary, #] & /@ {
      $xtResult["RunID"],
      $xtResult["Provenance"]["StateEquivalence"],
      "verified to halt under this finite reachable exploration",
      "not resolved within the stated limits",
      $xtExported["WXFHash"]
    }
  ],
  {True, True, True, True, True},
  TestID -> "Experiments-SummaryMarkdown"
]

VerificationTest[
  Module[{copy = FileNameJoin[{$xtRoot, "tampered"}], stream, tampered, missing},
    CopyDirectory[$xtExportDirectory, copy];
    stream = OpenAppend[FileNameJoin[{copy, "result.wxf"}], BinaryFormat -> True];
    BinaryWrite[stream, {0}];
    Close[stream];
    tampered = ImportEvolutionResult[copy];
    DeleteFile[FileNameJoin[{copy, "manifest.json"}]];
    missing = ImportEvolutionResult[copy];
    {
      FailureQ[tampered], tampered[[1]],
      FailureQ[missing], missing[[1]],
      ImportEvolutionResult[FileNameJoin[{$xtRoot, "no-such-run"}]][[1]],
      ExportEvolutionResult[<|"RunID" -> "x"|>, FileNameJoin[{$xtRoot, "never"}]][[1]],
      DirectoryQ[FileNameJoin[{$xtRoot, "never"}]]
    }
  ],
  {True, "HashMismatch", True, "MissingRunFile", "MissingRunDirectory", "NotAnEvolutionResult", False},
  TestID -> "Experiments-ImportDetectsTampering"
]


(* ::Section:: *)
(*Experiment store*)


$xtStore = FileNameJoin[{$xtRoot, "store"}];

VerificationTest[
  Module[{added, runs, all, halted, ranged, solutions},
    added = ExperimentStoreAdd[$xtStore, $xtResult];
    runs = Normal @ ExperimentStoreRuns[$xtStore];
    all = Normal @ ExperimentStoreQuery[$xtStore];
    halted = Normal @ ExperimentStoreQuery[$xtStore, <|"Status" -> "Halted"|>];
    ranged = Normal @ ExperimentStoreQuery[$xtStore, <|"MultiwayStateCount" -> {6, Infinity}|>];
    solutions = Normal @ ExperimentStoreQuery[$xtStore, Function[row, row["FrontMembership"] === "Solution"]];
    {
      added["RowsAdded"] === Length[$xtResult["Candidates"]],
      FileExistsQ[FileNameJoin[{$xtStore, "index.wxf"}]],
      FileExistsQ[FileNameJoin[{$xtStore, "runs", $xtResult["RunID"], "manifest.json"}]],
      Lookup[runs, "RunID"] === {$xtResult["RunID"]},
      First[runs]["CandidateCount"] === Length[$xtResult["Candidates"]],
      Lookup[all, "CandidateID"] === Lookup[$xtResult["Candidates"], "CandidateID"],
      Lookup[all, "EvaluationID"] === Lookup[$xtResult["Candidates"], "EvaluationID"],
      AllTrue[all,
        SubsetQ[Keys[#], {"RunID", "CandidateID", "EvaluationID", "EvolutionKey", "Status", "Rule", "Fitness", "FrontMembership"}] &],
      Sort[Lookup[halted, "CandidateID"]] ===
        Sort[Lookup[Select[$xtResult["Candidates"], #["Status"] === "Halted" &], "CandidateID"]],
      Sort[Lookup[ranged, "CandidateID"]] ===
        Sort[Lookup[Select[$xtResult["Candidates"], TrueQ[Lookup[#["Fitness"], "MultiwayStateCount", 0] >= 6] &], "CandidateID"]],
      Sort[Lookup[solutions, "CandidateID"]] === Sort[Lookup[$xtResult["SolutionParetoFront"], "CandidateID"]]
    }
  ],
  {True, True, True, True, True, True, True, True, True, True, True},
  TestID -> "Experiments-StoreAddRunsQuery"
]

VerificationTest[
  Module[{again, overwritten},
    again = ExperimentStoreAdd[$xtStore, $xtResult];
    overwritten = ExperimentStoreAdd[$xtStore, $xtResult, "Overwrite" -> True];
    {
      ExperimentStoreLoad[$xtStore, $xtResult["RunID"]] === $xtResult,
      again[[1]],
      overwritten["RowsAdded"] === Length[$xtResult["Candidates"]],
      Length[ExperimentStoreRuns[$xtStore]],
      Length[ExperimentStoreQuery[$xtStore]] === Length[$xtResult["Candidates"]],
      ExperimentStoreLoad[$xtStore, "no-such-run"][[1]],
      ExperimentStoreRuns[FileNameJoin[{$xtRoot, "no-such-store"}]][[1]],
      ExperimentStoreQuery[$xtStore, 42][[1]]
    }
  ],
  {True, "RunAlreadyStored", True, 1, True, "UnknownRun", "NoExperimentStore", "InvalidFilter"},
  TestID -> "Experiments-StoreLoadAndDuplicates"
]

VerificationTest[
  Module[{count, rerun, outcome},
    $priv["clearPreloadedEvaluations"][];
    $priv["ClearEvaluationCache"][];
    count = ExperimentStorePreload[$xtStore];
    rerun = StructureAdaptiveEvolution[
      Sequence @@ $xtOptions, "CustomFitnessMetrics" -> $xtCustom, "ReuseEvaluations" -> True];
    outcome = {
      count === Count[$xtResult["Candidates"], _?(#["Status"] =!= "TimedOut" &)],
      rerun["Performance"]["PreloadedHits"] === Length[rerun["Candidates"]],
      rerun["Performance"]["FreshEvaluations"],
      Lookup[rerun["Candidates"], "CandidateID"] === Lookup[$xtResult["Candidates"], "CandidateID"],
      Lookup[rerun["Candidates"], "Fitness"] === Lookup[$xtResult["Candidates"], "Fitness"]
    };
    $priv["clearPreloadedEvaluations"][];
    outcome
  ],
  {True, True, 0, True, True},
  TestID -> "Experiments-StorePreloadReuse"
]

VerificationTest[
  Module[{store = FileNameJoin[{$xtRoot, "timed-out-store"}], timed, count},
    timed = StructureAdaptiveEvolution[
      "Rule" -> $xtContract,
      "InitialState" -> $xtCycle4,
      "Rounds" -> 1,
      "MutationBudget" -> 2,
      "EvolutionLimits" -> <|"MaxGenerations" -> 5, "MaxEvents" -> 200, "TimeConstraint" -> 10^-6|>,
      "InitialStateDiagnostics" -> None,
      "RandomSeed" -> 3
    ];
    ExperimentStoreAdd[store, timed];
    $priv["clearPreloadedEvaluations"][];
    count = ExperimentStorePreload[store];
    $priv["clearPreloadedEvaluations"][];
    {
      timed["Baseline"]["Status"],
      count === Count[timed["Candidates"], _?(#["Status"] =!= "TimedOut" &)]
    }
  ],
  {"TimedOut", True},
  TestID -> "Experiments-PreloadExcludesTimedOut"
]


(* ::Section:: *)
(*Replication*)


VerificationTest[
  Module[{replicated, results, bestStateCounts},
    replicated = ReplicateEvolution[$xtOptions, {1, 2}];
    results = replicated["Results"];
    bestStateCounts = Map[
      Function[result,
        With[
          {solutions = Select[result["Candidates"], $priv["solutionEligibleQ"][#, result["Configuration"]] &]},
          If[solutions === {}, Missing["NoVerifiedSolution"], Max[Lookup[Lookup[solutions, "Fitness"], "MultiwayStateCount"]]]
        ]
      ],
      results
    ];
    {
      Lookup[replicated["Runs"], "Seed"],
      Lookup[Lookup[results, "Configuration"], "RandomSeed"],
      Lookup[replicated["Runs"], "RunID"] === Lookup[results, "RunID"],
      AllTrue[replicated["Runs"],
        SubsetQ[Keys[#], {"RunID", "Seed", "SolutionCount", "BestValues", "FreshEvaluations", "WallTime", "Failure"}] &],
      Keys[replicated["Distributions"]],
      Lookup[Lookup[replicated["Runs"], "BestValues"], "MultiwayStateCount"] === bestStateCounts,
      replicated["Distributions"]["MultiwayStateCount"]["Values"] === bestStateCounts,
      replicated["SuccessFraction"]["Trials"],
      replicated["SuccessFraction"]["Successes"] === Count[bestStateCounts, _Integer],
      replicated["SuccessFraction"]["WilsonInterval"] === WilsonInterval[replicated["SuccessFraction"]["Successes"], 2]
    }
  ],
  {
    {1, 2}, {1, 2}, True, True,
    {"MultiwayStateCount", "MultiwayTransitionCount", "MultiwayLongestDerivation", "HGMaxVerticesCount"},
    True, True, 2, True, True
  },
  TestID -> "Experiments-ReplicateEvolution"
]

VerificationTest[
  Module[{failed = ReplicateEvolution[{"Rule" -> $xtContract, "InitialState" -> $xtCycle4, "MutationBudget" -> 0}, {1, 2}]},
    {
      Length[failed["Runs"]],
      failed["SuccessFraction"]["Successes"],
      failed["SuccessFraction"]["Trials"],
      failed["FailedRuns"],
      AllTrue[failed["Results"], FailureQ],
      AllTrue[failed["Runs"], FailureQ[#["Failure"]] &],
      FailureQ[ReplicateEvolution[$xtOptions, {}]],
      FailureQ[ReplicateEvolution[$xtOptions, {1.5}]]
    }
  ],
  {2, 0, 2, 2, True, True, True, True},
  TestID -> "Experiments-ReplicateKeepsFailedRuns"
]


(* ::Section:: *)
(*Budget-matched baselines*)


$xtComparison = BaselineComparison[$xtOptions, <|"Seeds" -> {1, 2}|>];

VerificationTest[
  Module[{c = $xtComparison, search},
    search = Join[c["Results"]["Guided"], c["Results"]["Random"]];
    {
      c["Budget"],
      Keys[c["Methods"]],
      c["Signature"],
      Lookup[Lookup[c["Results"]["Guided"], "Configuration"], "AdaptiveWeights"],
      Lookup[Lookup[c["Results"]["Random"], "Configuration"], "AdaptiveWeights"],
      DeleteDuplicates @ Lookup[Lookup[search, "Configuration"], "InitialStateDiagnostics"],
      DeleteDuplicates @ Lookup[Lookup[search, "Configuration"], "EvolutionLimits"] === {c["EvolutionLimits"]},
      AllTrue[search, Length[#["Candidates"]] <= c["Budget"] &],
      Length[c["Results"]["Exhaustive"]] <= c["Budget"],
      DeleteDuplicates[Lookup[Lookup[search, "Seed"], "CanonicalInitialState"]] === {c["InitialState"]},
      DeleteDuplicates[Lookup[c["Results"]["Exhaustive"], "InitialState"]] === {c["InitialState"]},
      c["Methods"]["Exhaustive"]["Coverage"]["CanonicalRules"] ===
        Length[DeleteDuplicates[CanonicalRuleForm /@ EnumerateWolframModelRules[{{2, 2}} -> {{1, 2}}]]],
      Lookup[Lookup[Values[c["Methods"]], "SuccessRate"], "Trials"]
    }
  ],
  {
    5, {"Guided", "Random", "Exhaustive"}, {{2, 2}} -> {{1, 2}},
    {True, True}, {False, False}, {None}, True, True, True, True, True, True, {2, 2, 1}
  },
  TestID -> "Experiments-BaselineBudgetsMatch"
]

VerificationTest[
  Module[{c = $xtComparison, firstSolution, eligible},
    eligible = Function[result, $priv["solutionEligibleQ"][#, result["Configuration"]] & /@ result["Candidates"]];
    firstSolution = Function[result,
      Replace[FirstPosition[eligible[result], True, {Missing["NoVerifiedSolution"]}, {1}], {k_} :> k]];
    {
      c["Methods"]["Guided"]["EvaluationsToFirstSolution"]["PerRun"] === (firstSolution /@ c["Results"]["Guided"]),
      c["Methods"]["Random"]["EvaluationsToFirstSolution"]["PerRun"] === (firstSolution /@ c["Results"]["Random"]),
      c["Methods"]["Guided"]["SolutionCounts"] === (Count[eligible[#], True] & /@ c["Results"]["Guided"]),
      c["Methods"]["Guided"]["SuccessRate"]["WilsonInterval"] ===
        WilsonInterval[c["Methods"]["Guided"]["SuccessRate"]["Successes"], 2],
      c["Methods"]["Exhaustive"]["ComputeCost"]["FreshEvaluations"] === Length[c["Results"]["Exhaustive"]],
      AllTrue[Values[c["Methods"]],
        SubsetQ[Keys[#], {"SuccessRate", "EvaluationsToFirstSolution", "SolutionCounts", "BestObjectiveValues", "ComputeCost", "Claim"}] &],
      AllTrue[Values[c["Methods"]],
        StringStartsQ[#["Claim"],
          "Under signature {{2, 2}} -> {{1, 2}}, initial state " <> ToString[c["InitialState"], InputForm] <>
            ", equivalence " <> c["StateEquivalence"] <> " and limits "] &],
      NoneTrue[Values[c["Methods"]], StringContainsQ[#["Claim"], "physic", IgnoreCase -> True] &]
    }
  ],
  {True, True, True, True, True, True, True, True},
  TestID -> "Experiments-BaselineReportsAndClaims"
]


(* ::Section:: *)
(*Robustness and cap sensitivity*)


VerificationTest[
  Module[{robustness, again, caps},
    robustness = CandidateRobustness[$xtResult, $xtSolutionID, "EnsembleSize" -> 4];
    again = CandidateRobustness[$xtResult, $xtSolutionID, "EnsembleSize" -> 4, "CapFactors" -> {}, "RewriteSemantics" -> False];
    caps = robustness["CapSensitivity"]["Evaluations"];
    {
      robustness["BaseStatus"],
      Lookup[caps, "Factor"],
      Lookup[caps, "Status"],
      Lookup[caps, "EvolutionLimits"],
      robustness["CapSensitiveQ"],
      robustness["InitialStateCorpus"]["Source"],
      robustness["InitialStateCorpus"]["StatesTested"] <= 4,
      robustness["InitialStateCorpus"]["StatesTested"] === Length[robustness["InitialStateCorpus"]["PerState"]],
      Lookup[robustness["InitialStateCorpus"]["PerState"], "InitialState"] ===
        Lookup[again["InitialStateCorpus"]["PerState"], "InitialState"],
      robustness["RewriteSemantics"]["Alternative"],
      MemberQ[{True, False}, robustness["SemanticsSensitiveQ"]],
      again["RewriteSemantics"],
      StringQ[robustness["Summary"]]
    }
  ],
  {
    "Halted", {2, 4}, {"Halted", "Halted"},
    {
      <|"MaxGenerations" -> 10, "MaxEvents" -> 400, "MaxStates" -> Infinity, "TimeConstraint" -> 40.|>,
      <|"MaxGenerations" -> 20, "MaxEvents" -> 800, "MaxStates" -> Infinity, "TimeConstraint" -> 80.|>
    },
    False, "DiagnosticInitialStateEnsemble", True, True, True, "VertexDeletion", True,
    Missing["NotRequested"], True
  },
  TestID -> "Experiments-RobustnessHaltedCandidate"
]

VerificationTest[
  Module[{robustness},
    robustness = CandidateRobustness[$xtCapped, $xtCappedID,
      "InitialStates" -> {{{1, 2}, {2, 3}}, {{1, 2}, {2, 3}}}, "RewriteSemantics" -> False];
    {
      $xtCapped["Baseline"]["Status"],
      Lookup[robustness["CapSensitivity"]["Evaluations"], "Status"],
      robustness["CapSensitiveQ"],
      robustness["InitialStateCorpus"]["Source"],
      robustness["InitialStateCorpus"]["StatesTested"],
      robustness["InitialStateCorpus"]["HaltedCount"],
      StringContainsQ[robustness["Summary"], "cap-sensitive"],
      CandidateRobustness[$xtCapped, "no-such-candidate"][[1]],
      CandidateRobustness[$xtCapped, $xtCappedID, "CapFactors" -> {0}][[1]],
      CandidateRobustness[$xtCapped, $xtCappedID, "InitialStates" -> {"not a state"}][[1]]
    }
  ],
  {
    "GenerationCap", {"Halted", "Halted"}, True, "User", 1, 1, True,
    "UnknownCandidate", "InvalidCapFactors", "InvalidInitialStates"
  },
  TestID -> "Experiments-RobustnessCapSensitive"
]

VerificationTest[
  Module[{report = RobustnessReport[$xtResult, "CapFactors" -> {2}, "EnsembleSize" -> 4]},
    {
      report["FinalistSource"],
      Lookup[report["Finalists"], "CandidateID"] === Lookup[$xtResult["SolutionParetoFront"], "CandidateID"],
      DeleteDuplicates[
        Lookup[#["InitialStateCorpus"]["PerState"], "InitialState"] & /@ report["Finalists"]
      ] === {report["InitialStates"]},
      DeleteDuplicates[Lookup[Lookup[report["Finalists"], "InitialStateCorpus"], "Source"]],
      report["CapSensitiveIDs"],
      report["StateEquivalence"] === $xtResult["Provenance"]["StateEquivalence"]
    }
  ],
  {"SolutionParetoFront", True, True, {"DiagnosticInitialStateEnsemble"}, {}, True},
  TestID -> "Experiments-RobustnessReport"
]


(* ::Section:: *)
(*Discovery report*)


VerificationTest[
  Module[{report = DiscoveryReport[$xtResult, $xtSolutionID], lines},
    lines = StringSplit[report["Text"], "\n"];
    {
      Keys[report] === Append[$xtDiscoveryFields, "Text"],
      AllTrue[$xtDiscoveryFields, AssociationQ[report[#]] && StringQ[report[#]["Summary"]] &],
      Length[lines],
      AllTrue[Transpose[{Rest[lines], $xtDiscoveryFields}], StringStartsQ[#[[1]], #[[2]] <> ": "] &],
      report["Candidate ID / evaluation ID"]["EvaluationID"] ===
        SelectFirst[$xtResult["Candidates"], #["CandidateID"] === $xtSolutionID &]["EvaluationID"],
      report["Canonical rule"]["Rule"] === SelectFirst[$xtResult["Candidates"], #["CandidateID"] === $xtSolutionID &]["Rule"],
      report["Search-front / solution-front membership"]["SolutionFrontQ"],
      report["Mutation lineage"]["Path"][[1, "Strategy"]],
      report["Mutation lineage"]["Path"][[-1, "CandidateID"]] === $xtSolutionID,
      report["Initial-state robustness summary"]["Source"]
    }
  ],
  {True, True, 19, True, True, True, True, "Seed", True, "InitialStateDiagnostics"},
  TestID -> "Experiments-DiscoveryReportTemplate"
]

VerificationTest[
  Module[{report = DiscoveryReport[$xtResult, $xtSolutionID], text},
    text = report["Text"];
    {
      report["Status and cycle evidence"]["Statement"],
      report["Interpretation with evidence level"]["EvidenceLevel"],
      report["Lifetime (longest derivation and BFS depth) and maximum frontier"]["LongestDerivationExactQ"],
      report["Constraint satisfaction"]["SolutionEligibleQ"],
      StringContainsQ[text, "verified to halt under this finite reachable exploration"],
      StringContainsQ[text, $xtResult["Provenance"]["StateEquivalence"]],
      StringContainsQ[text, "not resolved within the stated limits"],
      StringContainsQ[text, "physic", IgnoreCase -> True]
    }
  ],
  {"verified to halt under this finite reachable exploration", "VerifiedSolution", True, True, True, True, False, False},
  TestID -> "Experiments-DiscoveryClaimsHalted"
]

VerificationTest[
  Module[{robustness, plain, withRobustness},
    robustness = CandidateRobustness[$xtCapped, $xtCappedID, "InitialStates" -> {{{1, 2}, {2, 3}}}, "RewriteSemantics" -> False];
    plain = DiscoveryReport[$xtCapped, $xtCappedID];
    withRobustness = DiscoveryReport[$xtCapped, $xtCappedID, "Robustness" -> robustness];
    {
      plain["Status and cycle evidence"]["Statement"],
      plain["Interpretation with evidence level"]["EvidenceLevel"],
      StringContainsQ[plain["Text"], "not resolved within the stated limits"],
      StringContainsQ[plain["Text"], "verified to halt"],
      StringContainsQ[plain["Text"], "cycle detected"],
      plain["Initial-state robustness summary"]["Available"],
      withRobustness["Initial-state robustness summary"]["CapSensitiveQ"],
      StringContainsQ[withRobustness["Text"], "cap-sensitive"],
      DiscoveryReport[$xtResult, $xtSolutionID, "Robustness" -> robustness][[1]],
      DiscoveryReport[$xtResult, "no-such-candidate"][[1]]
    }
  ],
  {
    "not resolved within the stated limits", "Unresolved", True, False, False, False, True, True,
    "RobustnessMismatch", "UnknownCandidate"
  },
  TestID -> "Experiments-DiscoveryClaimsCapped"
]

VerificationTest[
  Module[{report, unwitnessed, stripped},
    report = DiscoveryReport[$xtResult, $xtCycleID];
    (* Claim discipline: without a recorded witness the cycle is not claimed. *)
    unwitnessed = MapAt[
      Map[If[#["CandidateID"] === $xtCycleID, Append[#, "CycleWitness" -> Missing["NotRecorded"]], #] &],
      $xtResult,
      {"Candidates"}
    ];
    stripped = DiscoveryReport[unwitnessed, $xtCycleID];
    {
      report["Status and cycle evidence"]["CycleWitnessRecordedQ"],
      report["Interpretation with evidence level"]["EvidenceLevel"],
      StringContainsQ[report["Text"], "cycle detected"],
      StringContainsQ[report["Text"], "verified to halt"],
      stripped["Interpretation with evidence level"]["EvidenceLevel"],
      StringContainsQ[stripped["Text"], "cycle detected"],
      StringContainsQ[stripped["Text"], "not resolved within the stated limits"]
    }
  ],
  {True, "WitnessedCycle", True, False, "Unresolved", False, True},
  TestID -> "Experiments-DiscoveryClaimsCycle"
]


(* ::Section:: *)
(*Seed corpus*)


VerificationTest[
  Module[{corpus = SeedCorpus[]},
    {
      Length[corpus] >= 10,
      AllTrue[corpus, SubsetQ[Keys[#], {"Name", "Rule", "InitialState", "EdgeSymmetry", "Limits", "ExpectedStatus", "Notes"}] &],
      DuplicateFreeQ[Lookup[corpus, "Name"]],
      SubsetQ[Lookup[corpus, "ExpectedStatus"], {"Halted", "CycleDetected", "GenerationCap", "EventCap", "StateCap"}],
      AnyTrue[corpus, MatchQ[#["Rule"], {__Rule}] &],
      AnyTrue[corpus, #["EdgeSymmetry"] === "Ordered" &],
      AnyTrue[corpus, #["EdgeSymmetry"] === "Declared" && #["SymmetryGroups"] === <|3 -> "Cyclic"|> &],
      AnyTrue[corpus,
        #["Rule"] === ({{1, 2}, {2, 3}} -> {{1, 3}}) && #["ExpectedStatus"] === "Halted" &&
          MemberQ[#["InitialState"], {4, 1}] &],
      AllTrue[corpus, AssociationQ[#["Limits"]] && SubsetQ[Keys[#["Limits"]], {"MaxGenerations", "MaxEvents", "MaxStates", "TimeConstraint"}] &]
    }
  ],
  {True, True, True, True, True, True, True, True, True},
  TestID -> "Experiments-SeedCorpusCoverage"
]

VerificationTest[
  Module[{verified = VerifySeedCorpus[], wrong},
    wrong = VerifySeedCorpus[{Append[First[SeedCorpus[]], "ExpectedStatus" -> "CycleDetected"]}];
    {
      verified["AllMatchQ"],
      verified["Mismatches"],
      Length[verified["Entries"]] === Length[SeedCorpus[]],
      Lookup[verified["Entries"], "ObservedStatus"] === Lookup[SeedCorpus[], "ExpectedStatus"],
      AllTrue[Select[verified["Entries"], #["ObservedStatus"] === "CycleDetected" &], #["CycleWitnessQ"] &],
      wrong["AllMatchQ"],
      wrong["Mismatches"] === {First[SeedCorpus[]]["Name"]},
      FailureQ[VerifySeedCorpus[{}]]
    }
  ],
  {True, {}, True, True, True, False, True, True},
  TestID -> "Experiments-VerifySeedCorpus"
]


(* ::Section:: *)
(*Cleanup*)


VerificationTest[
  $priv["clearPreloadedEvaluations"][];
  DeleteDirectory[$xtRoot, DeleteContents -> True];
  DirectoryQ[$xtRoot],
  False,
  TestID -> "Experiments-Cleanup"
]
