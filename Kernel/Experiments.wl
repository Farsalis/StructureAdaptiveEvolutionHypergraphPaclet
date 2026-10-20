(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context.

   Experimental-protocol layer: lossless result export/import with a run
   manifest, a persistent experiment store with cross-run evaluation reuse,
   multi-seed replication, budget-matched baselines, robustness and
   cap-sensitivity analysis, discovery reports with claim discipline, a
   verified seed corpus and Wilson score intervals.

   Every module shares the Private context, so all helpers of this file carry
   the prefix "xp". *)


(* ::Section:: *)
(*Shared helpers*)


xpResultQ[result_] :=
  AssociationQ[result] &&
    SubsetQ[
      Keys[result],
      {
        "RunID", "Configuration", "Seed", "Candidates", "SearchParetoFront",
        "SolutionParetoFront", "FrontMembership", "Provenance"
      }
    ]


xpNotResult[value_] :=
  Failure[
    "NotAnEvolutionResult",
    <|
      "Message" -> "Expected a StructureAdaptiveEvolution result association.",
      "Head" -> Head[value]
    |>
  ]


xpPath[File[path_String]] := path
xpPath[path_String] := path
xpPath[other_] := other


xpInvalidDirectory[value_] :=
  Failure[
    "InvalidDirectory",
    <|"Message" -> "The directory must be a path string or File[...].", "Directory" -> value|>
  ]


xpEnsureDirectory[directory_String] := (
  If[!DirectoryQ[directory], Quiet @ CreateDirectory[directory, CreateIntermediateDirectories -> True]];
  If[
    DirectoryQ[directory],
    directory,
    Failure[
      "DirectoryNotWritable",
      <|"Message" -> "The directory could not be created.", "Directory" -> directory|>
    ]
  ]
)


(* InputForm text that does not depend on the caller's context path:
   Global` symbols print bare, every other non-System symbol with its
   context. *)
xpInputString[expr_] :=
  Block[{$Context = "Global`", $ContextPath = {"System`", "Global`"}},
    ToString[expr, InputForm, PageWidth -> Infinity]
  ]


xpShortID[id_String] := StringTake[id, UpTo[12]]
xpShortID[other_] := xpInputString[other]


xpFailureTag[failure_Failure] :=
  Replace[First[failure, Missing[]], {tag_String :> tag, other_ :> xpInputString[other]}]


xpMissingReason[Missing[reason_String, ___]] := reason
xpMissingReason[Missing[]] := "Missing"
xpMissingReason[missing_Missing] := xpInputString[missing]
xpMissingReason[failure_Failure] := "Failure: " <> xpFailureTag[failure]
xpMissingReason[other_] := xpInputString[other]


(* Human-readable scalar text (summaries, claims, reports). *)
xpValueString[value_Real] :=
  If[
    TrueQ[Abs[value] < 10^6],
    ToString[N[Round[1000 value]/1000], InputForm],
    ToString[value, InputForm]
  ]
xpValueString[value_Integer] := ToString[value]
xpValueString[value_String] := value
xpValueString[value_Missing] := "n/a (" <> xpMissingReason[value] <> ")"
xpValueString[value_Failure] := "failed (" <> xpFailureTag[value] <> ")"
xpValueString[other_] := xpInputString[other]


xpLimitsString[limits_Association] :=
  StringRiffle[KeyValueMap[#1 <> " " <> xpValueString[#2] &, limits], ", "]
xpLimitsString[other_] := xpValueString[other]


xpDistributionSummary[values_List] :=
  With[{numeric = Select[values, NumericQ]},
    If[
      numeric === {},
      Missing["NoValues"],
      <|
        "Count" -> Length[numeric],
        "Minimum" -> Min[numeric],
        "Median" -> N @ Median[numeric],
        "Mean" -> N @ Mean[numeric],
        "Maximum" -> Max[numeric]
      |>
    ]
  ]


xpCycleWitnessQ[candidate_Association] :=
  MatchQ[Lookup[candidate, "CycleWitness", Missing["NotRecorded"]], {__DirectedEdge}]


xpFindCandidate[result_Association, candidateID_] :=
  SelectFirst[result["Candidates"], #["CandidateID"] === candidateID &, Missing["UnknownCandidate"]]


xpUnknownCandidate[candidateID_] :=
  Failure[
    "UnknownCandidate",
    <|"Message" -> "The result contains no candidate with this CandidateID.", "CandidateID" -> candidateID|>
  ]


(* A stored configuration restricted to metrics known in this session, so
   results written by a session with more registered metrics stay usable. *)
xpSafeConfig[config_Association] :=
  Append[
    config,
    "FitnessMetrics" -> Select[
      Lookup[config, "FitnessMetrics", {}],
      KeyExistsQ[$FitnessMetricRegistry, #] ||
        KeyExistsQ[Lookup[config, "CustomFitnessMetrics", <||>], #] &
    ]
  ]


xpMetricSpecifications[config_Association] :=
  resolveMetricSpecifications[xpSafeConfig[config]]


xpMetricSpecification[name_String, config_Association] :=
  Lookup[
    xpMetricSpecifications[config],
    name,
    Lookup[$FitnessMetricRegistry, name, Missing["UnknownMetric", name]]
  ]


xpSolutionQ[candidate_Association, config_Association] :=
  TrueQ[Quiet @ Check[solutionEligibleQ[candidate, xpSafeConfig[config]], False]]


(* Best value of a metric over candidates under the metric's own direction
   (the value with the least minimization coordinate). *)
xpBestValue[{}, _String, _Association, emptyReason_String] := Missing[emptyReason]

xpBestValue[candidates_List, metric_String, config_Association, emptyReason_String] :=
  Module[{values, specification},
    values = Select[
      Lookup[Lookup[candidates, "Fitness", <||>], metric, Missing["NotComputed"]],
      NumericQ
    ];
    If[!ListQ[values] || values === {}, Return[Missing[emptyReason]]];
    specification = xpMetricSpecification[metric, config];
    If[
      AssociationQ[specification],
      First @ MinimalBy[values, NormalizedObjectiveValue[#, specification, config] &],
      Max[values]
    ]
  ]


xpSideSignature[side_List] := SortBy[Reverse /@ Tally[Length /@ side], Last]

xpRuleSignature[lhs_List -> rhs_List] := xpSideSignature[lhs] -> xpSideSignature[rhs]
xpRuleSignature[_] := Missing["NotASingleRule"]


xpSignatureString[signature_Rule] := xpInputString[signature]
xpSignatureString[_] := "n/a (rule-set seed)"


xpStateEquivalence[result_Association] :=
  Lookup[result["Provenance"], "StateEquivalence", stateEquivalenceTag[result["Configuration"]]]


(* ::Section:: *)
(*WXF and JSON*)


xpWriteWXF[file_String, expr_] := Module[{stream},
  stream = Quiet @ Check[OpenWrite[file, BinaryFormat -> True], $Failed];
  If[stream === $Failed, Return[$Failed]];
  BinaryWrite[stream, BinarySerialize[expr, PerformanceGoal -> "Size"]];
  Close[stream];
  file
]


xpReadWXF[file_String] := Quiet @ Check[BinaryDeserialize[ReadByteArray[file]], $Failed]


xpFileHash[file_String] := FileHash[file, "SHA256", All, "HexString"]


(* WXF restores a Graph in an indexed internal form that prints and
   compares differently inside larger expressions; rebuilding every graph
   from its vertices, edges and options restores the original form exactly.
   The rebuilt graph is evaluated during the replacement (the /; True form):
   values replaced inside an Association are not evaluated afterwards. *)
xpRebuildGraphs[expr_] :=
  expr /. graph_Graph :> With[
    {rebuilt = Graph[VertexList[graph], EdgeList[graph], Options[graph]]},
    rebuilt /; True
  ]


xpJSONKey[key_String] := key
xpJSONKey[key_] := xpInputString[key]


(* JSON-safe data: Missing becomes null, Infinity a string, Function and
   other symbolic expressions their InputForm strings, a Graph its sizes. *)
xpJSONSafe[Null] := Null
xpJSONSafe[True] := True
xpJSONSafe[False] := False
xpJSONSafe[value_String] := value
xpJSONSafe[value_Integer] := value
xpJSONSafe[value_Real] :=
  If[TrueQ[Abs[value] < $MaxMachineNumber], N[value], xpInputString[value]]
xpJSONSafe[value_Rational] := N[value]
xpJSONSafe[DirectedInfinity[1]] := "Infinity"
xpJSONSafe[DirectedInfinity[-1]] := "-Infinity"
xpJSONSafe[_Missing] := Null
xpJSONSafe[failure_Failure] :=
  <|
    "Failure" -> xpFailureTag[failure],
    "Message" -> Replace[Quiet[failure["Message"]], Except[_String] -> Null]
  |>
xpJSONSafe[association_Association] :=
  Association @ KeyValueMap[xpJSONKey[#1] -> xpJSONSafe[#2] &, association]
xpJSONSafe[list_List] := xpJSONSafe /@ list
xpJSONSafe[graph_Graph] := <|"VertexCount" -> VertexCount[graph], "EdgeCount" -> EdgeCount[graph]|>
xpJSONSafe[other_] := xpInputString[other]


(* Fitness with Missing (and failed) values as null plus their reasons. *)
xpFitnessJSON[fitness_Association] :=
  With[{missing = Select[fitness, MissingQ[#] || FailureQ[#] &]},
    <|
      "Fitness" -> Association @ KeyValueMap[
        xpJSONKey[#1] -> If[KeyExistsQ[missing, #1], Null, xpJSONSafe[#2]] &,
        fitness
      ],
      "FitnessMissingReasons" -> Association @ KeyValueMap[
        xpJSONKey[#1] -> xpMissingReason[#2] &,
        missing
      ]
    |>
  ]
xpFitnessJSON[_] := <|"Fitness" -> <||>, "FitnessMissingReasons" -> <||>|>


(* ::Section:: *)
(*Run manifest*)


(* The paclet's git checkout, from the core (pacletGitInformation in
   Evaluation.wl): the commit, whether tracked files differ from it, and
   whether the repository top level is the paclet root itself. *)
xpGitInformation[] := pacletGitInformation[]


xpMetricSpecificationRows[config_Association] :=
  KeyValueMap[
    Function[{name, specification},
      <|
        "Name" -> name,
        "Direction" -> xpJSONSafe[Lookup[specification, "Direction", Missing[]]],
        "Stage" -> xpJSONSafe[Lookup[specification, "Stage", "Objective"]],
        "Range" -> xpJSONSafe[
          If[
            Lookup[specification, "Direction", None] === "Range",
            resolveObjectiveRange[specification, config],
            Lookup[specification, "Range", Missing[]]
          ]
        ],
        "Target" -> xpJSONSafe[Lookup[specification, "Target", Missing[]]],
        "Tolerance" -> xpJSONSafe[Lookup[specification, "Tolerance", Missing[]]],
        "Threshold" -> xpJSONSafe[Lookup[specification, "Threshold", Missing[]]],
        "ValueType" -> xpJSONSafe[Lookup[specification, "ValueType", Missing[]]],
        "Input" -> xpJSONSafe[Lookup[specification, "Input", Missing[]]],
        "Parameters" -> xpJSONSafe[Lookup[specification, "Parameters", Missing[]]],
        "Custom" -> KeyExistsQ[Lookup[config, "CustomFitnessMetrics", <||>], name]
      |>
    ],
    xpMetricSpecifications[config]
  ]


xpStrategyRows[result_Association] := Module[{initial, final, strategies},
  initial = Replace[First[Lookup[result, "StrategyWeightHistory", {}], <||>], Except[_Association] -> <||>];
  final = Replace[Lookup[result, "FinalStrategyWeights", <||>], Except[_Association] -> <||>];
  strategies = Lookup[result["Configuration"], "MutationStrategies", Keys[final]];
  Map[
    <|
      "Strategy" -> #,
      "InitialWeight" -> xpJSONSafe[Lookup[initial, #, Missing[]]],
      "FinalWeight" -> xpJSONSafe[Lookup[final, #, Missing[]]]
    |> &,
    strategies
  ]
]


xpCandidateManifestRow[candidate_Association, result_Association, config_Association] :=
  Join[
    <|
      "CandidateID" -> candidate["CandidateID"],
      "EvaluationID" -> xpJSONSafe[Lookup[candidate, "EvaluationID", Missing[]]],
      "EvolutionKey" -> xpJSONSafe[Lookup[candidate, "EvolutionKey", Missing[]]],
      "ParentID" -> xpJSONSafe[Lookup[candidate, "ParentID", Missing[]]],
      "Round" -> xpJSONSafe[Lookup[candidate, "Round", Missing[]]],
      "Trial" -> xpJSONSafe[Lookup[candidate, "Trial", Missing[]]],
      "Strategy" -> xpJSONSafe[Lookup[candidate, "Strategy", Missing[]]],
      "AppliedOperators" -> xpJSONSafe[
        Lookup[Lookup[candidate, "Provenance", <||>], "AppliedOperators", {}]
      ],
      "CanonicalRule" -> xpInputString[candidate["Rule"]],
      "Status" -> xpJSONSafe[Lookup[candidate, "Status", Missing[]]],
      "ValidQ" -> TrueQ[Lookup[candidate, "ValidQ", False]],
      "CycleWitnessPresent" -> xpCycleWitnessQ[candidate],
      "LimitsReached" -> xpJSONSafe[Lookup[candidate, "LimitsReached", {}]],
      "StateCount" -> Length[Lookup[candidate, "States", {}]],
      "TransitionCount" -> xpJSONSafe[Lookup[candidate, "TransitionCount", Missing[]]],
      "EventCount" -> xpJSONSafe[Lookup[candidate, "EventCount", Missing[]]]
    |>,
    xpFitnessJSON[Lookup[candidate, "Fitness", <||>]],
    <|
      "Runtime" -> xpJSONSafe[Lookup[candidate, "Runtime", Missing[]]],
      "FrontMembership" -> Lookup[result["FrontMembership"], candidate["CandidateID"], "None"],
      "SolutionEligibleQ" -> xpSolutionQ[candidate, config]
    |>
  ]


xpDiagnosticsSummary[diagnostics_Association] :=
  <|
    "Requested" -> True,
    "EnsemblePolicy" -> xpJSONSafe[Lookup[diagnostics, "EnsemblePolicy", Missing[]]],
    "EnsembleSize" -> Length[Lookup[diagnostics, "Ensemble", {}]],
    "Finalists" -> Map[
      xpJSONSafe @ KeyTake[
        #,
        {
          "CandidateID", "InitialStatesTested", "InitiallyApplicableRate", "TerminationRate",
          "MedianMultiwayStateCount", "MinimumMultiwayStateCount", "MaximumMultiwayStateCount",
          "WorstCaseRuntime"
        }
      ] &,
      Select[Lookup[diagnostics, "Finalists", {}], AssociationQ]
    ]
  |>
xpDiagnosticsSummary[missing_Missing] := <|"Requested" -> False, "Reason" -> xpMissingReason[missing]|>
xpDiagnosticsSummary[_] := <|"Requested" -> Null|>


xpManifest[result_Association, hash_String, bytes_Integer] := Module[
  {config, seed, provenance, candidates, git, solutions},

  config = result["Configuration"];
  seed = result["Seed"];
  provenance = result["Provenance"];
  candidates = result["Candidates"];
  (* The commit recorded by the run itself ("PacletGitCommit" in its
     provenance) wins over the commit at export time. *)
  git = If[
    StringQ[Lookup[provenance, "PacletGitCommit", None]],
    <|
      "Commit" -> provenance["PacletGitCommit"],
      "Dirty" -> Replace[Lookup[provenance, "PacletGitDirty", Null], Except[True | False] -> Null],
      "RootIsPacletRoot" -> Null,
      "RecordedAt" -> "Run"
    |>,
    Append[xpGitInformation[], "RecordedAt" -> "Export"]
  ];
  solutions = Select[candidates, xpSolutionQ[#, config] &];

  <|
    "Format" -> "StructureAdaptiveEvolution-RunManifest",
    "FormatVersion" -> 1,
    "RunID" -> result["RunID"],
    "ExportedAt" -> DateString["ISODateTime"],
    "Provenance" -> xpJSONSafe[provenance],
    "PacletGitCommit" -> git["Commit"],
    "PacletGitDirty" -> git["Dirty"],
    "PacletGitRootIsPacletRoot" -> git["RootIsPacletRoot"],
    "PacletGitCommitRecordedAt" -> git["RecordedAt"],
    "Configuration" -> xpJSONSafe[config],
    "Seed" -> <|
      "SeedID" -> xpJSONSafe[Lookup[seed, "SeedID", Missing[]]],
      "Source" -> xpJSONSafe[Lookup[seed, "Source", Missing[]]],
      "RegistryCode" -> xpJSONSafe[Lookup[seed, "RegistryCode", Missing[]]],
      "RegistryVersion" -> xpJSONSafe[Lookup[seed, "RegistryVersion", Missing[]]],
      "OriginalRule" -> xpInputString[Lookup[seed, "OriginalRule", Missing[]]],
      "OriginalInitialState" -> xpJSONSafe[Lookup[seed, "OriginalInitialState", Missing[]]],
      "CanonicalRule" -> xpInputString[Lookup[seed, "CanonicalRule", Missing[]]],
      "CanonicalInitialState" -> xpJSONSafe[Lookup[seed, "CanonicalInitialState", Missing[]]],
      "InitiallyApplicableQ" -> xpJSONSafe[Lookup[seed, "InitiallyApplicableQ", Missing[]]]
    |>,
    "Universe" -> <|
      "EdgeSymmetry" -> config["EdgeSymmetry"],
      "SymmetryGroups" -> xpJSONSafe[config["SymmetryGroups"]],
      "RewriteSemantics" -> config["RewriteSemantics"],
      "CanonicalForm" -> config["CanonicalForm"],
      "StateEquivalence" -> xpStateEquivalence[result]
    |>,
    "EvolutionLimits" -> xpJSONSafe[config["EvolutionLimits"]],
    "RandomSeed" -> xpJSONSafe[config["RandomSeed"]],
    "Strategies" -> <|
      "AdaptiveWeights" -> config["AdaptiveWeights"],
      "Weights" -> xpStrategyRows[result]
    |>,
    "MetricSpecifications" -> xpMetricSpecificationRows[config],
    "RoundsCompleted" -> xpJSONSafe[Lookup[Lookup[result, "ResumeState", <||>], "RoundsCompleted", Missing[]]],
    "CandidateCount" -> Length[candidates],
    "StatusCounts" -> xpJSONSafe[Counts[Lookup[candidates, "Status", {}]]],
    "SearchFrontIDs" -> Lookup[result["SearchParetoFront"], "CandidateID", {}],
    "SolutionFrontIDs" -> Lookup[result["SolutionParetoFront"], "CandidateID", {}],
    "Candidates" -> (xpCandidateManifestRow[#, result, config] & /@ candidates),
    "Solutions" -> Map[
      <|
        "CandidateID" -> #["CandidateID"],
        "FrontMembership" -> Lookup[result["FrontMembership"], #["CandidateID"], "None"],
        "TerminalStateCount" -> Length[Lookup[#, "FinalStates", {}]],
        "VerifiedTerminalStates" -> xpJSONSafe[Lookup[#, "FinalStates", {}]]
      |> &,
      solutions
    ],
    "InitialStateDiagnostics" -> xpDiagnosticsSummary[Lookup[result, "InitialStateDiagnostics", Missing["NotRecorded"]]],
    "ProposalFailureCount" -> Length[Lookup[result, "ProposalFailures", {}]],
    "Performance" -> xpJSONSafe[Lookup[result, "Performance", <||>]],
    "Files" -> <|"result.wxf" -> <|"SHA256" -> hash, "Bytes" -> bytes|>|>,
    "WXFSHA256" -> hash
  |>
]


(* ::Section:: *)
(*Human-readable summary*)


xpMarkdownCell[value_] :=
  StringReplace[xpValueString[value], {"|" -> "\\|", "\n" -> " "}]


xpSummaryMarkdown[result_Association, manifest_Association] := Module[
  {config, provenance, seed, candidates, statuses, objectives, frontTable, lines, gitText, groups},

  config = result["Configuration"];
  provenance = result["Provenance"];
  seed = result["Seed"];
  candidates = result["Candidates"];
  statuses = Counts[Lookup[candidates, "Status", {}]];
  objectives = Keys @ Select[xpMetricSpecifications[config], Lookup[#, "Stage", "Objective"] === "Objective" &];

  gitText = Replace[
    manifest["PacletGitCommit"],
    {
      commit_String :> commit <>
        Switch[manifest["PacletGitDirty"], True, ", tracked files modified", False, ", clean", _, ""] <>
        ", recorded at " <> ToLowerCase[xpValueString[manifest["PacletGitCommitRecordedAt"]]] <> " time",
      _ -> "unknown"
    }
  ];
  groups = If[config["SymmetryGroups"] === <||>, "none", xpInputString[config["SymmetryGroups"]]];

  frontTable[title_String, front_List] :=
    If[
      front === {},
      {"## " <> title, "", "Empty.", ""},
      Join[
        {
          "## " <> title,
          "",
          "| Candidate | Strategy | Status | Rule | " <> StringRiffle[objectives, " | "] <> " |",
          "|" <> StringRepeat["---|", 4 + Length[objectives]]
        },
        Map[
          Function[candidate,
            "| " <> StringRiffle[
              Join[
                {
                  xpShortID[candidate["CandidateID"]],
                  xpMarkdownCell[Lookup[candidate, "Strategy", Missing[]]],
                  xpMarkdownCell[Lookup[candidate, "Status", Missing[]]],
                  "`" <> xpInputString[candidate["Rule"]] <> "`"
                },
                xpMarkdownCell[Lookup[Lookup[candidate, "Fitness", <||>], #, Missing["NotComputed"]]] & /@ objectives
              ],
              " | "
            ] <> " |"
          ],
          Take[front, UpTo[50]]
        ],
        {""}
      ]
    ];

  lines = Join[
    {
      "# StructureAdaptiveEvolution run " <> result["RunID"],
      "",
      "| Field | Value |",
      "|---|---|",
      "| Started / ended | " <> xpMarkdownCell[Lookup[provenance, "StartTime", Missing[]]] <> " / " <>
        xpMarkdownCell[Lookup[provenance, "EndTime", Missing[]]] <> " |",
      "| Resumed from | " <> xpMarkdownCell[Lookup[provenance, "ResumedFrom", None]] <> " |",
      "| Wolfram Language | " <> xpMarkdownCell[Lookup[provenance, "WolframVersion", Missing[]]] <> " |",
      "| Paclet version | " <> xpMarkdownCell[Lookup[provenance, "PacletVersion", Missing[]]] <> " (git " <> gitText <> ") |",
      "| Hypergraph paclet | " <> xpMarkdownCell[Lookup[provenance, "HypergraphPacletVersion", Missing[]]] <> " |",
      "| Evaluator | CanonicalBFS, version " <> xpMarkdownCell[Lookup[provenance, "EvaluatorVersion", Missing[]]] <> " |",
      "| Edge symmetry | " <> config["EdgeSymmetry"] <> " (symmetry groups: " <> StringReplace[groups, "|" -> "\\|"] <> ") |",
      "| Rewrite semantics | " <> config["RewriteSemantics"] <> " |",
      "| Canonical form | " <> config["CanonicalForm"] <> " |",
      "| State equivalence | " <> xpStateEquivalence[result] <> " |",
      "| Evolution limits | " <> xpLimitsString[config["EvolutionLimits"]] <> " |",
      "| Random seed | " <> xpMarkdownCell[config["RandomSeed"]] <> " |",
      "| Seed rule (original) | `" <> xpInputString[Lookup[seed, "OriginalRule", Missing[]]] <> "` |",
      "| Seed rule (canonical) | `" <> xpInputString[Lookup[seed, "CanonicalRule", Missing[]]] <> "` |",
      "| Seed initial state (canonical) | `" <> xpInputString[Lookup[seed, "CanonicalInitialState", Missing[]]] <> "` |",
      "| Rounds completed / mutation budget | " <> xpMarkdownCell[manifest["RoundsCompleted"] /. Null -> Missing[]] <> " / " <>
        xpMarkdownCell[config["MutationBudget"]] <> " |",
      "| Adaptive strategy weights | " <> xpMarkdownCell[config["AdaptiveWeights"]] <> " |",
      "",
      "## Strategies",
      "",
      "| Strategy | Initial weight | Final weight |",
      "|---|---|---|"
    },
    Map[
      "| " <> #["Strategy"] <> " | " <> xpMarkdownCell[#["InitialWeight"] /. Null -> Missing[]] <> " | " <>
        xpMarkdownCell[#["FinalWeight"] /. Null -> Missing[]] <> " |" &,
      manifest["Strategies"]["Weights"]
    ],
    {
      "",
      "## Outcome",
      "",
      "- Candidates: " <> ToString[Length[candidates]] <> " (" <>
        StringRiffle[KeyValueMap[ToString[#1] <> " " <> ToString[#2] &, statuses], ", "] <> ")",
      "- Search front: " <> ToString[Length[result["SearchParetoFront"]]] <> "; solution front: " <>
        ToString[Length[result["SolutionParetoFront"]]] <> "; verified solutions: " <>
        ToString[Length[manifest["Solutions"]]],
      "- Fresh evaluations: " <> xpMarkdownCell[Lookup[Lookup[result, "Performance", <||>], "FreshEvaluations", Missing[]]] <>
        "; cache hits: " <> xpMarkdownCell[Lookup[Lookup[result, "Performance", <||>], "CacheHits", Missing[]]] <>
        "; preloaded hits: " <> xpMarkdownCell[Lookup[Lookup[result, "Performance", <||>], "PreloadedHits", Missing[]]],
      ""
    },
    frontTable["Solution front", result["SolutionParetoFront"]],
    frontTable["Search front", result["SearchParetoFront"]],
    {
      "## Claim discipline",
      "",
      "- Counts are numbers of distinct states under the " <> xpStateEquivalence[result] <> " state equivalence.",
      "- \"Halted\" means verified to halt under this finite reachable exploration (the canonical state space reachable from the stated initial state was exhausted without a cycle).",
      "- GenerationCap, EventCap, StateCap and TimedOut mean not resolved within the stated limits.",
      "- \"CycleDetected\" is backed by a recorded cycle witness.",
      "- Nothing in this run concerns initial states, equivalences or limits other than the stated ones.",
      "",
      "## Files",
      "",
      "- result.wxf: complete result (WXF), SHA256 " <> manifest["WXFSHA256"] <> ", " <>
        ToString[manifest["Files"]["result.wxf"]["Bytes"]] <> " bytes",
      "- manifest.json: run manifest",
      "- summary.md: this summary",
      ""
    }
  ];

  StringRiffle[lines, "\n"]
]


(* ::Section:: *)
(*Export and import*)


ExportEvolutionResult[result_, directory_] := Module[
  {dir, wxf, manifestFile, summaryFile, hash, manifest},

  If[!xpResultQ[result], Return[xpNotResult[result]]];
  dir = xpPath[directory];
  If[!StringQ[dir], Return[xpInvalidDirectory[directory]]];
  dir = xpEnsureDirectory[dir];
  If[FailureQ[dir], Return[dir]];

  wxf = FileNameJoin[{dir, "result.wxf"}];
  manifestFile = FileNameJoin[{dir, "manifest.json"}];
  summaryFile = FileNameJoin[{dir, "summary.md"}];

  If[
    xpWriteWXF[wxf, result] === $Failed,
    Return @ Failure["WriteFailed", <|"Message" -> "result.wxf could not be written.", "File" -> wxf|>]
  ];
  hash = xpFileHash[wxf];
  manifest = xpManifest[result, hash, FileByteCount[wxf]];

  If[
    Quiet[Export[manifestFile, manifest, "RawJSON"]] === $Failed,
    Return @ Failure["WriteFailed", <|"Message" -> "manifest.json could not be written.", "File" -> manifestFile|>]
  ];
  If[
    Quiet[Export[summaryFile, xpSummaryMarkdown[result, manifest], "Text", CharacterEncoding -> "UTF8"]] === $Failed,
    Return @ Failure["WriteFailed", <|"Message" -> "summary.md could not be written.", "File" -> summaryFile|>]
  ];

  <|"Directory" -> dir, "Files" -> {wxf, manifestFile, summaryFile}, "WXFHash" -> hash|>
]


ImportEvolutionResult[directory_] := Module[
  {dir, wxf, manifestFile, manifest, expected, actual, result},

  dir = xpPath[directory];
  If[!StringQ[dir], Return[xpInvalidDirectory[directory]]];
  If[
    !DirectoryQ[dir],
    Return @ Failure["MissingRunDirectory", <|"Message" -> "The run directory does not exist.", "Directory" -> dir|>]
  ];

  wxf = FileNameJoin[{dir, "result.wxf"}];
  manifestFile = FileNameJoin[{dir, "manifest.json"}];
  If[
    !FileExistsQ[wxf] || !FileExistsQ[manifestFile],
    Return @ Failure[
      "MissingRunFile",
      <|
        "Message" -> "A run directory must contain result.wxf and manifest.json.",
        "Directory" -> dir,
        "Missing" -> Select[{wxf, manifestFile}, !FileExistsQ[#] &]
      |>
    ]
  ];

  manifest = Quiet @ Check[Import[manifestFile, "RawJSON"], $Failed];
  expected = Quiet @ Check[manifest["Files"]["result.wxf"]["SHA256"], Missing["NoHash"]];
  If[
    !AssociationQ[manifest] || !StringQ[expected],
    Return @ Failure[
      "InvalidManifest",
      <|"Message" -> "manifest.json is unreadable or records no SHA256 for result.wxf.", "File" -> manifestFile|>
    ]
  ];

  actual = xpFileHash[wxf];
  If[
    actual =!= expected,
    Return @ Failure[
      "HashMismatch",
      <|
        "Message" -> "The SHA256 hash of result.wxf does not match the hash recorded in manifest.json: the file was modified or corrupted.",
        "File" -> wxf,
        "Expected" -> expected,
        "Actual" -> actual
      |>
    ]
  ];

  result = xpReadWXF[wxf];
  If[
    !xpResultQ[result],
    Return @ Failure["UnreadableResult", <|"Message" -> "result.wxf does not contain an evolution result.", "File" -> wxf|>]
  ];
  If[
    result["RunID"] =!= Lookup[manifest, "RunID", Missing[]],
    Return @ Failure[
      "ManifestMismatch",
      <|"Message" -> "The RunID of result.wxf differs from the manifest.", "Directory" -> dir|>
    ]
  ];

  xpRebuildGraphs[result]
]


(* ::Section:: *)
(*Experiment store*)


$xpStoreFormat = "StructureAdaptiveEvolution-ExperimentStore";

$xpStoreRowFields = {
  "RunID", "CandidateID", "EvaluationID", "EvolutionKey", "ParentID", "Round", "Strategy",
  "Status", "ValidQ", "SolutionEligibleQ", "Rule", "InitialState", "FrontMembership"
};


xpStoreIndexFile[store_String] := FileNameJoin[{store, "index.wxf"}]


xpEmptyStoreIndex[] :=
  <|"Format" -> $xpStoreFormat, "FormatVersion" -> 1, "Runs" -> {}, "Candidates" -> {}|>


xpReadStoreIndex[store_String] := With[{file = xpStoreIndexFile[store]},
  If[
    !FileExistsQ[file],
    xpEmptyStoreIndex[],
    With[{index = xpReadWXF[file]},
      If[
        AssociationQ[index] && Lookup[index, "Format", None] === $xpStoreFormat,
        index,
        Failure["InvalidStoreIndex", <|"Message" -> "index.wxf is not an experiment store index.", "File" -> file|>]
      ]
    ]
  ]
]


(* Written to a temporary file and renamed, so an interrupted write never
   leaves a truncated index. *)
xpWriteStoreIndex[store_String, index_Association] := Module[{file, temporary},
  file = xpStoreIndexFile[store];
  temporary = file <> ".tmp";
  If[xpWriteWXF[temporary, index] === $Failed, Return[$Failed]];
  Quiet @ Check[RenameFile[temporary, file, OverwriteTarget -> True], $Failed]
]


xpStoreDirectory[storeDirectory_] := With[{store = xpPath[storeDirectory]},
  Which[
    !StringQ[store], xpInvalidDirectory[storeDirectory],
    !DirectoryQ[store],
      Failure["NoExperimentStore", <|"Message" -> "The experiment store directory does not exist.", "Store" -> store|>],
    True, store
  ]
]


xpStoreCandidateRow[result_Association, candidate_Association, config_Association] := <|
  "RunID" -> result["RunID"],
  "CandidateID" -> candidate["CandidateID"],
  "EvaluationID" -> Lookup[candidate, "EvaluationID", Missing["NotRecorded"]],
  "EvolutionKey" -> Lookup[candidate, "EvolutionKey", Missing["NotRecorded"]],
  "ParentID" -> Lookup[candidate, "ParentID", Missing["NotRecorded"]],
  "Round" -> Lookup[candidate, "Round", Missing["NotRecorded"]],
  "Strategy" -> Lookup[candidate, "Strategy", Missing["NotRecorded"]],
  "Status" -> Lookup[candidate, "Status", Missing["NotRecorded"]],
  "ValidQ" -> TrueQ[Lookup[candidate, "ValidQ", False]],
  "SolutionEligibleQ" -> xpSolutionQ[candidate, config],
  "Rule" -> candidate["Rule"],
  "InitialState" -> candidate["InitialState"],
  "Fitness" -> Lookup[candidate, "Fitness", <||>],
  "FrontMembership" -> Lookup[result["FrontMembership"], candidate["CandidateID"], "None"]
|>


xpStoreRunRow[result_Association, hash_String, config_Association] := Module[
  {provenance, performance, seed},
  provenance = result["Provenance"];
  performance = Lookup[result, "Performance", <||>];
  seed = result["Seed"];
  <|
    "RunID" -> result["RunID"],
    "StartTime" -> Lookup[provenance, "StartTime", Missing["NotRecorded"]],
    "EndTime" -> Lookup[provenance, "EndTime", Missing["NotRecorded"]],
    "ResumedFrom" -> Lookup[provenance, "ResumedFrom", None],
    "RandomSeed" -> Lookup[config, "RandomSeed", Missing["NotRecorded"]],
    "Goal" -> Lookup[config, "Goal", Missing["NotRecorded"]],
    "SeedRule" -> Lookup[seed, "CanonicalRule", Missing["NotRecorded"]],
    "SeedInitialState" -> Lookup[seed, "CanonicalInitialState", Missing["NotRecorded"]],
    "EdgeSymmetry" -> config["EdgeSymmetry"],
    "RewriteSemantics" -> config["RewriteSemantics"],
    "StateEquivalence" -> xpStateEquivalence[result],
    "EvolutionLimits" -> config["EvolutionLimits"],
    "RoundsCompleted" -> Lookup[Lookup[result, "ResumeState", <||>], "RoundsCompleted", Missing["NotRecorded"]],
    "MutationBudget" -> config["MutationBudget"],
    "AdaptiveWeights" -> config["AdaptiveWeights"],
    "CandidateCount" -> Length[result["Candidates"]],
    "SearchFrontSize" -> Length[result["SearchParetoFront"]],
    "SolutionFrontSize" -> Length[result["SolutionParetoFront"]],
    "SolutionCount" -> Count[result["Candidates"], _?(xpSolutionQ[#, config] &)],
    "FreshEvaluations" -> Lookup[performance, "FreshEvaluations", Missing["NotRecorded"]],
    "PreloadedHits" -> Lookup[performance, "PreloadedHits", Missing["NotRecorded"]],
    "PacletVersion" -> Lookup[provenance, "PacletVersion", Missing["NotRecorded"]],
    "EvaluatorVersion" -> Lookup[provenance, "EvaluatorVersion", Missing["NotRecorded"]],
    "Directory" -> FileNameJoin[{"runs", result["RunID"]}],
    "WXFHash" -> hash,
    "StoredAt" -> DateString["ISODateTime"]
  |>
]


Options[ExperimentStoreAdd] = {"Overwrite" -> False};

ExperimentStoreAdd[storeDirectory_, result_, OptionsPattern[]] := Module[
  {store, index, runID, runDirectory, exported, config, rows},

  If[!xpResultQ[result], Return[xpNotResult[result]]];
  store = xpPath[storeDirectory];
  If[!StringQ[store], Return[xpInvalidDirectory[storeDirectory]]];
  store = xpEnsureDirectory[store];
  If[FailureQ[store], Return[store]];

  index = xpReadStoreIndex[store];
  If[FailureQ[index], Return[index]];

  runID = result["RunID"];
  If[
    MemberQ[Lookup[index["Runs"], "RunID", {}], runID],
    If[
      TrueQ[OptionValue["Overwrite"]],
      index = Join[
        index,
        <|
          "Runs" -> Select[index["Runs"], #["RunID"] =!= runID &],
          "Candidates" -> Select[index["Candidates"], #["RunID"] =!= runID &]
        |>
      ],
      Return @ Failure[
        "RunAlreadyStored",
        <|
          "Message" -> "The store already contains this RunID; use \"Overwrite\" -> True to replace it.",
          "RunID" -> runID,
          "Store" -> store
        |>
      ]
    ]
  ];

  runDirectory = FileNameJoin[{store, "runs", runID}];
  exported = ExportEvolutionResult[result, runDirectory];
  If[FailureQ[exported], Return[exported]];

  config = result["Configuration"];
  rows = xpStoreCandidateRow[result, #, config] & /@ result["Candidates"];
  index = Join[
    index,
    <|
      "Runs" -> Append[index["Runs"], xpStoreRunRow[result, exported["WXFHash"], config]],
      "Candidates" -> Join[index["Candidates"], rows]
    |>
  ];
  If[
    xpWriteStoreIndex[store, index] === $Failed,
    Return @ Failure["WriteFailed", <|"Message" -> "index.wxf could not be written.", "Store" -> store|>]
  ];

  <|
    "Store" -> store,
    "RunID" -> runID,
    "Directory" -> runDirectory,
    "RowsAdded" -> Length[rows],
    "WXFHash" -> exported["WXFHash"]
  |>
]


ExperimentStoreRuns[storeDirectory_] := Module[{store, index},
  store = xpStoreDirectory[storeDirectory];
  If[FailureQ[store], Return[store]];
  index = xpReadStoreIndex[store];
  If[FailureQ[index], index, Dataset[index["Runs"]]]
]


xpRangeSpecificationQ[{low_, high_}] :=
  (NumericQ[low] || low === -Infinity) && (NumericQ[high] || high === Infinity)
xpRangeSpecificationQ[_] := False


xpValueMatchQ[value_, specification_List] /; !ListQ[value] := MemberQ[specification, value]
xpValueMatchQ[value_, specification_] := MatchQ[value, specification]


(* Row fields match by value, by membership in a list of values, or by
   pattern; any other key names a metric: {min, max} selects numeric values
   in the closed range, anything else matches the value. *)
xpCriterionQ[row_Association, key_, specification_] :=
  If[
    MemberQ[$xpStoreRowFields, key],
    xpValueMatchQ[Lookup[row, key, Missing["KeyAbsent", key]], specification],
    With[{value = Lookup[Lookup[row, "Fitness", <||>], key, Missing["NotComputed"]]},
      If[
        xpRangeSpecificationQ[specification],
        NumericQ[value] && TrueQ[specification[[1]] <= value <= specification[[2]]],
        xpValueMatchQ[value, specification]
      ]
    ]
  ]


ExperimentStoreQuery[storeDirectory_] := ExperimentStoreQuery[storeDirectory, <||>]

ExperimentStoreQuery[storeDirectory_, filter_] := Module[{store, index, predicate},
  store = xpStoreDirectory[storeDirectory];
  If[FailureQ[store], Return[store]];
  index = xpReadStoreIndex[store];
  If[FailureQ[index], Return[index]];
  predicate = Which[
    AssociationQ[filter],
      Function[row, AllTrue[Normal[filter], xpCriterionQ[row, First[#], Last[#]] &]],
    MatchQ[filter, _Function],
      filter,
    True,
      Return @ Failure[
        "InvalidFilter",
        <|"Message" -> "The filter must be a Function or an Association of criteria.", "Filter" -> filter|>
      ]
  ];
  Dataset @ Select[index["Candidates"], TrueQ[Quiet[predicate[#]]] &]
]


ExperimentStoreLoad[storeDirectory_, runID_String] := Module[{store, index},
  store = xpStoreDirectory[storeDirectory];
  If[FailureQ[store], Return[store]];
  index = xpReadStoreIndex[store];
  If[FailureQ[index], Return[index]];
  If[
    !MemberQ[Lookup[index["Runs"], "RunID", {}], runID],
    Return @ Failure[
      "UnknownRun",
      <|"Message" -> "The store contains no run with this RunID.", "RunID" -> runID, "Store" -> store|>
    ]
  ];
  ImportEvolutionResult[FileNameJoin[{store, "runs", runID}]]
]


(* Every stored run is re-imported (and so hash-verified) before any of its
   behaviors is offered for reuse; a store with an unreadable run preloads
   nothing. *)
ExperimentStorePreload[storeDirectory_] := Module[{store, index, imported, failures, behaviors},
  store = xpStoreDirectory[storeDirectory];
  If[FailureQ[store], Return[store]];
  index = xpReadStoreIndex[store];
  If[FailureQ[index], Return[index]];

  imported = AssociationMap[
    ImportEvolutionResult[FileNameJoin[{store, "runs", #}]] &,
    Lookup[index["Runs"], "RunID", {}]
  ];
  failures = Select[imported, FailureQ];
  If[
    failures =!= <||>,
    Return @ Failure[
      "StoreRunUnreadable",
      <|
        "Message" -> "One or more stored runs failed verification; nothing was preloaded.",
        "Runs" -> Keys[failures],
        "Failures" -> Values[failures]
      |>
    ]
  ];

  behaviors = Association @ Catenate @ Map[
    Function[result,
      Map[
        #["EvaluationID"] -> # &,
        Select[
          result["Candidates"],
          StringQ[Lookup[#, "EvaluationID", None]] && Lookup[#, "Status", "TimedOut"] =!= "TimedOut" &
        ]
      ]
    ],
    Values[imported]
  ];

  preloadEvaluations[behaviors]
]


(* ::Section:: *)
(*Wilson score interval*)


WilsonInterval[successes_Integer?NonNegative, trials_Integer?NonNegative, level_ : 0.95] /;
  successes <= trials && NumericQ[level] && TrueQ[0 < level < 1] :=
  If[
    trials === 0,
    {0., 1.},
    Module[{z, p, n = trials, denominator, center, half},
      z = N @ InverseCDF[NormalDistribution[0, 1], 1 - (1 - level)/2];
      p = N[successes/n];
      denominator = 1 + z^2/n;
      center = (p + z^2/(2 n))/denominator;
      half = z Sqrt[p (1 - p)/n + z^2/(4 n^2)]/denominator;
      (* The bounds at 0 and n successes are exactly 0 and 1; the general
         formula reaches them only up to rounding. *)
      {
        If[successes === 0, 0., Max[0., center - half]],
        If[successes === n, 1., Min[1., center + half]]
      }
    ]
  ]

WilsonInterval[arguments___] :=
  Failure[
    "InvalidArguments",
    <|
      "Message" -> "WilsonInterval[successes, trials, level] needs integers 0 <= successes <= trials and 0 < level < 1.",
      "Arguments" -> {arguments}
    |>
  ]


(* ::Section:: *)
(*Multi-seed replication*)


$xpReportMetrics = {
  "MultiwayStateCount", "MultiwayTransitionCount", "MultiwayLongestDerivation", "HGMaxVerticesCount"
};


xpOptionListQ[options_List] := MatchQ[options, {(_Rule | _RuleDelayed) ...}]
xpOptionListQ[_] := False


(* First occurrence wins, exactly like OptionValue. *)
xpNormalizeOptions[options_List] := Normal @ Association @ Reverse[options]


xpWithoutOptions[options_List, names_List] :=
  DeleteCases[options, (Rule | RuleDelayed)[Alternatives @@ names, _]]


xpRunFailure[result_] :=
  If[
    FailureQ[result],
    result,
    Failure[
      "RunFailed",
      <|"Message" -> "StructureAdaptiveEvolution did not return a result.", "Head" -> Head[result]|>
    ]
  ]


xpReplicateRunSummary[seed_, wallTime_, result_, metrics_List] :=
  If[
    xpResultQ[result],
    Module[{config, solutions},
      config = result["Configuration"];
      solutions = Select[result["Candidates"], xpSolutionQ[#, config] &];
      <|
        "RunID" -> result["RunID"],
        "Seed" -> seed,
        "SuccessQ" -> solutions =!= {},
        "SolutionCount" -> Length[solutions],
        "SolutionFrontSize" -> Length[result["SolutionParetoFront"]],
        "BestValues" -> AssociationMap[xpBestValue[solutions, #, config, "NoVerifiedSolution"] &, metrics],
        "Evaluations" -> Length[result["Candidates"]],
        "FreshEvaluations" -> Lookup[Lookup[result, "Performance", <||>], "FreshEvaluations", Missing["NotRecorded"]],
        "WallTime" -> wallTime,
        "Failure" -> None
      |>
    ],
    <|
      "RunID" -> Missing["RunFailed"],
      "Seed" -> seed,
      "SuccessQ" -> False,
      "SolutionCount" -> 0,
      "SolutionFrontSize" -> 0,
      "BestValues" -> AssociationMap[Missing["RunFailed"] &, metrics],
      "Evaluations" -> 0,
      "FreshEvaluations" -> 0,
      "WallTime" -> wallTime,
      "Failure" -> xpRunFailure[result]
    |>
  ]


xpQuantileSummary[values_List] :=
  With[{numeric = Select[values, NumericQ]},
    <|
      "Values" -> values,
      "Count" -> Length[numeric],
      "Quantiles" -> If[
        numeric === {},
        Missing["NoValues"],
        With[{quartiles = N @ Quartiles[numeric]},
          <|
            "Minimum" -> Min[numeric],
            "LowerQuartile" -> quartiles[[1]],
            "Median" -> quartiles[[2]],
            "UpperQuartile" -> quartiles[[3]],
            "Maximum" -> Max[numeric]
          |>
        ]
      ]
    |>
  ]


Options[ReplicateEvolution] = {"Metrics" -> $xpReportMetrics, "ConfidenceLevel" -> 0.95};

ReplicateEvolution[options_List, seeds_List, OptionsPattern[]] := Module[
  {metrics, level, baseOptions, runs, summaries, successes, trials},

  If[
    !xpOptionListQ[options],
    Return @ Failure["InvalidOptions", <|"Message" -> "The options must be a list of rules.", "Options" -> options|>]
  ];
  If[
    seeds === {} || !AllTrue[seeds, IntegerQ],
    Return @ Failure["InvalidSeeds", <|"Message" -> "The seeds must be a nonempty list of integers.", "Seeds" -> seeds|>]
  ];
  metrics = OptionValue["Metrics"];
  level = OptionValue["ConfidenceLevel"];
  baseOptions = xpWithoutOptions[xpNormalizeOptions[options], {"RandomSeed"}];

  runs = Map[
    Function[seed,
      Module[{wallTime, result},
        {wallTime, result} = AbsoluteTiming[
          StructureAdaptiveEvolution[Sequence @@ baseOptions, "RandomSeed" -> seed]
        ];
        <|"Seed" -> seed, "WallTime" -> wallTime, "Result" -> result|>
      ]
    ],
    seeds
  ];

  summaries = xpReplicateRunSummary[#["Seed"], #["WallTime"], #["Result"], metrics] & /@ runs;
  successes = Count[summaries, _?(TrueQ[#["SuccessQ"]] &)];
  trials = Length[summaries];

  <|
    "Runs" -> summaries,
    "SuccessFraction" -> <|
      "Fraction" -> N[successes/trials],
      "Successes" -> successes,
      "Trials" -> trials,
      "WilsonInterval" -> WilsonInterval[successes, trials, level],
      "ConfidenceLevel" -> level,
      "Definition" -> "Runs with at least one verified solution (Halted, at least one transition, every constraint satisfied); failed runs count as runs without a solution."
    |>,
    "Distributions" -> AssociationMap[
      xpQuantileSummary[Lookup[Lookup[summaries, "BestValues"], #, Missing["NotComputed"]]] &,
      metrics
    ],
    "Metrics" -> metrics,
    "Seeds" -> seeds,
    "FailedRuns" -> Count[summaries, _?(#["Failure"] =!= None &)],
    "Results" -> Lookup[runs, "Result"]
  |>
]


(* ::Section:: *)
(*Budget-matched baselines*)


$xpBaselineMethods = {"Guided", "Random", "Exhaustive"};


xpSearchRunRow[run_Association] := Module[{result, config, candidates, flags, first, performance},
  result = run["Result"];
  If[
    !xpResultQ[result],
    Return @ <|
      "Seed" -> run["Seed"],
      "RunID" -> Missing["RunFailed"],
      "SuccessQ" -> False,
      "SolutionCount" -> 0,
      "EvaluationsToFirstSolution" -> Missing["RunFailed"],
      "Evaluations" -> 0,
      "FreshEvaluations" -> 0,
      "EvolutionTime" -> 0.,
      "WallTime" -> run["WallTime"],
      "Solutions" -> {},
      "Failure" -> xpRunFailure[result]
    |>
  ];
  config = result["Configuration"];
  candidates = result["Candidates"];
  flags = xpSolutionQ[#, config] & /@ candidates;
  first = FirstPosition[flags, True, {Missing["NoVerifiedSolution"]}, {1}][[1]];
  performance = Lookup[result, "Performance", <||>];
  <|
    "Seed" -> run["Seed"],
    "RunID" -> result["RunID"],
    "SuccessQ" -> MemberQ[flags, True],
    "SolutionCount" -> Count[flags, True],
    "EvaluationsToFirstSolution" -> first,
    "Evaluations" -> Length[candidates],
    "FreshEvaluations" -> Lookup[performance, "FreshEvaluations", 0],
    "EvolutionTime" -> Lookup[performance, "EvolutionTime", 0.],
    "WallTime" -> run["WallTime"],
    "Solutions" -> Pick[candidates, flags],
    "Failure" -> None
  |>
]


xpClaimPrefix[context_Association] :=
  "Under signature " <> xpSignatureString[context["Signature"]] <>
    ", initial state " <> xpInputString[context["InitialState"]] <>
    ", equivalence " <> context["StateEquivalence"] <>
    " and limits " <> xpLimitsString[context["EvolutionLimits"]] <> ", "


$xpClaimSuffix =
  " A verified solution halted (its finite reachable canonical state space was exhausted without a cycle), made at least one transition and satisfied every constraint; nothing is claimed for other initial states, equivalences or limits.";


xpPercentString[level_] :=
  With[{percent = 100 level},
    If[TrueQ[Abs[percent - Round[percent]] < 10^-9], ToString[Round[percent]], xpValueString[N[percent]]]
  ]


(* Fixed text for claims: three decimals, integers without a decimal point. *)
xpClaimNumber[value_?NumericQ] :=
  Which[
    IntegerQ[value], ToString[value],
    TrueQ[Abs[value - Round[value]] < 10^-9], ToString[Round[value]],
    True, With[{text = ToString[N[Round[1000 value]/1000], InputForm]}, If[StringEndsQ[text, "."], text <> "0", text]]
  ]
xpClaimNumber[other_] := xpValueString[other]


xpIntervalString[{low_, high_}] := "[" <> xpClaimNumber[low] <> ", " <> xpClaimNumber[high] <> "]"
xpIntervalString[other_] := xpValueString[other]


xpMethodSummary[method_String, description_String, rows_List, context_Association] := Module[
  {config, level, successes, trials, firsts, solutions, objectives, interval, median, claim, evaluations},

  config = context["Configuration"];
  level = context["ConfidenceLevel"];
  successes = Count[rows, _?(TrueQ[#["SuccessQ"]] &)];
  trials = Length[rows];
  firsts = Lookup[rows, "EvaluationsToFirstSolution", {}];
  solutions = Catenate[Lookup[rows, "Solutions", {}]];
  objectives = Keys @ Select[xpMetricSpecifications[config], Lookup[#, "Stage", "Objective"] === "Objective" &];
  interval = WilsonInterval[successes, trials, level];
  median = With[{numeric = Select[firsts, NumericQ]},
    If[numeric === {}, Missing["NoVerifiedSolution"], N @ Median[numeric]]
  ];
  evaluations = Lookup[rows, "Evaluations", {}];

  claim = xpClaimPrefix[context] <> description <> " " <>
    If[
      successes === 0,
      "found no verified solution in any of " <> ToString[trials] <> " run(s)",
      "found at least one verified solution in " <> ToString[successes] <> " of " <> ToString[trials] <> " run(s)"
    ] <>
    " (" <> xpPercentString[level] <> "% Wilson interval " <> xpIntervalString[interval] <> ")" <>
    " with a budget of at most " <> ToString[context["Budget"]] <> " evaluations per run (" <>
    ToString[Total[evaluations]] <> " evaluations in total)" <>
    If[
      MissingQ[median],
      ".",
      "; median evaluations to the first verified solution among successful runs: " <> xpClaimNumber[median] <> "."
    ] <>
    $xpClaimSuffix;

  <|
    "Method" -> method,
    "Description" -> description,
    "Runs" -> trials,
    "SuccessRate" -> <|
      "Successes" -> successes,
      "Trials" -> trials,
      "Fraction" -> If[trials > 0, N[successes/trials], Missing["NoRuns"]],
      "WilsonInterval" -> interval,
      "ConfidenceLevel" -> level
    |>,
    "EvaluationsToFirstSolution" -> <|"PerRun" -> firsts, "Median" -> median|>,
    "SolutionCounts" -> Lookup[rows, "SolutionCount", {}],
    "BestObjectiveValues" -> AssociationMap[xpBestValue[solutions, #, config, "NoVerifiedSolution"] &, objectives],
    "ComputeCost" -> <|
      "Evaluations" -> Total[evaluations],
      "FreshEvaluations" -> Total[Lookup[rows, "FreshEvaluations", {}]],
      "EvolutionTime" -> Total[Lookup[rows, "EvolutionTime", {}]],
      "WallTime" -> Total[Lookup[rows, "WallTime", {}]]
    |>,
    "EvaluationsPerRun" -> evaluations,
    "Budget" -> context["Budget"],
    "PerRun" -> (KeyDrop[#, "Solutions"] & /@ rows),
    "Claim" -> claim
  |>
]


(* Canonical rules of a signature in enumeration order, deduplicated under
   the configuration's universe, the first `budget` of them evaluated on the
   seed's canonical initial state with the run's limits and metrics. *)
xpExhaustiveArm[config_Association, seed_Association, signature_Rule, maxRules_, budget_Integer] :=
  withConfigUniverse[
    config,
    Module[{enumerated, truncatedQ, canonical, selected, state, candidates, statistics, wallTime},
      enumerated = Quiet @ Check[EnumerateWolframModelRules[signature], $Failed];
      If[
        !MatchQ[enumerated, {___Rule}],
        Return @ Failure[
          "EnumerationFailed",
          <|"Message" -> "EnumerateWolframModelRules could not enumerate the signature.", "Signature" -> signature|>
        ]
      ];
      truncatedQ = Length[enumerated] > maxRules;
      enumerated = Take[enumerated, UpTo[maxRules]];
      canonical = DeleteDuplicates @ Select[CanonicalRuleForm /@ enumerated, !FailureQ[#] &];
      selected = Take[canonical, UpTo[budget]];
      state = seed["InitialState"];

      If[!TrueQ[config["ReuseEvaluations"]], ClearEvaluationCache[]];
      Block[
        {
          $evaluationStatistics = <|
            "FreshEvolutions" -> 0, "CacheHits" -> 0, "ParallelEvaluations" -> 0,
            "PreloadedHits" -> 0, "EvolutionTime" -> 0.
          |>,
          $PreloadedEvaluations = If[TrueQ[config["ReuseEvaluations"]], $PreloadedEvaluations, <||>]
        },
        {wallTime, candidates} = AbsoluteTiming @ MapIndexed[
          EvaluateCandidate[
            <|
              "CandidateID" -> CandidateIDFromForms[#1, state],
              "ParentID" -> Missing["Enumeration"],
              "Round" -> 0,
              "Trial" -> First[#2],
              "Strategy" -> "Exhaustive",
              "Rule" -> #1,
              "InitialState" -> state,
              "Provenance" -> <|"Strategy" -> "Exhaustive", "Signature" -> signature, "CanonicalIndex" -> First[#2]|>
            |>,
            config
          ] &,
          selected
        ];
        statistics = $evaluationStatistics
      ];

      <|
        "Candidates" -> candidates,
        "EnumeratedRules" -> Length[enumerated],
        "EnumerationTruncatedQ" -> truncatedQ,
        "CanonicalRules" -> Length[canonical],
        "Evaluated" -> Length[selected],
        "CompleteQ" -> !truncatedQ && Length[selected] === Length[canonical],
        "FreshEvaluations" -> statistics["FreshEvolutions"],
        "EvolutionTime" -> statistics["EvolutionTime"],
        "WallTime" -> wallTime
      |>
    ]
  ]


xpExhaustiveSummary[arm_Association, context_Association] := Module[
  {config, level, candidates, flags, successes, first, solutions, objectives, interval, claim},

  config = context["Configuration"];
  level = context["ConfidenceLevel"];
  candidates = arm["Candidates"];
  flags = xpSolutionQ[#, config] & /@ candidates;
  successes = Boole[MemberQ[flags, True]];
  first = FirstPosition[flags, True, {Missing["NoVerifiedSolution"]}, {1}][[1]];
  solutions = Pick[candidates, flags];
  objectives = Keys @ Select[xpMetricSpecifications[config], Lookup[#, "Stage", "Objective"] === "Objective" &];
  interval = WilsonInterval[successes, 1, level];

  claim = xpClaimPrefix[context] <>
    "enumerating the signature gave " <> ToString[arm["CanonicalRules"]] <> " canonical rule(s) from " <>
    ToString[arm["EnumeratedRules"]] <> " enumerated rule(s)" <>
    If[arm["EnumerationTruncatedQ"], " (enumeration truncated at MaxExhaustiveRules)", ""] <>
    "; " <> ToString[arm["Evaluated"]] <> " were evaluated (budget " <> ToString[context["Budget"]] <> ", " <>
    If[arm["CompleteQ"], "complete coverage of the signature", "incomplete coverage"] <> ") and " <>
    ToString[Length[solutions]] <> " were verified solutions" <>
    If[MissingQ[first], ".", ", the first at evaluation " <> ToString[first] <> "."] <>
    $xpClaimSuffix;

  <|
    "Method" -> "Exhaustive",
    "Description" -> "canonical rules of the signature in enumeration order",
    "Runs" -> 1,
    "SuccessRate" -> <|
      "Successes" -> successes,
      "Trials" -> 1,
      "Fraction" -> N[successes],
      "WilsonInterval" -> interval,
      "ConfidenceLevel" -> level
    |>,
    "EvaluationsToFirstSolution" -> <|"PerRun" -> {first}, "Median" -> If[MissingQ[first], first, N[first]]|>,
    "SolutionCounts" -> {Length[solutions]},
    "BestObjectiveValues" -> AssociationMap[xpBestValue[solutions, #, config, "NoVerifiedSolution"] &, objectives],
    "ComputeCost" -> <|
      "Evaluations" -> Length[candidates],
      "FreshEvaluations" -> arm["FreshEvaluations"],
      "EvolutionTime" -> arm["EvolutionTime"],
      "WallTime" -> arm["WallTime"]
    |>,
    "EvaluationsPerRun" -> {Length[candidates]},
    "Budget" -> context["Budget"],
    "Coverage" -> KeyTake[arm, {"EnumeratedRules", "EnumerationTruncatedQ", "CanonicalRules", "Evaluated", "CompleteQ"}],
    "Claim" -> claim
  |>
]


BaselineComparison[options_List, specification_Association] := Module[
  {
    seeds, level, methods, maxRules, baseOptions, config, seed, budget, signature,
    context, searchRuns, summaries = <||>, results = <||>, arm
  },

  If[
    !xpOptionListQ[options],
    Return @ Failure["InvalidOptions", <|"Message" -> "The options must be a list of rules.", "Options" -> options|>]
  ];
  seeds = Lookup[specification, "Seeds", {1, 2, 3}];
  If[
    !MatchQ[seeds, {__Integer}],
    Return @ Failure["InvalidSeeds", <|"Message" -> "\"Seeds\" must be a nonempty list of integers.", "Seeds" -> seeds|>]
  ];
  level = Lookup[specification, "ConfidenceLevel", 0.95];
  methods = Lookup[specification, "Methods", $xpBaselineMethods];
  If[
    !SubsetQ[$xpBaselineMethods, methods],
    Return @ Failure[
      "InvalidMethods",
      <|"Message" -> "\"Methods\" must be a subset of {\"Guided\", \"Random\", \"Exhaustive\"}.", "Methods" -> methods|>
    ]
  ];
  maxRules = Lookup[specification, "MaxExhaustiveRules", 10000];
  If[
    !(maxRules === Infinity || (IntegerQ[maxRules] && Positive[maxRules])),
    Return @ Failure[
      "InvalidMaxExhaustiveRules",
      <|"Message" -> "\"MaxExhaustiveRules\" must be a positive integer or Infinity.", "Value" -> maxRules|>
    ]
  ];

  baseOptions = xpWithoutOptions[
    xpNormalizeOptions[options],
    {"RandomSeed", "AdaptiveWeights", "InitialStateDiagnostics", "ResumeFrom"}
  ];
  config = ValidateEvolutionConfiguration[
    Association[Join[baseOptions, {"InitialStateDiagnostics" -> None, "RandomSeed" -> First[seeds]}]]
  ];
  If[FailureQ[config], Return[config]];

  (* Every method starts from one resolved seed: the same canonical rule and
     initial state, also when the rule or state is Automatic. *)
  seed = BlockRandom[SeedRandom[First[seeds]]; ResolveAndCanonicalizeSeed[config]];
  If[FailureQ[seed], Return[seed]];
  baseOptions = Join[
    xpWithoutOptions[baseOptions, {"Rule", "InitialState"}],
    {"Rule" -> seed["OriginalRule"], "InitialState" -> seed["OriginalInitialState"]}
  ];

  budget = 1 + config["Rounds"] config["MutationBudget"];
  signature = Replace[
    Lookup[specification, "Signature", Automatic],
    Automatic :> xpRuleSignature[seed["CanonicalRule"]]
  ];

  context = <|
    "Configuration" -> config,
    "ConfidenceLevel" -> level,
    "Budget" -> budget,
    "Signature" -> signature,
    "InitialState" -> seed["InitialState"],
    "StateEquivalence" -> stateEquivalenceTag[config],
    "EvolutionLimits" -> config["EvolutionLimits"]
  |>;

  searchRuns[adaptive_] := Map[
    Function[randomSeed,
      Module[{wallTime, result},
        {wallTime, result} = AbsoluteTiming[
          StructureAdaptiveEvolution[
            Sequence @@ baseOptions,
            "AdaptiveWeights" -> adaptive,
            "InitialStateDiagnostics" -> None,
            "RandomSeed" -> randomSeed
          ]
        ];
        <|"Seed" -> randomSeed, "WallTime" -> wallTime, "Result" -> result|>
      ]
    ],
    seeds
  ];

  If[
    MemberQ[methods, "Guided"],
    With[{runs = searchRuns[True]},
      results["Guided"] = Lookup[runs, "Result"];
      summaries["Guided"] = xpMethodSummary[
        "Guided",
        "guided search (adaptive strategy weights; mutation may leave the seed signature)",
        xpSearchRunRow /@ runs,
        context
      ]
    ]
  ];

  If[
    MemberQ[methods, "Random"],
    With[{runs = searchRuns[False]},
      results["Random"] = Lookup[runs, "Result"];
      summaries["Random"] = xpMethodSummary[
        "Random",
        "random-mutation search (fixed uniform weights over the same strategies; mutation may leave the seed signature)",
        xpSearchRunRow /@ runs,
        context
      ]
    ]
  ];

  If[
    MemberQ[methods, "Exhaustive"],
    If[
      !MatchQ[signature, _Rule],
      summaries["Exhaustive"] = <|
        "Method" -> "Exhaustive",
        "Skipped" -> True,
        "Reason" -> "No signature: the seed is a rule set; give \"Signature\" explicitly.",
        "Claim" -> Missing["NotRun"]
      |>,
      arm = xpExhaustiveArm[config, seed, signature, maxRules, budget];
      If[
        FailureQ[arm],
        summaries["Exhaustive"] = <|
          "Method" -> "Exhaustive", "Skipped" -> True, "Reason" -> arm, "Claim" -> Missing["NotRun"]
        |>,
        results["Exhaustive"] = arm["Candidates"];
        summaries["Exhaustive"] = xpExhaustiveSummary[arm, context]
      ]
    ]
  ];

  <|
    "Budget" -> budget,
    "Seeds" -> seeds,
    "Signature" -> signature,
    "InitialState" -> seed["InitialState"],
    "Rule" -> seed["Rule"],
    "StateEquivalence" -> context["StateEquivalence"],
    "EvolutionLimits" -> config["EvolutionLimits"],
    "Methods" -> summaries,
    "Results" -> results
  |>
]


(* ::Section:: *)
(*Robustness and cap sensitivity*)


Options[CandidateRobustness] = {
  "CapFactors" -> {2, 4},
  "InitialStates" -> Automatic,
  "EnsembleSize" -> 8,
  "RandomSeed" -> Automatic,
  "RewriteSemantics" -> True,
  "ConfidenceLevel" -> 0.95
};


xpScaledLimits[limits_Association, factor_] :=
  Association @ KeyValueMap[
    Function[{name, value},
      name -> Which[
        value === Infinity, Infinity,
        name === "TimeConstraint", N[factor value],
        IntegerQ[value], Ceiling[factor value],
        NumericQ[value], N[factor value],
        True, value
      ]
    ],
    limits
  ]


xpEvaluateVariant[rule_, state_, config_Association] :=
  EvaluateCandidate[
    <|"CandidateID" -> CandidateIDFromForms[rule, state], "Rule" -> rule, "InitialState" -> state|>,
    config
  ]


xpCapSensitivity[candidate_Association, config_Association, factors_List] :=
  Map[
    Function[factor,
      Module[{limits, evaluated},
        limits = xpScaledLimits[config["EvolutionLimits"], factor];
        evaluated = xpEvaluateVariant[
          candidate["Rule"], candidate["InitialState"], Append[config, "EvolutionLimits" -> limits]
        ];
        <|
          "Factor" -> factor,
          "EvolutionLimits" -> limits,
          "Status" -> evaluated["Status"],
          "StateCount" -> Length[evaluated["States"]],
          "TransitionCount" -> evaluated["TransitionCount"],
          "EventCount" -> evaluated["EventCount"],
          "LimitsReached" -> evaluated["LimitsReached"],
          "CycleWitnessRecordedQ" -> xpCycleWitnessQ[evaluated],
          "StatusChangedQ" -> evaluated["Status"] =!= candidate["Status"]
        |>
      ]
    ],
    factors
  ]


(* Diagnostic initial states: a seeded random ensemble with the seed state's
   edge signature (DiagnosticInitialStateEnsemble), or a user list,
   canonicalized and deduplicated under the run's universe. *)
xpRobustnessStates[result_Association, Automatic, size_, randomSeedOption_] := Module[
  {config = result["Configuration"], randomSeed},
  randomSeed = Replace[
    randomSeedOption,
    Automatic :> Replace[config["RandomSeed"], Except[_Integer] -> 0]
  ];
  If[
    !IntegerQ[randomSeed] || !(IntegerQ[size] && Positive[size]),
    Return @ Failure[
      "InvalidRobustnessOptions",
      <|"Message" -> "\"EnsembleSize\" must be a positive integer and \"RandomSeed\" an integer or Automatic.", "EnsembleSize" -> size, "RandomSeed" -> randomSeedOption|>
    ]
  ];
  <|
    "Source" -> "DiagnosticInitialStateEnsemble",
    "RandomSeed" -> randomSeed,
    "RequestedSize" -> size,
    "States" -> BlockRandom[
      SeedRandom[randomSeed];
      withConfigUniverse[config, DiagnosticInitialStateEnsemble[result["Seed"]["InitialState"], size]]
    ]
  |>
]

xpRobustnessStates[result_Association, states_List, _, _] :=
  If[
    AllTrue[states, TrueQ[hypergraphStateQ[#]] &],
    <|
      "Source" -> "User",
      "RandomSeed" -> Missing["NotApplicable"],
      "RequestedSize" -> Length[states],
      "States" -> withConfigUniverse[result["Configuration"], DeleteDuplicates[CanonicalStateForm /@ states]]
    |>,
    Failure[
      "InvalidInitialStates",
      <|"Message" -> "\"InitialStates\" must be Automatic or a list of hypergraph states.", "InitialStates" -> states|>
    ]
  ]

xpRobustnessStates[_, other_, _, _] :=
  Failure[
    "InvalidInitialStates",
    <|"Message" -> "\"InitialStates\" must be Automatic or a nonempty list of hypergraph states.", "InitialStates" -> other|>
  ]


xpInitialStateCorpus[candidate_Association, config_Association, corpus_Association, level_] := Module[
  {perState, applicable, halted},
  perState = Map[
    Function[state,
      Module[{applicableQ, evaluated},
        applicableQ = TrueQ[withConfigUniverse[config, RuleApplicableQ[candidate["Rule"], state]]];
        evaluated = If[applicableQ, xpEvaluateVariant[candidate["Rule"], state, config], Missing["NotApplicable"]];
        <|
          "InitialState" -> state,
          "ApplicableQ" -> applicableQ,
          "Status" -> If[MissingQ[evaluated], "NotApplicable", evaluated["Status"]],
          "StateCount" -> If[MissingQ[evaluated], Missing["NotApplicable"], Length[evaluated["States"]]],
          "TransitionCount" -> If[MissingQ[evaluated], Missing["NotApplicable"], evaluated["TransitionCount"]]
        |>
      ]
    ],
    corpus["States"]
  ];
  applicable = Select[perState, #["ApplicableQ"] &];
  halted = Count[applicable, _?(#["Status"] === "Halted" &)];
  <|
    "Source" -> corpus["Source"],
    "RandomSeed" -> corpus["RandomSeed"],
    "RequestedSize" -> corpus["RequestedSize"],
    "StatesTested" -> Length[perState],
    "ApplicableCount" -> Length[applicable],
    "HaltedCount" -> halted,
    "TerminationRate" -> If[applicable === {}, Missing["NoApplicableStates"], N[halted/Length[applicable]]],
    "TerminationWilsonInterval" -> If[
      applicable === {},
      Missing["NoApplicableStates"],
      WilsonInterval[halted, Length[applicable], level]
    ],
    "StatusCounts" -> Counts[Lookup[perState, "Status", {}]],
    "StateCountDistribution" -> xpDistributionSummary[Lookup[applicable, "StateCount", {}]],
    "PerState" -> perState
  |>
]


xpSemanticsCheck[candidate_Association, config_Association] := Module[{base, alternative, evaluated},
  base = config["RewriteSemantics"];
  alternative = If[base === "EdgeToken", "VertexDeletion", "EdgeToken"];
  evaluated = xpEvaluateVariant[
    candidate["Rule"], candidate["InitialState"], Append[config, "RewriteSemantics" -> alternative]
  ];
  <|
    "Base" -> base,
    "BaseStatus" -> candidate["Status"],
    "BaseStateCount" -> Length[Lookup[candidate, "States", {}]],
    "Alternative" -> alternative,
    "AlternativeStatus" -> evaluated["Status"],
    "AlternativeStateCount" -> Length[evaluated["States"]],
    "StatusChangedQ" -> evaluated["Status"] =!= candidate["Status"]
  |>
]


xpRobustnessText[status_, capRows_, corpus_, semantics_] :=
  StringRiffle[
    {
      If[
        capRows === {},
        "cap sensitivity not tested",
        If[
          AnyTrue[capRows, #["StatusChangedQ"] &],
          "cap-sensitive: status " <> xpValueString[status] <> " became " <>
            StringRiffle[(xpValueString[#["Status"]] <> " at factor " <> xpValueString[#["Factor"]]) & /@ capRows, ", "],
          "status " <> xpValueString[status] <> " unchanged at limit factors " <> xpInputString[Lookup[capRows, "Factor"]]
        ]
      ],
      If[
        corpus["StatesTested"] === 0,
        "no alternative initial states tested",
        "halted on " <> ToString[corpus["HaltedCount"]] <> " of " <> ToString[corpus["ApplicableCount"]] <>
          " applicable alternative initial state(s) (" <> ToString[corpus["StatesTested"]] <> " tested; these states only)"
      ],
      If[
        AssociationQ[semantics],
        semantics["Alternative"] <> " semantics: " <> semantics["AlternativeStatus"],
        "rewrite semantics not compared"
      ]
    },
    "; "
  ]


CandidateRobustness[result_, candidateID_, opts : OptionsPattern[]] := Module[
  {config, candidate, factors, corpus, capRows, corpusSummary, semantics, level},

  If[!xpResultQ[result], Return[xpNotResult[result]]];
  candidate = xpFindCandidate[result, candidateID];
  If[MissingQ[candidate], Return[xpUnknownCandidate[candidateID]]];
  config = result["Configuration"];
  level = OptionValue["ConfidenceLevel"];

  factors = OptionValue["CapFactors"];
  If[
    !MatchQ[factors, {___?(NumericQ[#] && TrueQ[# > 0] &)}],
    Return @ Failure["InvalidCapFactors", <|"Message" -> "\"CapFactors\" must be a list of positive numbers.", "CapFactors" -> factors|>]
  ];

  corpus = xpRobustnessStates[result, OptionValue["InitialStates"], OptionValue["EnsembleSize"], OptionValue["RandomSeed"]];
  If[FailureQ[corpus], Return[corpus]];

  capRows = xpCapSensitivity[candidate, config, factors];
  corpusSummary = xpInitialStateCorpus[candidate, config, corpus, level];
  semantics = If[TrueQ[OptionValue["RewriteSemantics"]], xpSemanticsCheck[candidate, config], Missing["NotRequested"]];

  <|
    "CandidateID" -> candidateID,
    "Rule" -> candidate["Rule"],
    "InitialState" -> candidate["InitialState"],
    "BaseStatus" -> candidate["Status"],
    "BaseEvolutionLimits" -> config["EvolutionLimits"],
    "StateEquivalence" -> xpStateEquivalence[result],
    "CapSensitivity" -> <|
      "Factors" -> factors,
      "Evaluations" -> capRows,
      "StatusChangedQ" -> AnyTrue[capRows, #["StatusChangedQ"] &]
    |>,
    "InitialStateCorpus" -> corpusSummary,
    "RewriteSemantics" -> semantics,
    "CapSensitiveQ" -> AnyTrue[capRows, #["StatusChangedQ"] &],
    "SemanticsSensitiveQ" -> If[AssociationQ[semantics], semantics["StatusChangedQ"], Missing["NotRequested"]],
    "Summary" -> xpRobustnessText[candidate["Status"], capRows, corpusSummary, semantics]
  |>
]


RobustnessReport[result_, opts : OptionsPattern[CandidateRobustness]] := Module[
  {source, finalists, corpus, passOptions, rows},

  If[!xpResultQ[result], Return[xpNotResult[result]]];
  {source, finalists} =
    If[
      result["SolutionParetoFront"] =!= {},
      {"SolutionParetoFront", result["SolutionParetoFront"]},
      {"SearchParetoFront", result["SearchParetoFront"]}
    ];

  (* One corpus for every finalist, so their termination rates compare. *)
  corpus = xpRobustnessStates[
    result,
    OptionValue[CandidateRobustness, {opts}, "InitialStates"],
    OptionValue[CandidateRobustness, {opts}, "EnsembleSize"],
    OptionValue[CandidateRobustness, {opts}, "RandomSeed"]
  ];
  If[FailureQ[corpus], Return[corpus]];
  passOptions = FilterRules[{opts}, Except["InitialStates"]];

  rows = Map[
    Function[finalist,
      Module[{row},
        row = CandidateRobustness[result, finalist["CandidateID"], "InitialStates" -> corpus["States"], Sequence @@ passOptions];
        If[
          AssociationQ[row],
          Append[row, "InitialStateCorpus" -> Join[row["InitialStateCorpus"], KeyTake[corpus, {"Source", "RandomSeed", "RequestedSize"}]]],
          row
        ]
      ]
    ],
    finalists
  ];

  <|
    "FinalistSource" -> source,
    "Finalists" -> rows,
    "InitialStates" -> corpus["States"],
    "InitialStateSource" -> corpus["Source"],
    "CapSensitiveIDs" -> Lookup[Select[rows, AssociationQ[#] && TrueQ[#["CapSensitiveQ"]] &], "CandidateID", {}],
    "SemanticsSensitiveIDs" -> Lookup[Select[rows, AssociationQ[#] && TrueQ[#["SemanticsSensitiveQ"]] &], "CandidateID", {}],
    "StateEquivalence" -> xpStateEquivalence[result]
  |>
]


(* ::Section:: *)
(*Discovery report*)


$DiscoveryReportFields = {
  "Candidate ID / evaluation ID",
  "Canonical rule",
  "Initial state",
  "Edge symmetry",
  "Rewrite semantics",
  "Backend and versions",
  "Limits and random seed",
  "Status and cycle evidence",
  "Constraint satisfaction",
  "State / transition / raw-event counts",
  "Lifetime (longest derivation and BFS depth) and maximum frontier",
  "Maximum state size and density",
  "Terminal-state summary",
  "Runtime",
  "Search-front / solution-front membership",
  "Initial-state robustness summary",
  "Mutation lineage",
  "Interpretation with evidence level"
};


(* Claim discipline: the only phrases used for a status. *)
xpStatusStatement[status_, witnessQ_] :=
  Switch[
    status,
    "Halted", "verified to halt under this finite reachable exploration",
    "CycleDetected",
      If[
        TrueQ[witnessQ],
        "cycle detected",
        "not resolved within the stated limits (a cycle was reported, but no cycle witness is recorded)"
      ],
    "Invalid", "evaluation failed; no behavior is established",
    _, "not resolved within the stated limits"
  ]


xpEvidenceLevel[status_, witnessQ_, solutionQ_] :=
  Switch[
    status,
    "Halted", If[TrueQ[solutionQ], "VerifiedSolution", "VerifiedHalting"],
    "CycleDetected", If[TrueQ[witnessQ], "WitnessedCycle", "Unresolved"],
    "Invalid", "EvaluationFailed",
    _, "Unresolved"
  ]


xpRequirementString[specification_Association, config_Association] :=
  Switch[
    Lookup[specification, "Direction", None],
    "Range", "in " <> xpInputString[resolveObjectiveRange[specification, config]],
    "Target", "within " <> xpValueString[Lookup[specification, "Tolerance", Missing["NoTolerance"]]] <>
      " of " <> xpValueString[Lookup[specification, "Target", Missing["NoTarget"]]],
    "Maximize",
      If[KeyExistsQ[specification, "Threshold"], ">= " <> xpValueString[specification["Threshold"]], "True"],
    "Minimize",
      If[KeyExistsQ[specification, "Threshold"], "<= " <> xpValueString[specification["Threshold"]], "False"],
    _, "unknown requirement"
  ]


xpConstraintField[candidate_Association, config_Association] := Module[{rows, allQ, solutionQ},
  rows = KeyValueMap[
    Function[{name, specification},
      With[{value = Lookup[Lookup[candidate, "Fitness", <||>], name, Missing["NotComputed"]]},
        <|
          "Metric" -> name,
          "Value" -> value,
          "Requirement" -> xpRequirementString[specification, config],
          "SatisfiedQ" -> TrueQ[Quiet @ constraintSatisfiedQ[value, specification, config]]
        |>
      ]
    ],
    Select[xpMetricSpecifications[config], Lookup[#, "Stage", "Objective"] === "Constraint" &]
  ];
  allQ = AllTrue[rows, #["SatisfiedQ"] &];
  solutionQ = xpSolutionQ[candidate, config];
  <|
    "Constraints" -> rows,
    "AllSatisfiedQ" -> allQ,
    "SolutionEligibleQ" -> solutionQ,
    "Summary" -> If[
      rows === {},
      "no constraints configured",
      StringRiffle[
        (#["Metric"] <> " = " <> xpValueString[#["Value"]] <> " (required " <> #["Requirement"] <> ": " <>
          If[#["SatisfiedQ"], "satisfied", "not satisfied"] <> ")") & /@ rows,
        "; "
      ] <> If[allQ, "; all constraints satisfied", "; not all constraints satisfied"]
    ] <> If[solutionQ, "; verified solution of this run", "; not a verified solution of this run"]
  |>
]


xpMetricOrCompute[fitness_Association, metric_String, function_, states_List] :=
  Which[
    KeyExistsQ[fitness, metric], fitness[metric],
    states === {}, Missing["NoStates"],
    True, Quiet @ Check[function[states], Missing["NotComputed"]]
  ]


xpSizeField[candidate_Association, config_Association] := Module[{states, fitness, values},
  states = Lookup[candidate, "States", {}];
  fitness = Lookup[candidate, "Fitness", <||>];
  values = withConfigUniverse[
    config,
    <|
      "MaxVertexCount" -> xpMetricOrCompute[fitness, "HGMaxVerticesCount", statesMaxVertexCount, states],
      "MaxEdgeCount" -> xpMetricOrCompute[fitness, "HGMaxEdgesCount", statesMaxEdgeCount, states],
      "MaxEdgeToVertexRatio" -> xpMetricOrCompute[fitness, "HGMaxEdgeToVertexRatio", statesMaxEdgeToVertexRatio, states],
      "MaxDensity" -> xpMetricOrCompute[fitness, "HGMaxDensity", statesMaxDensity, states]
    |>
  ];
  Append[
    values,
    "Summary" -> "over explored states: at most " <> xpValueString[values["MaxVertexCount"]] <> " vertices and " <>
      xpValueString[values["MaxEdgeCount"]] <> " edges; maximum edge-to-vertex ratio " <>
      xpValueString[values["MaxEdgeToVertexRatio"]] <> "; maximum density " <> xpValueString[values["MaxDensity"]]
  ]
]


xpTerminalField[candidate_Association] := Module[{terminals, status, edges, vertices},
  terminals = Lookup[candidate, "FinalStates", {}];
  status = Lookup[candidate, "Status", Missing[]];
  edges = Length /@ terminals;
  vertices = Length[Union[Flatten[#]]] & /@ terminals;
  <|
    "TerminalStateCount" -> Length[terminals],
    "CompleteQ" -> status === "Halted",
    "EdgeCounts" -> xpDistributionSummary[edges],
    "VertexCounts" -> xpDistributionSummary[vertices],
    "Examples" -> Take[SortBy[terminals, {Length, Identity}], UpTo[3]],
    "Summary" -> If[
      status === "Halted",
      ToString[Length[terminals]] <> " verified terminal state(s), complete for this exploration",
      ToString[Length[terminals]] <> " terminal state(s) found within the stated limits (not exhaustive)"
    ] <>
      If[
        terminals === {},
        "",
        "; edges " <> ToString[Min[edges]] <> "-" <> ToString[Max[edges]] <> ", vertices " <>
          ToString[Min[vertices]] <> "-" <> ToString[Max[vertices]]
      ]
  |>
]


xpLineageField[result_Association, candidate_Association] := Module[{byID, path = {}, current = candidate, steps, guard = 0},
  byID = Association[#["CandidateID"] -> # & /@ result["Candidates"]];
  While[
    AssociationQ[current] && guard <= Length[byID],
    PrependTo[path, current];
    current = Lookup[byID, Key[Lookup[current, "ParentID", Missing["NoParent"]]], Missing["NoParent"]];
    guard++
  ];
  steps = Map[
    <|
      "CandidateID" -> #["CandidateID"],
      "Strategy" -> Lookup[#, "Strategy", Missing["NotRecorded"]],
      "Round" -> Lookup[#, "Round", Missing["NotRecorded"]],
      "AppliedOperators" -> Lookup[
        Select[Lookup[Lookup[#, "Provenance", <||>], "AppliedOperators", {}], AssociationQ],
        "Operator",
        {}
      ],
      "Rule" -> #["Rule"]
    |> &,
    path
  ];
  <|
    "Path" -> steps,
    "Depth" -> Length[steps] - 1,
    "StartsAtSeedQ" -> MatchQ[First[path, <||>], _?(Lookup[#, "Strategy", None] === "Seed" &)],
    "Summary" -> StringRiffle[
      Map[
        xpShortID[#["CandidateID"]] <> " (" <> xpValueString[#["Strategy"]] <>
          If[#["AppliedOperators"] === {}, "", ": " <> StringRiffle[#["AppliedOperators"], ", "]] <> ")" &,
        steps
      ],
      " -> "
    ]
  |>
]


xpRobustnessField[result_Association, candidateID_, Automatic] := Module[{diagnostics, entry},
  diagnostics = Lookup[result, "InitialStateDiagnostics", Missing["NotRecorded"]];
  entry = If[
    AssociationQ[diagnostics],
    SelectFirst[Select[Lookup[diagnostics, "Finalists", {}], AssociationQ], #["CandidateID"] === candidateID &, Missing["NotAFinalist"]],
    Missing["NotRequested"]
  ];
  If[
    !AssociationQ[entry],
    <|"Source" -> None, "Available" -> False, "Summary" -> "not computed for this candidate"|>,
    <|
      "Source" -> "InitialStateDiagnostics",
      "Available" -> True,
      "InitialStatesTested" -> Lookup[entry, "InitialStatesTested", Missing[]],
      "InitiallyApplicableRate" -> Lookup[entry, "InitiallyApplicableRate", Missing[]],
      "TerminationRate" -> Lookup[entry, "TerminationRate", Missing[]],
      "MedianMultiwayStateCount" -> Lookup[entry, "MedianMultiwayStateCount", Missing[]],
      "Summary" -> "run diagnostics on " <> xpValueString[Lookup[entry, "InitialStatesTested", Missing[]]] <>
        " random initial state(s) with the seed's edge signature: initially applicable rate " <>
        xpValueString[Lookup[entry, "InitiallyApplicableRate", Missing[]]] <> ", termination rate among applicable states " <>
        xpValueString[Lookup[entry, "TerminationRate", Missing[]]] <> ", median state count " <>
        xpValueString[Lookup[entry, "MedianMultiwayStateCount", Missing[]]] <> " (these states only)"
    |>
  ]
]

xpRobustnessField[_, _, None] := <|"Source" -> None, "Available" -> False, "Summary" -> "not requested"|>

xpRobustnessField[_, _, robustness_Association] :=
  <|
    "Source" -> "CandidateRobustness",
    "Available" -> True,
    "CapSensitiveQ" -> Lookup[robustness, "CapSensitiveQ", Missing[]],
    "CapFactors" -> Lookup[Lookup[robustness, "CapSensitivity", <||>], "Factors", Missing[]],
    "StatesTested" -> Lookup[Lookup[robustness, "InitialStateCorpus", <||>], "StatesTested", Missing[]],
    "ApplicableCount" -> Lookup[Lookup[robustness, "InitialStateCorpus", <||>], "ApplicableCount", Missing[]],
    "HaltedCount" -> Lookup[Lookup[robustness, "InitialStateCorpus", <||>], "HaltedCount", Missing[]],
    "TerminationRate" -> Lookup[Lookup[robustness, "InitialStateCorpus", <||>], "TerminationRate", Missing[]],
    "SemanticsSensitiveQ" -> Lookup[robustness, "SemanticsSensitiveQ", Missing[]],
    "Summary" -> Lookup[robustness, "Summary", "robustness computed"]
  |>


xpInterpretationField[candidate_Association, statusStatement_, evidence_, equivalence_, robustness_] := Module[
  {status, states, interpretation, scope},
  status = candidate["Status"];
  states = Length[Lookup[candidate, "States", {}]];
  interpretation = Switch[
    evidence,
    "VerifiedSolution" | "VerifiedHalting",
      "Verified to halt under this finite reachable exploration: the canonical state space reachable from the stated initial state was exhausted (" <>
        ToString[states] <> " distinct states under " <> equivalence <> ") and contains no cycle; the longest derivation has " <>
        xpValueString[Lookup[candidate, "LongestDerivation", Missing["NotRecorded"]]] <> " events." <>
        If[evidence === "VerifiedSolution", " It satisfies every configured constraint.", " It does not satisfy every configured constraint."],
    "WitnessedCycle",
      "Cycle detected: the recorded witness (" <> ToString[Length[candidate["CycleWitness"]]] <>
        " transition(s)) revisits a state, so rewriting can continue indefinitely from the stated initial state under " <>
        equivalence <> ".",
    "EvaluationFailed",
      "The evaluation failed; no behavior is established.",
    _,
      "Not resolved within the stated limits: exploration stopped " <>
        If[
          Lookup[candidate, "LimitsReached", {}] === {},
          "without a certified outcome",
          "at " <> StringRiffle[Lookup[candidate, "LimitsReached", {}], ", "]
        ] <> " after " <> ToString[states] <> " distinct states under " <> equivalence <>
        "; neither halting nor non-halting is established."
  ];
  scope = "Scope: the stated rule, initial state, equivalence, rewrite semantics and limits only; no conclusion is drawn for other initial states.";
  <|
    "EvidenceLevel" -> evidence,
    "StatusStatement" -> statusStatement,
    "Interpretation" -> interpretation,
    "RobustnessNote" -> Lookup[robustness, "Summary", "not computed"],
    "Scope" -> scope,
    "Summary" -> "Evidence level " <> evidence <> ". " <> interpretation <>
      If[TrueQ[Lookup[robustness, "Available", False]], " Robustness: " <> robustness["Summary"] <> ".", ""] <>
      " " <> scope
  |>
]


Options[DiscoveryReport] = {"Robustness" -> Automatic};

DiscoveryReport[result_, candidateID_, OptionsPattern[]] := Module[
  {
    candidate, config, provenance, equivalence, status, witnessQ, solutionQ, statusStatement,
    evidence, robustnessOption, robustness, searchIDs, solutionIDs, generations, depth, frontier,
    champions, fields
  },

  If[!xpResultQ[result], Return[xpNotResult[result]]];
  candidate = xpFindCandidate[result, candidateID];
  If[MissingQ[candidate], Return[xpUnknownCandidate[candidateID]]];

  robustnessOption = OptionValue["Robustness"];
  If[
    AssociationQ[robustnessOption] && Lookup[robustnessOption, "CandidateID", None] =!= candidateID,
    Return @ Failure[
      "RobustnessMismatch",
      <|"Message" -> "The \"Robustness\" association belongs to another candidate.", "CandidateID" -> candidateID|>
    ]
  ];

  config = result["Configuration"];
  provenance = result["Provenance"];
  equivalence = xpStateEquivalence[result];
  status = Lookup[candidate, "Status", Missing["NotRecorded"]];
  witnessQ = xpCycleWitnessQ[candidate];
  solutionQ = xpSolutionQ[candidate, config];
  statusStatement = xpStatusStatement[status, witnessQ];
  evidence = xpEvidenceLevel[status, witnessQ, solutionQ];
  robustness = xpRobustnessField[result, candidateID, robustnessOption];
  searchIDs = Lookup[result["SearchParetoFront"], "CandidateID", {}];
  solutionIDs = Lookup[result["SolutionParetoFront"], "CandidateID", {}];
  generations = Lookup[candidate, "Generations", {}];
  depth = Max[0, Length[DeleteCases[generations, {}]] - 1];
  frontier = Max[0, Length /@ generations];
  champions = Keys @ Select[Lookup[result, "MetricChampions", <||>], # === candidateID &];

  fields = <|
    "Candidate ID / evaluation ID" -> <|
      "CandidateID" -> candidateID,
      "EvaluationID" -> Lookup[candidate, "EvaluationID", Missing["NotRecorded"]],
      "EvolutionKey" -> Lookup[candidate, "EvolutionKey", Missing["NotRecorded"]],
      "RunID" -> result["RunID"],
      "Summary" -> candidateID <> " / " <> xpValueString[Lookup[candidate, "EvaluationID", Missing["NotRecorded"]]] <>
        " (run " <> result["RunID"] <> ")"
    |>,
    "Canonical rule" -> <|
      "Rule" -> candidate["Rule"],
      "RuleSetQ" -> ruleSetQ[candidate["Rule"]],
      "Signature" -> xpRuleSignature[candidate["Rule"]],
      "Summary" -> xpInputString[candidate["Rule"]] <>
        If[ruleSetQ[candidate["Rule"]], " (rule set)", " (signature " <> xpSignatureString[xpRuleSignature[candidate["Rule"]]] <> ")"]
    |>,
    "Initial state" -> <|
      "InitialState" -> candidate["InitialState"],
      "EdgeCount" -> Length[candidate["InitialState"]],
      "VertexCount" -> Length[Union[Flatten[candidate["InitialState"]]]],
      "SeedInitialStateQ" -> candidate["InitialState"] === Lookup[result["Seed"], "InitialState", None],
      "Summary" -> xpInputString[candidate["InitialState"]] <> " (canonical; " <> ToString[Length[candidate["InitialState"]]] <>
        " edges, " <> ToString[Length[Union[Flatten[candidate["InitialState"]]]]] <> " vertices)"
    |>,
    "Edge symmetry" -> <|
      "EdgeSymmetry" -> config["EdgeSymmetry"],
      "SymmetryGroups" -> config["SymmetryGroups"],
      "StateEquivalence" -> equivalence,
      "Summary" -> config["EdgeSymmetry"] <>
        If[config["SymmetryGroups"] === <||>, "", " with symmetry groups " <> xpInputString[config["SymmetryGroups"]]] <>
        "; state equivalence " <> equivalence
    |>,
    "Rewrite semantics" -> <|
      "RewriteSemantics" -> config["RewriteSemantics"],
      "Summary" -> config["RewriteSemantics"]
    |>,
    "Backend and versions" -> <|
      "Backend" -> "CanonicalBFS",
      "CanonicalForm" -> config["CanonicalForm"],
      "EvaluatorVersion" -> Lookup[provenance, "EvaluatorVersion", Missing["NotRecorded"]],
      "PacletVersion" -> Lookup[provenance, "PacletVersion", Missing["NotRecorded"]],
      "HypergraphPacletVersion" -> Lookup[provenance, "HypergraphPacletVersion", Missing["NotRecorded"]],
      "WolframVersion" -> Lookup[provenance, "WolframVersion", Missing["NotRecorded"]],
      "Summary" -> "CanonicalBFS backend, " <> config["CanonicalForm"] <> " canonical form, evaluator " <>
        xpValueString[Lookup[provenance, "EvaluatorVersion", Missing["NotRecorded"]]] <> ", paclet " <>
        xpValueString[Lookup[provenance, "PacletVersion", Missing["NotRecorded"]]] <> ", Hypergraph paclet " <>
        xpValueString[Lookup[provenance, "HypergraphPacletVersion", Missing["NotRecorded"]]] <> ", Wolfram " <>
        xpValueString[Lookup[provenance, "WolframVersion", Missing["NotRecorded"]]]
    |>,
    "Limits and random seed" -> <|
      "EvolutionLimits" -> config["EvolutionLimits"],
      "RandomSeed" -> Lookup[provenance, "RandomSeed", config["RandomSeed"]],
      "Summary" -> xpLimitsString[config["EvolutionLimits"]] <> "; random seed " <>
        xpValueString[Lookup[provenance, "RandomSeed", config["RandomSeed"]]]
    |>,
    "Status and cycle evidence" -> <|
      "Status" -> status,
      "CycleDetectedQ" -> Lookup[candidate, "CycleDetectedQ", Missing["NotRecorded"]],
      "CycleWitnessRecordedQ" -> witnessQ,
      "CycleWitness" -> Lookup[candidate, "CycleWitness", Missing["NotRecorded"]],
      "LimitsReached" -> Lookup[candidate, "LimitsReached", {}],
      "Statement" -> statusStatement,
      "Summary" -> xpValueString[status] <> ": " <> statusStatement <>
        Which[
          witnessQ, " (cycle witness of " <> ToString[Length[candidate["CycleWitness"]]] <> " transition(s) recorded)",
          Lookup[candidate, "LimitsReached", {}] =!= {}, " (limits reached: " <> StringRiffle[candidate["LimitsReached"], ", "] <> ")",
          True, ""
        ]
    |>,
    "Constraint satisfaction" -> xpConstraintField[candidate, config],
    "State / transition / raw-event counts" -> <|
      "StateCount" -> Length[Lookup[candidate, "States", {}]],
      "TransitionCount" -> Lookup[candidate, "TransitionCount", Missing["NotRecorded"]],
      "RawEventCount" -> Lookup[candidate, "EventCount", Missing["NotRecorded"]],
      "StateEquivalence" -> equivalence,
      "Summary" -> ToString[Length[Lookup[candidate, "States", {}]]] <> " distinct states, " <>
        xpValueString[Lookup[candidate, "TransitionCount", Missing["NotRecorded"]]] <> " distinct transitions, " <>
        xpValueString[Lookup[candidate, "EventCount", Missing["NotRecorded"]]] <> " raw rewrite events (states counted under the " <>
        equivalence <> " state equivalence)"
    |>,
    "Lifetime (longest derivation and BFS depth) and maximum frontier" -> <|
      "LongestDerivation" -> Lookup[candidate, "LongestDerivation", Missing["NotRecorded"]],
      "LongestDerivationExactQ" -> status === "Halted",
      "BFSDepth" -> depth,
      "MaximumFrontier" -> frontier,
      "Summary" -> "longest derivation " <> xpValueString[Lookup[candidate, "LongestDerivation", Missing["NotRecorded"]]] <>
        Which[
          status === "Halted", " (exact)",
          MissingQ[Lookup[candidate, "LongestDerivation", Missing[]]], "",
          True, " (longest found within the stated limits, not exact)"
        ] <>
        ", BFS depth " <> ToString[depth] <> ", maximum frontier size " <> ToString[frontier]
    |>,
    "Maximum state size and density" -> xpSizeField[candidate, config],
    "Terminal-state summary" -> xpTerminalField[candidate],
    "Runtime" -> <|
      "Seconds" -> Lookup[candidate, "Runtime", Missing["NotRecorded"]],
      "Summary" -> xpValueString[Lookup[candidate, "Runtime", Missing["NotRecorded"]]] <>
        " s wall clock for the multiway evaluation (machine-dependent)"
    |>,
    "Search-front / solution-front membership" -> <|
      "FrontMembership" -> Lookup[result["FrontMembership"], candidateID, "None"],
      "SearchFrontQ" -> MemberQ[searchIDs, candidateID],
      "SolutionFrontQ" -> MemberQ[solutionIDs, candidateID],
      "MetricChampionOf" -> champions,
      "Summary" -> "search front: " <> If[MemberQ[searchIDs, candidateID], "yes", "no"] <>
        "; solution front: " <> If[MemberQ[solutionIDs, candidateID], "yes", "no"] <>
        If[champions === {}, "", "; champion of " <> StringRiffle[champions, ", "]]
    |>,
    "Initial-state robustness summary" -> robustness,
    "Mutation lineage" -> xpLineageField[result, candidate],
    "Interpretation with evidence level" -> xpInterpretationField[candidate, statusStatement, evidence, equivalence, robustness]
  |>;

  Append[
    fields,
    "Text" -> StringRiffle[
      Prepend[
        (# <> ": " <> fields[#]["Summary"]) & /@ $DiscoveryReportFields,
        "Discovery report: candidate " <> candidateID <> " of run " <> result["RunID"]
      ],
      "\n"
    ]
  ]
]


(* ::Section:: *)
(*Seed corpus*)


$xpCorpusLimits = <|"MaxGenerations" -> 10, "MaxEvents" -> 2000, "MaxStates" -> Infinity, "TimeConstraint" -> 60.|>;


xpCorpusEntry[name_, rule_, state_, symmetry_, groups_, limits_, expected_, notes_] :=
  <|
    "Name" -> name,
    "Rule" -> rule,
    "InitialState" -> state,
    "EdgeSymmetry" -> symmetry,
    "SymmetryGroups" -> groups,
    "Limits" -> Join[$xpCorpusLimits, limits],
    "ExpectedStatus" -> expected,
    "Notes" -> notes
  |>


SeedCorpus[] := {
  xpCorpusEntry[
    "EdgeContractionCycle4",
    {{1, 2}, {2, 3}} -> {{1, 3}},
    {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
    "Unordered", Automatic, <||>, "Halted",
    "Contraction shortens the cycle; in the simple unordered universe the triangle collapses to one edge, which no longer matches."
  ],
  xpCorpusEntry[
    "EdgeContractionCycle6",
    {{1, 2}, {2, 3}} -> {{1, 3}},
    {{1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 1}},
    "Unordered", Automatic, <||>, "Halted",
    "A longer contraction chain C6 -> C5 -> C4 -> C3 -> single edge."
  ],
  xpCorpusEntry[
    "EdgeContractionPath3",
    {{1, 2}, {2, 3}} -> {{1, 3}},
    {{1, 2}, {2, 3}, {3, 4}},
    "Unordered", Automatic, <||>, "Halted",
    "Paths shrink by one edge per event until a single edge remains."
  ],
  xpCorpusEntry[
    "ContractionRuleSet",
    {{{1, 2}, {2, 3}} -> {{1, 3}}, {{1, 2}, {2, 3}, {3, 4}} -> {{1, 4}}},
    {{1, 2}, {2, 3}, {3, 4}},
    "Unordered", Automatic, <||>, "Halted",
    "Rule set: the three-edge path reaches one edge directly or in two events, so the longest derivation (2) exceeds the BFS depth (1)."
  ],
  xpCorpusEntry[
    "EdgeReversalUnordered",
    {{1, 2}} -> {{2, 1}},
    {{1, 2}},
    "Unordered", Automatic, <||>, "CycleDetected",
    "Reversal is the identity on unordered edges: the state rewrites to itself (self-loop witness)."
  ],
  xpCorpusEntry[
    "EdgeReversalOrdered",
    {{1, 2}} -> {{2, 1}},
    {{1, 2}, {2, 3}},
    "Ordered", Automatic, <||>, "CycleDetected",
    "Ordered universe: reversing an edge of a directed path gives an out- or in-star, and reversing again returns to the path."
  ],
  xpCorpusEntry[
    "DuplicationUnordered",
    {{1, 2}} -> {{1, 2}, {1, 2}},
    {{1, 2}},
    "Unordered", Automatic, <||>, "CycleDetected",
    "The simple unordered universe removes duplicate edges, so duplication rewrites the state to itself."
  ],
  xpCorpusEntry[
    "DuplicationOrdered",
    {{1, 2}} -> {{1, 2}, {1, 2}},
    {{1, 2}},
    "Ordered", Automatic, <|"MaxGenerations" -> 3|>, "GenerationCap",
    "Edge multiplicity is semantic in the ordered universe: every event adds a copy, so the generation cap stops the exploration."
  ],
  xpCorpusEntry[
    "OrderedPathContraction",
    {{1, 2}, {2, 3}} -> {{1, 3}},
    {{1, 2}, {2, 3}, {3, 4}},
    "Ordered", Automatic, <||>, "Halted",
    "Directed contraction of a directed path halts at a single directed edge."
  ],
  xpCorpusEntry[
    "SubdivisionGenerationCap",
    {{1, 2}} -> {{1, 3}, {3, 2}},
    {{1, 2}},
    "Unordered", Automatic, <|"MaxGenerations" -> 3|>, "GenerationCap",
    "Edge subdivision grows a path by one edge per generation, without end."
  ],
  xpCorpusEntry[
    "SubdivisionEventCap",
    {{1, 2}} -> {{1, 3}, {3, 2}},
    {{1, 2}},
    "Unordered", Automatic, <|"MaxGenerations" -> 20, "MaxEvents" -> 10|>, "EventCap",
    "The raw event count grows with the path length and exceeds MaxEvents before MaxGenerations."
  ],
  xpCorpusEntry[
    "SubdivisionStateCap",
    {{1, 2}} -> {{1, 3}, {3, 2}},
    {{1, 2}},
    "Unordered", Automatic, <|"MaxGenerations" -> 20, "MaxEvents" -> Infinity, "MaxStates" -> 3|>, "StateCap",
    "Every generation discovers one new path; the fourth distinct state exceeds MaxStates."
  ],
  xpCorpusEntry[
    "DeclaredCyclicMerge",
    {{1, 2, 3}, {1, 2, 3}} -> {{1, 2, 3}},
    {{1, 2, 3}, {2, 3, 1}, {3, 1, 2}},
    "Declared", <|3 -> "Cyclic"|>, <||>, "Halted",
    "Under the cyclic slot symmetry the three rotations are three copies of one ternary edge; merging copies halts at one copy."
  ],
  xpCorpusEntry[
    "DeclaredCyclicGrowth",
    {{1, 2, 3}} -> {{1, 2, 4}, {4, 2, 3}},
    {{1, 2, 3}},
    "Declared", <|3 -> "Cyclic"|>, <|"MaxGenerations" -> 2|>, "GenerationCap",
    "Ternary-edge growth under the cyclic slot symmetry never halts; the generation cap stops it."
  ]
}


xpVerifyCorpusEntry[entry_Association] := Module[{name, expected, config, seed, evolution, observed},
  name = Lookup[entry, "Name", Missing["NoName"]];
  expected = Lookup[entry, "ExpectedStatus", Missing["NoExpectedStatus"]];
  config = ValidateEvolutionConfiguration[
    <|
      "Rule" -> Lookup[entry, "Rule", Automatic],
      "InitialState" -> Lookup[entry, "InitialState", Automatic],
      "EdgeSymmetry" -> Lookup[entry, "EdgeSymmetry", "Unordered"],
      "SymmetryGroups" -> Lookup[entry, "SymmetryGroups", Automatic],
      "RewriteSemantics" -> Lookup[entry, "RewriteSemantics", "EdgeToken"],
      "EvolutionLimits" -> Lookup[entry, "Limits", <||>]
    |>
  ];
  If[
    FailureQ[config],
    Return @ <|"Name" -> name, "ExpectedStatus" -> expected, "ObservedStatus" -> Missing["InvalidEntry"], "MatchQ" -> False, "Failure" -> config|>
  ];
  seed = ResolveAndCanonicalizeSeed[config];
  If[
    FailureQ[seed],
    Return @ <|"Name" -> name, "ExpectedStatus" -> expected, "ObservedStatus" -> Missing["InvalidEntry"], "MatchQ" -> False, "Failure" -> seed|>
  ];

  (* A fresh canonical evolution: no evaluation cache, no preloaded behavior. *)
  evolution = withConfigUniverse[
    config,
    CanonicalMultiwayEvolution[seed["Rule"], seed["InitialState"], config["EvolutionLimits"]]
  ];
  observed = If[AssociationQ[evolution], evolution["Status"], "Invalid"];

  <|
    "Name" -> name,
    "EdgeSymmetry" -> config["EdgeSymmetry"],
    "StateEquivalence" -> stateEquivalenceTag[config],
    "ExpectedStatus" -> expected,
    "ObservedStatus" -> observed,
    "MatchQ" -> observed === expected,
    "StateCount" -> If[AssociationQ[evolution], Length[evolution["States"]], Missing["Invalid"]],
    "TransitionCount" -> If[AssociationQ[evolution], Length[evolution["TransitionEdges"]], Missing["Invalid"]],
    "EventCount" -> If[AssociationQ[evolution], evolution["EventCount"], Missing["Invalid"]],
    "LongestDerivation" -> If[AssociationQ[evolution], evolution["LongestDerivation"], Missing["Invalid"]],
    "CycleWitnessQ" -> AssociationQ[evolution] && MatchQ[evolution["CycleWitness"], {__DirectedEdge}],
    "LimitsReached" -> If[AssociationQ[evolution], evolution["LimitsReached"], {}],
    "Failure" -> None
  |>
]


VerifySeedCorpus[] := VerifySeedCorpus[SeedCorpus[]]

VerifySeedCorpus[corpus_List] := Module[{rows},
  If[
    corpus === {} || !AllTrue[corpus, AssociationQ],
    Return @ Failure["InvalidCorpus", <|"Message" -> "The corpus must be a nonempty list of entry associations."|>]
  ];
  rows = xpVerifyCorpusEntry /@ corpus;
  <|
    "AllMatchQ" -> AllTrue[rows, TrueQ[#["MatchQ"]] &],
    "Entries" -> rows,
    "Mismatches" -> Lookup[Select[rows, !TrueQ[#["MatchQ"]] &], "Name", {}],
    "StatusCounts" -> Counts[Lookup[rows, "ObservedStatus", {}]]
  |>
]
