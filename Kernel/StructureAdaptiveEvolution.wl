(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["SamuelFrerichs`StructureAdaptiveEvolution`", {"WolframInstitute`Hypergraph`"}];


(* ::Subsection:: *)
(*Public symbols*)


StructureAdaptiveEvolution::usage =
  "StructureAdaptiveEvolution[opts] runs an adaptive Pareto search over mutated hypergraph rewrite rules (or rule sets) and returns a result association with candidates, search and solution fronts, champions, strategy weights, lineage, proposal failures, front history, performance, provenance and a resume state.";

StructureAdaptiveEvolution::regfail =
  "Registration failed while loading `1`: `2`.";

ValidateEvolutionConfiguration::usage =
  "ValidateEvolutionConfiguration[assoc] returns a normalized configuration association or a Failure.";

ResolveAndCanonicalizeSeed::usage =
  "ResolveAndCanonicalizeSeed[config] resolves explicit or Automatic rule/initial-state settings into a canonical seed association (with Registry code, metadata and version for Registry seeds) or a Failure.";

ClearPreloadedEvaluations::usage =
  "ClearPreloadedEvaluations[] removes every evaluation preloaded in this session (for example by ExperimentStorePreload); later evaluations are computed afresh.";

EvaluateCandidate::usage =
  "EvaluateCandidate[candidate, config] evolves a candidate rule/state pair once (with caching keyed by every behavior-changing policy and implementation version), builds the requested artifacts, computes the selected fitness metrics, and returns the completed candidate record with its EvolutionKey and EvaluationID.";

CanonicalMultiwayEvolution::usage =
  "CanonicalMultiwayEvolution[rule, state, limits] runs a canonical breadth-first multiway evolution of a rule or rule set and returns generations, states graph, transition multiplicities, terminal states, status (\"Halted\", \"CycleDetected\", \"GenerationCap\", \"EventCap\", \"StateCap\", \"TimedOut\" or \"Invalid\"), cycle witness and longest derivation. CanonicalMultiwayEvolution[rule, state, limits, \"RecordEvents\" -> True] also records every raw rewrite event.";

CanonicalStateForm::usage =
  "CanonicalStateForm[state] returns the canonical edge list of a hypergraph state under the active edge-symmetry universe (default: unordered hyperedges, duplicates removed). CanonicalStateForm[state, \"Unordered\" | \"Ordered\"] selects the universe explicitly; CanonicalStateForm[state, \"Declared\", groups] uses declared slot-symmetry groups per arity.";

CanonicalRuleForm::usage =
  "CanonicalRuleForm[lhs -> rhs] returns the canonical form of a hypergraph rewrite rule as an edge-list Rule under the active edge-symmetry universe; CanonicalRuleForm[{rule1, rule2, ...}] returns the canonical rule set (sorted canonical member rules, duplicates removed). CanonicalRuleForm[rule, \"Unordered\" | \"Ordered\"] and CanonicalRuleForm[rule, \"Declared\", groups] select the universe explicitly. In the unordered universe the right-hand side is read as a simple hypergraph, so rules that differ only by duplicate right-hand edges have one canonical form.";

CanonicalFormSelfTest::usage =
  "CanonicalFormSelfTest[] property-tests the canonical-form backends (\"Exact\", \"Native\") in the unordered and ordered universes on random states: invariance under relabelling and edge reordering, completeness against brute-force isomorphism, and whether every canonical form is an isomorphic copy of its input.";

RewriteEventEvolution::usage =
  "RewriteEventEvolution[rule, state, limits] runs a single-way evolution with explicit event and edge identities and returns its events, edge records, states, final state, status and causal graph. The option \"UpdateOrder\" chooses the events of each step: \"Generational\" (default), \"Sequential\", \"LeastRecent\", \"MostRecent\" or {\"Random\", seed}.";

MultiwayEvolutionGraph::usage =
  "MultiwayEvolutionGraph[evolution] unrolls the canonical states graph of a CanonicalMultiwayEvolution result by generation: vertices {state, k} for states reachable in k events. MultiwayEvolutionGraph[evolution, depth] bounds the number of generations.";

MultiwayLongestDerivation::usage =
  "MultiwayLongestDerivation[evolution] gives the length of the longest derivation from the initial state of a CanonicalMultiwayEvolution result: exact when the evolution halted, the longest found within the limits for a capped acyclic exploration, and Missing[\"CyclicStatesGraph\"] when a cycle makes derivations unbounded. MultiwayLongestDerivation[rule, state, limits] evolves first.";

hypergraphStateQ::usage =
  "hypergraphStateQ[expr] gives True if expr is a list of hyperedges (lists of atoms).";

HypergraphBasicSizeMetrics::usage =
  "HypergraphBasicSizeMetrics[hgOrStates] returns size metrics for a hypergraph state or aggregates over a list of states.";

FinalStateSizeMetrics::usage =
  "FinalStateSizeMetrics[states] returns size metrics for the last state of a state list.";

MultiwayFinalStateSizeMetrics::usage =
  "MultiwayFinalStateSizeMetrics[statesGraph] returns final-state size metrics for each terminal state of a multiway states graph.";

HypergraphRuntimeAndLifetime::usage =
  "HypergraphRuntimeAndLifetime[rule, initialState, maxGenerations] returns runtime, lifetime, and halting data for a bounded evolution.";

MWHypergraphRuntimeAndLifetime::usage =
  "MWHypergraphRuntimeAndLifetime[rule, initialState] returns multiway runtime and lifetime under the default evolution limits.";

MWHypergraphLifetime::usage =
  "MWHypergraphLifetime[multiwayGraph] returns the maximum distance from the initial state to a terminal state.";

EffectiveDimensionEstimate::usage =
  "EffectiveDimensionEstimate[hg] estimates the effective dimension from neighborhood-volume growth, or gives Missing[\"InsufficientStructure\"] when the state is too small for an estimate.";

DimensionVariance::usage =
  "DimensionVariance[hg] returns the variance of local dimension estimates, or Missing[\"InsufficientStructure\"] when fewer than two local estimates exist.";

DegreeMetrics::usage =
  "DegreeMetrics[hg] returns hyperedge-incidence degree metrics.";

BranchingUncertainty::usage =
  "BranchingUncertainty[input] returns branching/out-degree metrics for a multiway graph, state list, or single state.";

ReconvergenceMetrics::usage =
  "ReconvergenceMetrics[g] analyzes branch-point reconvergence in a directed multiway graph.";

ReconvergenceReport::usage =
  "ReconvergenceReport[g] summarizes reconvergence ratios for a directed multiway graph.";

CausalDependencyEntropy::usage =
  "CausalDependencyEntropy[g] returns the entropy of positive out-degrees of a directed graph.";

CausalMergeEvents::usage =
  "CausalMergeEvents[g] counts vertices with in-degree at least two.";

ComponentMetrics::usage =
  "ComponentMetrics[input] returns connected-component metrics for a graph, hypergraph state, state list, or multiway graph.";

GrowthBudgetMutation::usage =
  "GrowthBudgetMutation[rule] proposes a mutated rule with one fresh RHS variable and 1-2 added RHS hyperedges.";

GrowThenConstrainMutation::usage =
  "GrowThenConstrainMutation[rule] or GrowThenConstrainMutation[rule, \"Grow\"|\"Constrain\"] proposes a growth or constraining mutation.";

OverlappingMatchMutation::usage =
  "OverlappingMatchMutation[rule] proposes a rule with a less restrictive LHS.";

DelayedTerminationMutation::usage =
  "DelayedTerminationMutation[rule] proposes a single small RHS growth mutation or a new LHS condition edge.";

RuntimeThrottlingMutation::usage =
  "RuntimeThrottlingMutation[rule] proposes a rule with reduced RHS structure.";

AddLHSConditionMutation::usage =
  "AddLHSConditionMutation[rule] proposes a rule with one added LHS hyperedge over existing LHS variables, making the match more specific.";

IdentifyVariablesMutation::usage =
  "IdentifyVariablesMutation[rule] proposes a rule with two distinct variables merged into one.";

SplitVariableMutation::usage =
  "SplitVariableMutation[rule] proposes a rule with one occurrence of a repeated variable replaced by a fresh variable.";

VariableRewiringMutation::usage =
  "VariableRewiringMutation[rule] proposes a variable-level point mutation: identify two variables or split one.";

OrderedEdgePermutationMutation::usage =
  "OrderedEdgePermutationMutation[rule] permutes the vertex positions inside one edge of an ordered rule; OrderedEdgePermutationMutation[rule, \"Left\" | \"Right\"] targets one side. Requires the ordered or declared universe.";

GrowthBudgetStep::usage = "GrowthBudgetStep[rule, evolveFunction, ratioRange] performs one standalone growth-budget mutation step.";
RunGrowthBudgetMutations::usage = "RunGrowthBudgetMutations[rule, evolveFunction, iterations, tolerance] chains standalone growth-budget steps.";
GrowThenConstrainStep::usage = "GrowThenConstrainStep[rule, evolveFunction, targetVertices, targetEdges] performs one standalone grow-then-constrain step.";
RunGrowThenConstrainMutations::usage = "RunGrowThenConstrainMutations[rule, evolveFunction, iterations, targetVertices, targetEdges] chains standalone grow-then-constrain steps.";
OverlappingMatchStep::usage = "OverlappingMatchStep[rule, evolveFunction] performs one standalone overlapping-match step.";
RunOverlappingMatchMutations::usage = "RunOverlappingMatchMutations[rule, evolveFunction, iterations] chains standalone overlapping-match steps.";
DelayedTerminationStep::usage = "DelayedTerminationStep[rule, evolveFunction] performs one standalone delayed-termination step.";
RunDelayedTerminationMutations::usage = "RunDelayedTerminationMutations[rule, evolveFunction, iterations] chains standalone delayed-termination steps.";
RuntimeThrottlingStep::usage = "RuntimeThrottlingStep[rule, evolveFunction, retainedStateFraction] performs one standalone runtime-throttling step.";
RunRuntimeThrottlingMutations::usage = "RunRuntimeThrottlingMutations[rule, evolveFunction, iterations, retainedStateFraction] chains standalone runtime-throttling steps.";


(* Public symbols of further modules are declared in Kernel/Usage/*.wl, which
   are read here, in the public context, before any implementation file.
   The directory variable is spelled with its private context so it does not
   become a public symbol. *)
With[
  {SamuelFrerichs`StructureAdaptiveEvolution`Private`usageDirectory =
    FileNameJoin[{DirectoryName[$InputFileName], "Usage"}]},
  If[
    DirectoryQ[SamuelFrerichs`StructureAdaptiveEvolution`Private`usageDirectory],
    Scan[Get, Sort @ FileNames["*.wl", SamuelFrerichs`StructureAdaptiveEvolution`Private`usageDirectory]]
  ]
];


(* ::Section:: *)
(*Implementation loader*)


Begin["`Private`"];


$pacletRoot = ParentDirectory[DirectoryName[$InputFileName]];


(* Load order matters only for registrations: each module registers its
   metrics, artifacts, strategies and presets on top of the core
   registries. Optional modules are loaded when present. A failed
   registration is reported and the package keeps loading. *)
With[
  {directory = DirectoryName[$InputFileName]},
  Scan[
    Function[file,
      With[{path = FileNameJoin[{directory, file}]},
        If[
          FileExistsQ[path],
          Catch[
            Get[path],
            "registration",
            Function[{failure, tag},
              Message[StructureAdaptiveEvolution::regfail, file, failure];
              failure
            ]
          ]
        ]
      ]
    ],
    {
      "FitnessMetrics.wl",
      "MutationStrategies.wl",
      "Configurations.wl",
      "SeedCanonicalization.wl",
      "EventEvolution.wl",
      "Evaluation.wl",
      "ExtendedMetrics.wl",
      "CatalogStrategies.wl",
      "AdaptiveEvolution.wl",
      "Experiments.wl"
    }
  ]
];


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
