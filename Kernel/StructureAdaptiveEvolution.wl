(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["SamuelFrerichs`StructureAdaptiveEvolution`", {"WolframInstitute`Hypergraph`"}];


(* ::Subsection:: *)
(*Public symbols*)


StructureAdaptiveEvolution::usage =
  "StructureAdaptiveEvolution[opts] runs an adaptive Pareto search over mutated hypergraph rewrite rules and returns a result association with candidates, fronts, weights, lineage, and logs.";

ValidateEvolutionConfiguration::usage =
  "ValidateEvolutionConfiguration[assoc] returns a normalized configuration association or a Failure.";

ResolveAndCanonicalizeSeed::usage =
  "ResolveAndCanonicalizeSeed[config] resolves explicit or Automatic rule/initial-state settings into a canonical seed association or a Failure.";

EvaluateCandidate::usage =
  "EvaluateCandidate[candidate, config] evolves a candidate rule/state pair once (with caching), computes the selected fitness metrics, and returns the completed candidate record.";

CanonicalMultiwayEvolution::usage =
  "CanonicalMultiwayEvolution[rule, state, limits] runs a canonical breadth-first multiway evolution and returns generations, states graph, terminal states, status, and cycle evidence.";

CanonicalStateForm::usage =
  "CanonicalStateForm[state] returns the canonical edge list of a hypergraph state under the active edge-symmetry universe (default: unordered hyperedges, duplicates removed). CanonicalStateForm[state, \"Unordered\" | \"Ordered\"] selects the universe explicitly.";

CanonicalRuleForm::usage =
  "CanonicalRuleForm[lhs -> rhs] returns the canonical form of a hypergraph rewrite rule as an edge-list Rule under the active edge-symmetry universe. CanonicalRuleForm[rule, \"Unordered\" | \"Ordered\"] selects the universe explicitly.";

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
  "EffectiveDimensionEstimate[hg] estimates the effective dimension from neighborhood-volume growth.";

DimensionVariance::usage =
  "DimensionVariance[hg] returns the variance of local dimension estimates.";

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
  "OrderedEdgePermutationMutation[rule] permutes the vertex positions inside one edge of an ordered rule; OrderedEdgePermutationMutation[rule, \"Left\" | \"Right\"] targets one side. Requires the ordered universe (\"EdgeSymmetry\" -> \"Ordered\").";

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


(* ::Section:: *)
(*Implementation loader*)


Begin["`Private`"];


With[
  {directory = DirectoryName[$InputFileName]},
  Scan[
    Get[FileNameJoin[{directory, #}]] &,
    {
      "FitnessMetrics.wl",
      "MutationStrategies.wl",
      "Configurations.wl",
      "SeedCanonicalization.wl",
      "Evaluation.wl",
      "AdaptiveEvolution.wl"
    }
  ]
];


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
