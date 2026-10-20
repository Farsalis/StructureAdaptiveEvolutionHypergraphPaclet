(* ::Package:: *)

(* Public symbols of Kernel/ExtendedMetrics.wl. Read by the package header
   in the public context before any implementation file is loaded. *)


BranchialGraphs::usage =
  "BranchialGraphs[evolution] gives an Association k -> graph with the branchial graph of every layer k of the generation-unrolled MultiwayEvolutionGraph of a CanonicalMultiwayEvolution result: its vertices are the canonical states reachable in exactly k events, with an undirected edge between two states that share a parent state in layer k - 1 (layer 0 holds the initial state alone). BranchialGraphs[evolution, depth] bounds the number of layers; BranchialGraphs[evolutionGraph] takes a MultiwayEvolutionGraph directly. Also available as the evaluation artifact \"BranchialGraphs\".";

BranchialGraph::usage =
  "BranchialGraph[evolution, k] gives the branchial graph of layer k of BranchialGraphs[evolution], or Missing[\"NoSuchLayer\", k] when the layer does not exist.";

ClassifyCandidate::usage =
  "ClassifyCandidate[candidate] applies DefaultClassificationCriteria[] to a candidate record. ClassifyCandidate[candidate, criteria] uses criteria given as Automatic, a list of default label names, or an Association label -> criterion. ClassifyCandidate[candidate, criteria, config] evaluates missing metric values under config (StructureAdaptiveEvolution options or a normalized configuration such as a run's \"Configuration\"; default: the default configuration). Metric values come from the candidate's \"Fitness\" when present and are otherwise computed with EvaluateCandidate from its \"Rule\" and \"InitialState\". The result gives, per label, an Association with \"Label\", \"Satisfied\" (True, False or Undetermined), \"Evidence\" (metric -> value), \"Criteria\", \"CriteriaStatus\" (\"Provisional\" for an unmodified default criterion, \"UserSupplied\" otherwise), \"Claim\" (a sentence that states the evidence within the explored limits), \"Status\" (the exploration status) and \"ConditionResults\". The default thresholds are provisional: the owner will revise them.";

DefaultClassificationCriteria::usage =
  "DefaultClassificationCriteria[] gives the default quantitative classification criteria, an Association with a top-level \"Status\" -> \"Provisional (owner review pending)\" and the labels \"RichTerminalStates\", \"SpaceLike\", \"Homogeneous\", \"LocallyStable\" and \"CausalInvariant\"; each label has a \"Description\" and \"AllOf\" -> {condition, ...} or \"AnyOf\" -> {{condition, ...}, ...}, a condition being <|\"Metric\", \"Test\" (\"AtLeast\", \"AtMost\", \"Equals\" or \"Within\"), \"Value\", optional \"Tolerance\" and \"Parameters\"|>. DefaultClassificationCriteria[params] overrides thresholds by name: \"MinNonIsomorphicTerminalStates\" (3), \"MinMeanTerminalVertexCount\" (5), \"TargetDimension\" (2.), \"DimensionTolerance\" (0.5), \"SpaceLikeMaxDimensionVariance\" (0.25), \"MinLargestComponentRatio\" (0.9), \"HomogeneousMaxDimensionVariance\" (0.1), \"HomogeneousMaxVertexDegreeVariance\" (1.), \"MinLocalComponentLifetimeMax\" (3), \"MinMotifPersistence\" (0.5) and \"Motif\" (Automatic). These default thresholds are provisional: the owner will revise them.";

Undetermined::usage =
  "Undetermined is the \"Satisfied\" value of a ClassifyCandidate label whose criteria can be neither confirmed nor refuted because a required metric value is Missing or failed.";
