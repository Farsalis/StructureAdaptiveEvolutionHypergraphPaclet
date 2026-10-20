(* ::Package:: *)

(* Public symbols of CatalogStrategies.wl (read in the public context). The
   ten catalog strategies are opt-in: select them with "MutationStrategies" or
   with the goal preset of the same name as the strategy. *)

SymmetryConfluenceMutation::usage =
  "SymmetryConfluenceMutation[rule] proposes a symmetry/confluence mutation (catalog strategy 3, \"SymmetryConfluence\"): identify two variables, close the right-hand side under an exchange of interchangeable variables (SymmetrizeRHS), or, in the ordered and declared universes, permute the slots of one right-hand-side edge (PermuteRHS). Returns a canonically new rule or a Failure.";

BoundaryPreservationMutation::usage =
  "BoundaryPreservationMutation[rule] proposes a boundary-preservation mutation (catalog strategy 4, \"BoundaryPreservation\"): attach every right-hand-side component without a left-hand-side variable to the boundary and restore dropped left-hand-side variables (BoundaryPreserveRHS), or delete such components (DeleteDisconnectedRHS). Returns a canonically new rule or a Failure.";

TerminalDiversityMutation::usage =
  "TerminalDiversityMutation[rule] proposes a terminal-diversity mutation (catalog strategy 5, \"TerminalDiversity\"): split a repeated variable (SplitVariable), attach an asymmetric pendant, pendant-path or loop motif (AddMotif), or, in the ordered and declared universes, permute the slots of one edge (PermuteEdgeOrder). Returns a canonically new rule or a Failure.";

MeshDensityMutation::usage =
  "MeshDensityMutation[rule] or MeshDensityMutation[rule, <|\"MaxRHSDegree\" -> k|>] proposes a mesh-density mutation (catalog strategy 7, \"MeshDensity\"): close a 3- or 4-cycle (AddCycleMotif), subdivide a right-hand-side edge (AddChainMotif), or rewire one right-hand-side slot conserving the per-event growth budget (ConservationMutate); proposals raising the largest right-hand-side degree above k (default 4) are rejected. Returns a canonically new rule or a Failure.";

HomogenizingMutation::usage =
  "HomogenizingMutation[rule] proposes a homogenizing mutation (catalog strategy 8, \"Homogenizing\"): repeat a local right-hand-side template by closing the right-hand side under an exchange of interchangeable variables or twinning a right-hand-side-only variable (SymmetrizeRHS), or preserve the boundary (BoundaryPreserveRHS). Returns a canonically new rule or a Failure.";

LocalStabilityMutation::usage =
  "LocalStabilityMutation[rule] proposes a local-stability mutation (catalog strategy 10, \"LocalStability\"): keep a consumed left-hand-side edge on the right-hand side (PreserveMotif), or require and rewrite unchanged a new edge over left-hand-side variables (AddStableSubstructure). Returns a canonically new rule or a Failure.";

DegreeBalancingMutation::usage =
  "DegreeBalancingMutation[rule] proposes a degree-balancing mutation (catalog strategy 12, \"DegreeBalancing\"): split a right-hand-side occurrence of the most reused right-hand-side variable (SplitVariable), or reroute one of its right-hand-side edges to a least-used variable (ReduceVariableReuse). Returns a canonically new rule or a Failure.";

HubSeedingMutation::usage =
  "HubSeedingMutation[rule] or HubSeedingMutation[rule, <|\"StarEdges\" -> {min, max}|>] proposes a hub-seeding mutation (catalog strategy 13, \"HubSeeding\"): merge a variable into the most reused right-hand-side variable (IdentifyVariables), or attach min to max new edges to it (AddStarMotif, default {1, 2}). Returns a canonically new rule or a Failure.";

HubPruningMutation::usage =
  "HubPruningMutation[rules] or HubPruningMutation[rules, <|\"ContractionDegree\" -> k|>] proposes a hub-pruning mutation of a rule or rule set (catalog strategy 14, \"HubPruning\"): add a contraction rule that rewrites a star of k edges into a path over its leaves (ContractionRule, AddRule; k Automatic follows the largest right-hand-side degree), or delete one member of a rule set with at least two members (DeleteRule). Returns a canonically new rule set or a Failure.";

CausalInvarianceStyleMutation::usage =
  "CausalInvarianceStyleMutation[rules] proposes a causal-invariance-style mutation of a rule or rule set (catalog strategy 15, \"CausalInvarianceStyle\"): symmetrize the right-hand side or preserve the left-hand-side boundary of one member rule (SymmetrizeRHS, BoundaryPreserveRHS), or add the inverse of a member as a new rule (AddInverseRule). Returns a canonically new rule (set), an association with \"Rule\" and \"Details\" (\"RuleSetMember\") for a member mutation, or a Failure.";
