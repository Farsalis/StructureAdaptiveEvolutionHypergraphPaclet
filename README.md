# Structure-Adaptive Evolution for Hypergraphs

<img width="6849" height="2011" alt="wsri_picture_poster_for_sp" src="https://github.com/user-attachments/assets/2fd3b7ea-ca6b-4aa4-8e7a-7791cce780b0" />

A Wolfram Language paclet for adaptive, multi-objective search over hypergraph rewriting rules.
Every candidate rule is evaluated by an exact, canonical, breadth-first exploration of its
multiway system, so the search can tell systems that verifiably halt apart from systems that
merely ran out of budget. The paclet also provides analysis tools for termination, confluence and
update-order behaviour, an experiment layer for reproducible and statistically honest results, and
result-only visualizations.

- Paclet: `SamuelFrerichs/StructureAdaptiveEvolution`, version 2.0.0
- Requires: Wolfram Language 15+, the `WolframInstitute/Hypergraph` paclet (tested with 1.2.3)
- Contexts: ``SamuelFrerichs`StructureAdaptiveEvolution` `` and
  ``SamuelFrerichs`StructureAdaptiveEvolution`Visualizations` ``

## Loading

From a source checkout:

```wl
PacletDirectoryLoad["path/to/StructureAdaptiveEvolutionPaclet"];
Needs["SamuelFrerichs`StructureAdaptiveEvolution`"]
Needs["SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`"]
```

Loading the visualizations context also puts the main context on `$ContextPath`.

## Quick start

```wl
result = StructureAdaptiveEvolution[
  "Rule" -> ({{1, 2}, {2, 3}} -> {{1, 3}}),
  "InitialState" -> {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
  "Rounds" -> 2,
  "MutationBudget" -> 10,
  "EvolutionLimits" -> <|"MaxGenerations" -> 6, "MaxEvents" -> 500|>,
  "RandomSeed" -> 2026
];

Counts[Lookup[result["Candidates"], "Status"]]
Lookup[result["SolutionParetoFront"], "Rule"]
EvolutionDashboard[result]
```

`Scripts/DemoAdaptiveEvolution.wls` runs a fixed-seed demonstration from the command line.

## Concepts

**States and rules.** A state is a list of hyperedges, each a list of vertices. A rule
`lhs -> rhs` rewrites a match of `lhs`; vertices that occur only on the right-hand side are created.
A list of rules is an unordered rule set: each member has its own variables and any member can fire.

**Universes** (`"EdgeSymmetry"`):

| Universe | Hyperedge | Duplicate edges |
|---|---|---|
| `"Unordered"` (default) | unordered set of slots | removed (simple hypergraphs) |
| `"Ordered"` | ordered tuple | kept (multisets) |
| `"Declared"` | ordered ports with per-arity slot-symmetry groups (`"SymmetryGroups"`, e.g. `<\|3 -> "Cyclic"\|>`) | kept |

**Canonical forms** (`"CanonicalForm"`). States and rules are identified up to isomorphism by a
canonical form. The default `"Exact"` backend is an individualization–refinement canonical
labelling with automorphism pruning: it is complete (equal forms exactly for isomorphic inputs) and
invariant, and it is property-tested against brute force (`CanonicalFormSelfTest`). `"Native"` uses
`CanonicalHypergraph` from the Hypergraph paclet. With Hypergraph 1.2.3 that function is not
invariant on some 3-ary states, so isomorphic copies can receive different forms; its forms are
always isomorphic copies of their input, so it can only over-count states. In the unordered universe
the right-hand side of a rule is read as a simple hypergraph, as the state it produces is, so rules
that differ only by duplicate right-hand edges have one identity.

**Rewrite semantics** (`"RewriteSemantics"`): `"EdgeToken"` (default; matched edges are consumed,
vertices stay) or `"VertexDeletion"` (vertices left without edges disappear).

**Canonical multiway evolution and statuses.** `CanonicalMultiwayEvolution` explores every
rewrite order breadth first, merging isomorphic states, within the limits `"MaxGenerations"` (10),
`"MaxEvents"` (1000), `"MaxStates"` (Infinity) and `"TimeConstraint"` (30 s). Its status is:

| Status | Meaning |
|---|---|
| `"Halted"` | the reachable state space was exhausted and is acyclic: **verified to halt under this finite reachable exploration** |
| `"CycleDetected"` | the explored states graph has a cycle (witness recorded): an infinite derivation exists |
| `"GenerationCap"`, `"EventCap"`, `"StateCap"`, `"TimedOut"` | **not resolved within the stated limits** |
| `"Invalid"` | a rewrite failed; no conclusion |

A capped exploration never reports its unexplored frontier as terminal. `"LongestDerivation"` is
exact for a halted evolution; the breadth-first discovery depth (`MultiwayLifetime`) is kept only as
a diagnostic.

## The search

`StructureAdaptiveEvolution` proposes `"MutationBudget"` candidates per round. Each proposal applies a
mutation strategy, chosen with probability given by adaptive strategy weights, to a parent from an
archive (search front, per-objective champions and a few random valid candidates). Every candidate is
evaluated once by `EvaluateCandidate`, with caching keyed by every behaviour-changing setting and
by the evaluator, paclet, Hypergraph and Wolfram versions.

- The **search Pareto front** is computed over all valid candidates; the **solution Pareto front**
  contains only candidates that halted and satisfy every hard constraint. A capped candidate can be on
  the search front, never on the solution front.
- Metrics have a stage (`"Objective"`, `"Constraint"` or `"Diagnostic"`) and a direction
  (`"Maximize"`, `"Minimize"`, `"Target"`, `"Range"`). A `"Target"` constraint needs an explicit
  `"Tolerance"`; a numeric `"Maximize"`/`"Minimize"` constraint needs a `"Threshold"`. Diagnostics
  become objectives only explicitly, through `"MetricOverrides"` or a goal preset.
- Missing metric values follow `"MissingObjectivePolicy"`: `"Worst"` (default) or `"Exclude"`.
- `"RandomSeed"` -> `Automatic` draws a seed and records it, so every run can be replicated.
  `"ResumeFrom"` continues a run exactly; `"ReuseEvaluations"` reuses evaluations (also across
  sessions, see the experiment store); `"Parallelization"` evaluates candidates in parallel.

The result records the run ID, configuration, seed (with Registry code for Registry seeds), every
candidate with its exact applied operators, rule diff, status evidence, fitness and identities, both
fronts with their history, champions, strategy-weight history, lineage, proposal failures, a
performance profile, provenance (versions, git commit of the paclet source, random seed, state
equivalence) and a resume state.

### Mutation strategies

| Strategy | Catalog | In the default goal |
|---|---|---|
| GrowthBudget (with ConservationMutate) | 1 | yes |
| GrowThenConstrain | 2 | yes |
| SymmetryConfluence | 3 | opt-in |
| BoundaryPreservation | 4 | opt-in |
| TerminalDiversity | 5 | opt-in |
| OverlappingMatch | 6 | yes |
| MeshDensity | 7 | opt-in |
| Homogenizing | 8 | opt-in |
| DelayedTermination | 9 | yes |
| LocalStability | 10 | opt-in |
| RuntimeThrottling | 11 | yes |
| DegreeBalancing | 12 | opt-in |
| HubSeeding | 13 | opt-in |
| HubPruning (rule sets) | 14 | opt-in |
| CausalInvarianceStyle (rule sets) | 15 | opt-in |
| VariableRewiring | — | yes |
| OrderedEdgePermutation (ordered/declared universes) | — | yes |

GrowthBudget adds an RHS-only variable and one or two RHS edges or, with probability
`"ConservationProbability"` (default 1/3), applies ConservationMutate, which rewires one RHS slot
while keeping the LHS, the number of RHS edges and the number of created vertices.

The default goal `"LargeFiniteTerminating"` looks for large multiway systems that verifiably halt.
Each opt-in strategy has a goal preset of the same name (`"Goal" -> "HubPruning"`, …) that selects
it and promotes the catalog's primary objectives; your own `"MetricOverrides"` win per metric.

### Metrics

Core: `HaltedWithinCapQ`, `MultiwayStateCount`, `MultiwayTransitionCount`,
`MaxMultiwayFrontierSize`, `MultiwayLongestDerivation`, `MultiwayLifetime`, `TerminalStateCount`,
`NonIsomorphicTerminalStateCount`, `HGMaxVerticesCount`, `HGMaxEdgesCount`,
`HGMaxEdgeToVertexRatio`, `HGMaxDensity`, `HGMaxEdgeMultiplicity`, `Runtime`.

Diagnostics (33): structural (components, effective dimension and its variance, degrees, final-state
summaries), branching and confluence (out-degree entropy, reconvergence, resolved critical pairs,
`CausalInvariantWithinCapQ`), causal (merge ratio, dependency entropy, rewrite activity), update
order (state-outcome and causal-graph sensitivity, terminal outcome count), local persistence
(`LocalComponentLifetimeMean`/`Max`, `MotifPersistence`, `HubPersistence`, `EdgeSurvivalRate`) and branchial
(`BranchialMeanDegree`, `MeanBranchialDistance`). Each is defined with an explicit aggregation and
explicit `Missing` cases.

`MotifPersistence` measures how much of a motif survives from step to step in the event-level
evolution. By default the motif is the one the rule keeps: its left-hand edges that the right-hand
side writes back unchanged, which is what the Local-stability operators create. Edges are followed
through their lineage: an edge that a rewrite writes back unchanged stays the same edge, while a
motif destroyed and rebuilt from new edges does not count as persisting. A rule that keeps no edge
gets `Missing["NoKeptMotif"]`; the `"Motif"` parameter measures any other motif. `HubPersistence`
follows hub vertices (by default, vertices with at least 3 edges) whatever happens to their edges,
and is the Hub-seeding goal's objective in place of the catalog's motif persistence.
`EdgeSurvivalRate` is the share of edges that no event touches in a step.
Geometry metrics use the unordered simple projection of a state in every universe.

## Analysis tools

- `RewriteEventEvolution` — single-way evolution with event and edge identities, update orders and
  causal graphs; `MultiwayEvolutionGraph`, `BranchialGraphs`.
- `ClassifyCandidate` — labels such as `"RichTerminalStates"` or `"CausalInvariant"` with
  three-valued outcomes (`True`, `False`, `Undetermined`). **The default thresholds
  (`DefaultClassificationCriteria[]`) are provisional and under review.** Labels are structural
  classifications within the explored limits, not evidence of physical properties.

## Experiment protocol

- `ExportEvolutionResult` / `ImportEvolutionResult` — lossless WXF plus a JSON run manifest and a
  readable summary, hash-checked on import.
- `ExperimentStoreAdd`, `ExperimentStoreRuns`, `ExperimentStoreQuery`, `ExperimentStoreLoad`,
  `ExperimentStorePreload`, `ClearPreloadedEvaluations` — a persistent experiment store with
  cross-run reuse of identical evaluations.
- `ReplicateEvolution` (multi-seed success fractions with `WilsonInterval`s) and
  `BaselineComparison` (guided vs random mutation vs exhaustive enumeration at matched budgets).
- `CandidateRobustness`, `RobustnessReport` — cap sensitivity, initial-state corpus, rewrite
  semantics.
- `DiscoveryReport` — the discovery-report template with claim discipline.
- `SeedCorpus`, `VerifySeedCorpus` — a curated corpus of small systems with verified statuses.

Claim discipline throughout: "verified to halt under this finite reachable exploration" only for
`"Halted"`; "not resolved within the stated limits" for caps and time-outs; "cycle detected" only
with a recorded witness; the state equivalence is always named; no physical or all-initial-state
conclusions.

## Visualizations

`EvolutionDashboard`, `EvolutionSummaryTable`, `ParetoFrontPlot`, `RuleLineageGraph`,
`CandidateEvolutionPlot`, `FitnessTrajectoryPlot`, `StrategyWeightPlot`, `FrontHistoryPlot` — all
built from stored results; nothing is re-evaluated.

## Formal guarantees

The status logic has been formalized for an abstract model of the explorer (states, one-step rewrite
relation, canonical keys, visited set, explored edges) and machine-checked in Lean 4 with Mathlib.
The proofs are kept in a separate Lean workspace, not in this repository. In that model:

- if the canonical form is complete and invariant (the `"Exact"` backend), a `"Halted"` status implies
  that every derivation from the initial state is finite and shorter than the number of explored
  states, that the longest derivation equals the longest path of the explored graph, that terminal
  states are reported soundly, and that a detected cycle gives an infinite derivation;
- the key-completeness hypothesis is necessary (a counterexample is formalized);
- when canonical forms are only isomorphic copies (the `"Native"` backend), `"Halted"` remains sound
  and the longest-derivation value remains exact, but key-level statements (such as "one terminal
  key") need not hold;
- with joinable forks, Newman's lemma gives a unique terminal outcome up to isomorphism.

That this code implements the model is tested, not machine-checked.

## Tests and checks

```
wolframscript -file Scripts/FreshLoadCheck.wls     # clean load, usage messages, no leakage
```

Run the test files in `Tests/` with `TestReport` (306 tests in 15 files at version 2.0.0), e.g.

```wl
PacletDirectoryLoad["path/to/StructureAdaptiveEvolutionPaclet"];
TestReport /@ FileNames["*.wlt", "path/to/StructureAdaptiveEvolutionPaclet/Tests"]
```

## Documentation

Reference pages for every public symbol, the guide page *StructureAdaptiveEvolution* and the tutorial
*Adaptive search over hypergraph rewriting rules* are in `Documentation/English`.

## Known limitations

- The exact canonical form is fast on typical states (milliseconds for tens of vertices) but takes
  seconds on large, highly symmetric states (about 12 s for a 255-vertex binary tree).
- `RewriteEventEvolution` matches by building successor states, which is slow on very large states
  (`MotifPersistence` matches its motif at every step the same way);
  matching respects `"TimeConstraint"`, but the canonical form of the final state is computed after
  the limit.
- Classification thresholds are provisional.
- Registry seeds need the Wolfram Physics Project registry resource.
