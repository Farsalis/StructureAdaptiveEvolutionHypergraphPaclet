# Changelog

## 2.0.0

Defaults, statuses and evaluation identities changed, so stored evaluations from 1.0.0 are not reused.

### Evaluation and identity
- New `"StateCap"` status and `"MaxStates"` limit; caps never certify terminal states.
- Exact longest derivation (`MultiwayLongestDerivation`, the default lifetime objective); BFS depth
  (`MultiwayLifetime`) is now a diagnostic. Cycle witnesses, transition multiplicities, optional raw
  event records.
- New `"Exact"` canonical form (default), with automorphism pruning and vectorized refinement.
  `"Native"` (`CanonicalHypergraph`) remains available; with Hypergraph 1.2.3 it is not invariant on
  some 3-ary states.
- Cache and evaluation identities cover every behaviour-changing setting and the evaluator, paclet,
  Hypergraph and Wolfram versions; fitness is cached by effective metric specifications.
- Matching and multiway expansion run within the time left, so `"TimeConstraint"` holds inside a step.

### Universes and rules
- Unordered rule sets; `"Declared"` universe with per-arity slot-symmetry groups.
- In the unordered universe, rules that differ only by duplicate right-hand edges (also up to slot
  order) have one canonical form; left-hand duplicates and ordered/declared multiplicities are kept.
- `RewriteEventEvolution` (event and edge identities, update orders, causal graphs),
  `MultiwayEvolutionGraph`, `BranchialGraphs`.

### Search
- Target constraints require an explicit `"Tolerance"`; numeric Maximize/Minimize constraints require
  a `"Threshold"`; Boolean Minimize constraints fixed.
- `"MetricOverrides"`, `"StrategyOptions"`, `"AdaptiveWeights"`, `"MissingObjectivePolicy"`,
  `"CompromisePolicy"`, `"Parallelization"`, `"ReuseEvaluations"`, `"ResumeFrom"`.
- Default goal adds `MultiwayTransitionCount` and `MultiwayLongestDerivation`; geometry metrics return
  `Missing["InsufficientStructure"]` on tiny states.
- GrowthBudget also proposes ConservationMutate (option `"ConservationProbability"`, default 1/3),
  and its `"AddedEdgesRange"` option now takes effect.
- Ten catalog strategies (3–15) with 17 new operators, including rule-set operators, each with a goal
  preset that promotes its primary objectives (presets may carry `"MetricOverrides"`).
- `"RandomSeed"` -> `Automatic` records the drawn seed; provenance records the run ID, versions,
  git commit, exact applied operators, mutation diffs, proposal failures, front membership and
  history, a performance profile and a resume state.

### Analysis and experiments
- 33 diagnostic metrics, among them `MotifPersistence` (persistence of the motif a rule keeps,
  following edges through rewrites that write them back), `HubPersistence` (the Hub-seeding
  objective) and `EdgeSurvivalRate`; `ClassifyCandidate` with provisional criteria.
- `CanonicalFormSelfTest`.
- Export/import with run manifests, experiment store with cross-run reuse, replication with Wilson
  intervals, budget-matched baselines, robustness reports, discovery reports, seed corpus.
- `EvolutionDashboard`, `StrategyWeightPlot`, `FrontHistoryPlot`.

### Fixes
- Any numeric value no longer satisfies a constraint.
- Scripts load the current context; the Registry seed path no longer fails on
  `ResourceObject::updavb`.
- The spatial projection keeps vertices that occur only in one-vertex hyperedges.
- Configuration validation is idempotent.

### Packaging and documentation
- MIT `LICENSE`; `build/` is no longer tracked.
- Reference pages for all 86 public symbols, a guide page and a tutorial.

## 1.0.0

Initial version: adaptive Pareto search with seven mutation strategies over a canonical BFS
multiway evaluator.
