(* ::Package:: *)

(* Public symbols of Kernel/Experiments.wl, read in the public context by
   StructureAdaptiveEvolution.wl before any implementation file. *)


ExportEvolutionResult::usage =
  "ExportEvolutionResult[result, dir] writes a StructureAdaptiveEvolution result to the directory dir: result.wxf (the complete result, lossless WXF), manifest.json (the run manifest: RunID, provenance and versions, paclet git commit or null, JSON-safe normalized configuration with functions as InputForm strings, original and canonical seed, universe, rewrite semantics, canonical form, effective limits, random seed, strategies with initial and final weights, effective metric specifications, one row per candidate, verified terminal states of solution candidates, the initial-state diagnostics summary and the SHA256 of result.wxf) and summary.md (a human-readable summary). It returns <|\"Directory\" -> dir, \"Files\" -> {...}, \"WXFHash\" -> hash|>.";

ImportEvolutionResult::usage =
  "ImportEvolutionResult[dir] reads the result written by ExportEvolutionResult[result, dir] after verifying the SHA256 of result.wxf against manifest.json, and returns the result unchanged; a missing file, a hash mismatch or an unreadable result gives a Failure.";

ExperimentStoreAdd::usage =
  "ExperimentStoreAdd[storeDir, result] exports result into storeDir/runs/<RunID>/ with ExportEvolutionResult and appends a run row and one row per candidate (RunID, CandidateID, EvaluationID, EvolutionKey, Status, Rule, Fitness, front membership, ...) to storeDir/index.wxf. A RunID that is already stored gives a Failure unless \"Overwrite\" -> True.";

ExperimentStoreRuns::usage =
  "ExperimentStoreRuns[storeDir] returns a Dataset with one row per stored run.";

ExperimentStoreQuery::usage =
  "ExperimentStoreQuery[storeDir, filter] returns a Dataset of the stored candidate rows selected by filter: a Function of the row association, or an Association of criteria in which a row field (\"Status\", \"RunID\", \"Strategy\", \"FrontMembership\", ...) matches a value, a list of values or a pattern and a metric name matches {min, max} (closed numeric range) or a value. ExperimentStoreQuery[storeDir] returns every candidate row.";

ExperimentStoreLoad::usage =
  "ExperimentStoreLoad[storeDir, runID] returns the hash-verified stored result of the run runID.";

ExperimentStorePreload::usage =
  "ExperimentStorePreload[storeDir] verifies every stored run and preloads its candidate behaviors (keyed by EvaluationID; TimedOut behaviors excluded) for cross-run reuse, so a later StructureAdaptiveEvolution run with \"ReuseEvaluations\" -> True reuses identical evaluations across sessions. It returns the number of preloaded behaviors.";

WilsonInterval::usage =
  "WilsonInterval[successes, trials] gives the 95% Wilson score interval {lower, upper} for a binomial proportion. WilsonInterval[successes, trials, level] uses confidence level level; trials = 0 gives {0., 1.}.";

ReplicateEvolution::usage =
  "ReplicateEvolution[opts, seeds] runs StructureAdaptiveEvolution[opts] once per random seed, keeping failed runs and runs without solutions, and returns <|\"Runs\" -> per-run summaries (RunID, seed, verified solution count, best values over verified solutions, evaluations, fresh evaluations, wall time, failure), \"SuccessFraction\" -> the fraction of runs with at least one verified solution with its Wilson interval, \"Distributions\" -> per metric the per-run best values and their quantiles, \"Results\" -> the full results, ...|>. Options: \"Metrics\" (default MultiwayStateCount, MultiwayTransitionCount, MultiwayLongestDerivation, HGMaxVerticesCount) and \"ConfidenceLevel\".";

BaselineComparison::usage =
  "BaselineComparison[opts, spec] compares guided search (adaptive strategy weights), random-mutation search (fixed uniform weights over the same strategies) and exhaustive evaluation of the canonical rules of a signature at one evaluation budget, 1 + Rounds*MutationBudget evaluations per run, from the same canonical seed with identical limits and no initial-state diagnostics. spec keys: \"Seeds\" (random seeds), \"Signature\" (default: the seed rule's signature), \"MaxExhaustiveRules\", \"Methods\", \"ConfidenceLevel\". Each method reports its success rate with a Wilson interval, evaluations to the first verified solution, solution counts, best objective values, compute cost and a measured \"Claim\".";

CandidateRobustness::usage =
  "CandidateRobustness[result, candidateID] re-evaluates a candidate with every numeric evolution limit scaled by \"CapFactors\" (default {2, 4}) and reports status changes and \"CapSensitiveQ\", evaluates it on an initial-state corpus (\"InitialStates\" -> Automatic: a seeded DiagnosticInitialStateEnsemble of the seed state with \"EnsembleSize\" (8) states, or a list of states) with termination rate and state-count distribution, and compares the EdgeToken and VertexDeletion rewrite semantics.";

RobustnessReport::usage =
  "RobustnessReport[result] runs CandidateRobustness on every finalist (the solution front, else the search front) with one shared initial-state corpus. It accepts the options of CandidateRobustness.";

DiscoveryReport::usage =
  "DiscoveryReport[result, candidateID] returns the discovery-report template of a candidate as an Association with the fields \"Candidate ID / evaluation ID\", \"Canonical rule\", \"Initial state\", \"Edge symmetry\", \"Rewrite semantics\", \"Backend and versions\", \"Limits and random seed\", \"Status and cycle evidence\", \"Constraint satisfaction\", \"State / transition / raw-event counts\", \"Lifetime (longest derivation and BFS depth) and maximum frontier\", \"Maximum state size and density\", \"Terminal-state summary\", \"Runtime\", \"Search-front / solution-front membership\", \"Initial-state robustness summary\", \"Mutation lineage\" and \"Interpretation with evidence level\", plus \"Text\" (formatted). Claims follow the status: \"verified to halt under this finite reachable exploration\" only for Halted, \"not resolved within the stated limits\" for caps and time-outs, \"cycle detected\" only with a recorded witness. The option \"Robustness\" takes Automatic (run diagnostics), None or a CandidateRobustness result.";

SeedCorpus::usage =
  "SeedCorpus[] returns the curated corpus of small seed systems, one Association per entry with \"Name\", \"Rule\", \"InitialState\", \"EdgeSymmetry\", \"SymmetryGroups\", \"Limits\", \"ExpectedStatus\" and \"Notes\".";

VerifySeedCorpus::usage =
  "VerifySeedCorpus[] re-evaluates every SeedCorpus[] entry with a fresh canonical multiway evolution and reports, per entry, whether the observed status equals ExpectedStatus; \"AllMatchQ\" is True when all match. VerifySeedCorpus[corpus] verifies a list of entries of the same form.";
