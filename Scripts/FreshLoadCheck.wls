#!/usr/bin/env wolframscript
(* Fresh-kernel clean-load verification: public symbols present, usage
   messages attached, no Global` leakage from loading. *)

before = Names["Global`*"];

PacletDirectoryLoad[ParentDirectory[DirectoryName[$InputFileName]]];
Needs["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`"];
Needs["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`Visualizations`"];

after = Names["Global`*"];

publicMain = Names["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`*"];
publicViz = Names["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`Visualizations`*"];

Print["Main public symbols:  ", Length[publicMain]];
Print["Viz public symbols:   ", publicViz];
Print["Global leakage:       ", Complement[after, before]];
Print["Usage messages OK:    ",
  AllTrue[
    {StructureAdaptiveEvolution::usage, ValidateEvolutionConfiguration::usage,
     CanonicalMultiwayEvolution::usage, EvaluateCandidate::usage,
     ResolveAndCanonicalizeSeed::usage},
    StringQ
  ]
];
Print["Registries private:   ",
  Names["SamuelFrerichs`HypergraphGuidedAdaptiveEvolution`$*"] === {}];
