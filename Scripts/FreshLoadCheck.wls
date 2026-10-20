#!/usr/bin/env wolframscript
(* Fresh-kernel clean-load verification: the package loads without messages,
   every public symbol has a usage message, registries stay private and
   loading leaks no Global` symbols. Exits with status 1 on any failure.
   Run with: wolframscript -file FreshLoadCheck.wls *)

before = Names["Global`*"];

loadMessages = {};
Internal`HandlerBlock[
  {"Message", If[Last[#], AppendTo[loadMessages, First[#]]] &},
  PacletDirectoryLoad[ParentDirectory[DirectoryName[$InputFileName]]];
  Needs["SamuelFrerichs`StructureAdaptiveEvolution`"];
  Needs["SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`"]
];

after = Names["Global`*"];

publicMain = Names["SamuelFrerichs`StructureAdaptiveEvolution`*"];
publicViz = Names["SamuelFrerichs`StructureAdaptiveEvolution`Visualizations`*"];

missingUsage = Select[
  Join[publicMain, publicViz],
  !StringQ[ToExpression[# <> "::usage"]] &
];

leakage = Complement[after, before, {"before", "loadMessages", "after"}];
registriesPrivate = Names["SamuelFrerichs`StructureAdaptiveEvolution`$*"] === {};

Print["Main public symbols:     ", Length[publicMain]];
Print["Viz public symbols:      ", Length[publicViz]];
Print["Load messages:           ", loadMessages];
Print["Symbols without usage:   ", missingUsage];
Print["Global leakage:          ", leakage];
Print["Registries private:      ", registriesPrivate];

ok = loadMessages === {} && missingUsage === {} && leakage === {} && registriesPrivate &&
  Length[publicMain] > 0 && Length[publicViz] > 0;

Print[If[ok, "FRESH LOAD CHECK PASSED", "FRESH LOAD CHECK FAILED"]];
Exit[If[ok, 0, 1]];
