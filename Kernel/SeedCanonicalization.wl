(* ::Package:: *)

(* Loaded by StructureAdaptiveEvolution.wl inside the `Private` context. *)


(* ::Section:: *)
(*Canonical forms*)


(* Edge-symmetry universe. Dynamically scoped: config-taking entry points
   Block this from config["EdgeSymmetry"], so direct calls default to the
   project's original unordered convention. *)
$EdgeSymmetry = "Unordered";


(* Rewrite semantics for vertices the RHS drops. "EdgeToken" (the project
   default) follows the SetReplace/WolframModel convention: untouched edges
   keep their vertices, and a dropped vertex simply stops being mentioned.
   "VertexDeletion" opts into the WolframInstitute/Hypergraph native
   behavior, which removes a dropped vertex from every edge of the state.
   Dynamically scoped exactly like $EdgeSymmetry. *)
$RewriteSemantics = "EdgeToken";


(* The positional Hypergraph[edges, "Ordered"] form silently constructs a
   broken object in WolframInstitute/Hypergraph 1.2.3; only the option form
   is safe. *)
modeHypergraph[edges_] := Hypergraph[edges, "EdgeSymmetry" -> $EdgeSymmetry]


(* Unordered: simple hypergraphs (sorted edges, duplicates removed).
   Ordered: multiset semantics -- positions and multiplicity are semantic. *)
normalizeStateEdges[state_List] :=
  If[
    $EdgeSymmetry === "Ordered",
    state,
    DeleteDuplicates[Sort /@ state]
  ]


validHypergraphRuleQ[rule_] :=
  MatchQ[rule, (lhs_ -> rhs_) /; hypergraphStateQ[lhs] && hypergraphStateQ[rhs]]


toHypergraphRule[lhs_ -> rhs_] :=
  HypergraphRule[modeHypergraph[lhs], modeHypergraph[rhs]]


(* Application-time rule constructor. Under "EdgeToken" semantics the RHS
   hypergraph declares every rule variable as a vertex, so nothing lands in
   the paclet's deleted-vertex set and untouched edges survive rewrites
   intact. Canonicalization and matching keep using toHypergraphRule: rule
   identity does not depend on the application semantics. *)
toApplicationRule[lhs_ -> rhs_] :=
  If[
    $RewriteSemantics === "EdgeToken",
    HypergraphRule[
      modeHypergraph[lhs],
      Hypergraph[
        DeleteDuplicates @ Flatten[{lhs, rhs}],
        rhs,
        "EdgeSymmetry" -> $EdgeSymmetry
      ]
    ],
    toHypergraphRule[lhs -> rhs]
  ]


CanonicalStateForm[{}] := {}

CanonicalStateForm[state_?hypergraphStateQ] :=
  normalizeStateEdges @ EdgeList @ CanonicalHypergraph @ modeHypergraph @ normalizeStateEdges[state]

CanonicalStateForm[state_, symmetry : "Unordered" | "Ordered"] :=
  Block[{$EdgeSymmetry = symmetry}, CanonicalStateForm[state]]

CanonicalStateForm[other_] :=
  Failure[
    "InvalidHypergraphState",
    <|
      "Message" -> "The expression is not a hypergraph state.",
      "Value" -> other
    |>
  ]


CanonicalRuleForm[rule_?validHypergraphRuleQ] := Module[
  {canonical},

  canonical = CanonicalHypergraphRule[toHypergraphRule[rule]];

  EdgeList[canonical[[1]]] -> EdgeList[canonical[[2]]]
]

CanonicalRuleForm[rule_, symmetry : "Unordered" | "Ordered"] :=
  Block[{$EdgeSymmetry = symmetry}, CanonicalRuleForm[rule]]

CanonicalRuleForm[other_] :=
  Failure[
    "InvalidHypergraphRule",
    <|
      "Message" -> "The expression is not a hypergraph rewrite rule.",
      "Value" -> other
    |>
  ]


(* ::Section:: *)
(*Applicability*)


RuleApplicableQ[rule_?validHypergraphRuleQ, state_?hypergraphStateQ] :=
  toHypergraphRule[rule][modeHypergraph[normalizeStateEdges[state]]] =!= {}

RuleApplicableQ[___] := False


(* ::Section:: *)
(*Registry access (lazy)*)


wmData := wmData = ResourceFunction["WolframModelData"];

registryRules := registryRules =
  Association /@ wmData[All, {"Rule", "InitialCondition"}];


(* Single-rule entries only for the single-rule MVP. *)
singleRuleRegistryEntries[] :=
  Cases[
    registryRules,
    entry_Association /; MatchQ[entry["Rule"], {_Rule} | _Rule] :>
      <|
        "Rule" -> Replace[entry["Rule"], {r_Rule} :> r],
        "InitialCondition" -> entry["InitialCondition"]
      |>
  ]


seedResolutionFailure[message_String, details_Association : <||>] :=
  Failure[
    "SeedResolutionFailed",
    <|"Message" -> message|> ~Join~ details
  ]


(* ::Section:: *)
(*Seed resolution*)


SeedIDFromCanonicalForms[canonicalRule_, canonicalState_] :=
  Hash[{canonicalRule, canonicalState}, "SHA256", "HexString"]


buildResolvedSeed[
  source_String,
  originalRule_,
  originalState_,
  registryCode_ : Missing["NotRecorded"]
] := Module[
  {canonicalRule, canonicalState},

  canonicalRule = CanonicalRuleForm[originalRule];
  If[FailureQ[canonicalRule], Return[canonicalRule]];

  canonicalState = CanonicalStateForm[originalState];
  If[FailureQ[canonicalState], Return[canonicalState]];

  <|
    "SeedID" -> SeedIDFromCanonicalForms[canonicalRule, canonicalState],
    "Source" -> source,
    "RegistryCode" -> registryCode,
    "OriginalRule" -> originalRule,
    "OriginalInitialState" -> originalState,
    "CanonicalRule" -> canonicalRule,
    "CanonicalInitialState" -> canonicalState,
    "Rule" -> canonicalRule,
    "InitialState" -> canonicalState,
    "InitiallyApplicableQ" -> RuleApplicableQ[canonicalRule, canonicalState]
  |>
]


ResolveAndCanonicalizeSeed[config_Association] := Block[
  {
    $EdgeSymmetry = Lookup[config, "EdgeSymmetry", "Unordered"],
    $RewriteSemantics = Lookup[config, "RewriteSemantics", "EdgeToken"]
  },
  Module[
  {rule, state},

  rule = Lookup[config, "Rule", Automatic];
  state = Lookup[config, "InitialState", Automatic];

  Which[

    (* Explicit rule, explicit state: preserve originals, canonicalize both.
       Applicability is recorded, not enforced: mutation may restore it. *)
    rule =!= Automatic && state =!= Automatic,
    If[
      !validHypergraphRuleQ[rule],
      seedResolutionFailure[
        "The supplied rule is not a hypergraph rewrite rule.",
        <|"Rule" -> rule|>
      ],
      buildResolvedSeed["User", rule, state]
    ],

    (* Explicit rule, Automatic state: the canonicalized LHS is a guaranteed
       matching seed. *)
    rule =!= Automatic && state === Automatic,
    If[
      !validHypergraphRuleQ[rule],
      seedResolutionFailure[
        "The supplied rule is not a hypergraph rewrite rule.",
        <|"Rule" -> rule|>
      ],
      buildResolvedSeed["RuleInput", rule, First[CanonicalRuleForm[rule]]]
    ],

    (* Automatic rule, explicit state: select a Registry rule that actually
       matches the supplied state. *)
    rule === Automatic && state =!= Automatic,
    Module[{entries, chosen},
      entries = Quiet @ Check[singleRuleRegistryEntries[], $Failed];
      If[
        entries === $Failed || !MatchQ[entries, {__Association}],
        Return @ seedResolutionFailure[
          "The Wolfram model registry could not be retrieved."
        ]
      ];
      chosen = SelectFirst[
        RandomSample[entries],
        RuleApplicableQ[#["Rule"], state] &
      ];
      If[
        MissingQ[chosen],
        seedResolutionFailure[
          "No registry rule applies to the supplied initial state.",
          <|"InitialState" -> state|>
        ],
        buildResolvedSeed["WolframModelData", chosen["Rule"], state]
      ]
    ],

    (* Automatic rule, Automatic state: select a Registry rule-state pair,
       requiring initial applicability. *)
    True,
    Module[{entries, chosen},
      entries = Quiet @ Check[singleRuleRegistryEntries[], $Failed];
      If[
        entries === $Failed || !MatchQ[entries, {__Association}],
        Return @ seedResolutionFailure[
          "The Wolfram model registry could not be retrieved."
        ]
      ];
      chosen = SelectFirst[
        RandomSample[entries],
        hypergraphStateQ[#["InitialCondition"]] &&
          RuleApplicableQ[#["Rule"], #["InitialCondition"]] &
      ];
      If[
        MissingQ[chosen],
        seedResolutionFailure[
          "No applicable registry rule-state pair was found."
        ],
        buildResolvedSeed[
          "WolframModelData",
          chosen["Rule"],
          chosen["InitialCondition"]
        ]
      ]
    ]
  ]
  ]
]

ResolveAndCanonicalizeSeed[other_] :=
  seedResolutionFailure[
    "The configuration must be an Association.",
    <|"Value" -> other|>
  ]
