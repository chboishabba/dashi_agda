# Fallacy Obstruction Catalogue

Status: documentation and integration surface; non-promoting.

Agda modules:

```text
DASHI.Reasoning.FallacyCatalogue
DASHI.Reasoning.FallacyExamples
```

This catalogue records the typed obstruction shape for fallacy classification
inside DASHI. It is a claim-control surface: it names the argument object,
obstruction sectors, global admissibility criterion, and promotion boundary
that the Agda core/example modules preserve. It does not classify any live
public claim, issue a truth verdict, or promote a rhetorical diagnosis into a
theorem.

## Argument Object

The formal object is an argument candidate, not a free-form text label. The
core module keeps the following fields explicit:

| Field | Role |
|---|---|
| `carrier` | typed universe of statements, observations, or claims under review |
| `premiseContext` | typed source context for premises and admissible background assumptions |
| `conclusionContext` | typed target context for the conclusion |
| `premises` | finite or indexed premise support object |
| `conclusion` | target claim proposed by the argument |
| `bridge` | inference, transport, analogy, or compression map from premises to conclusion |
| `witnessPolicy` | admissible evidence policy for the selected context |
| `boundary` | declared scope, authority, and non-promotion boundary for the argument |

The important design point is that fallacy status attaches to a typed bridge
under a declared context. A slogan-level label such as "straw man" or "false
cause" is not enough; the obstruction must identify which typed dependency,
transport, scope, or evidence law failed.

## Obstruction Sectors

The catalogue should be organized as sectors. Each sector records a precise
failure mode plus the data needed to repair or reject the argument.

| Sector | Obstruction reading | Typical missing data |
|---|---|---|
| `semanticShift` | A term or predicate changes type, meaning, or fibre between premise and conclusion. | equality/transport witness, dictionary, fibre-preservation law |
| `scopeMismatch` | The conclusion exceeds the declared domain of the premises or bridge. | domain inclusion, boundary proof, qualified conclusion |
| `relevanceGap` | A premise is well-typed but does not feed the target bridge. | dependency edge, projection law, relevance witness |
| `missingBridge` | Premises and conclusion are typed, but the inference map is absent. | construction of the bridge and its law |
| `authorityGap` | The argument depends on external acceptance not present in the local receipt. | accepted authority token, provenance, reviewer or provider receipt |
| `evidenceMismatch` | The evidence object is from the wrong sample, metric, comparison law, or observable class. | comparison law, calibration, observable projection |
| `causalDirectionGap` | A dependence is used in the wrong direction or promoted from correlation to cause. | directional law, intervention model, asymmetry witness |
| `exhaustivenessGap` | A disjunction or case split is treated as complete without a covering proof. | finite cover, excluded-case audit, totality witness |
| `circularSupport` | The conclusion or an equivalent target is used as a premise or authority. | acyclic dependency graph, independent witness |
| `compressionLoss` | A compressed summary erases a distinction required by the conclusion. | loss budget, recoverability law, residual certificate |
| `promotionLeak` | A diagnostic or obstruction receipt is used as if it were a theorem or acceptance token. | explicit promotion authority or downgraded claim |

The sectors are not meant to be mutually exclusive. The global status should
join sector results with the most severe unresolved obstruction, following the
repo pattern used by residual and promotion-boundary surfaces.

## Global Admissibility Criterion

An argument candidate is globally admissible only when every sector required by
its declared boundary is closed. In prose:

```text
GloballyAdmissible argument =
  bridge is typed
  and all premise/conclusion transports preserve declared context
  and evidence satisfies the witness policy
  and authority requirements are inhabited when claimed
  and compression/rephrasing is loss-accounted
  and no sector reports contradiction, no-typed-meet, scope-exceeded, or
      promotion-leak status.
```

The expected fail-closed statuses are:

| Status | Meaning |
|---|---|
| `clean` | all required sector witnesses are present |
| `partial` | a local diagnostic is present, but at least one required witness is missing |
| `noTypedMeet` | the compared objects live in incompatible fibres or contexts |
| `scopeExceeded` | the conclusion outruns the declared boundary |
| `authorityMissing` | an external or governance authority token is required but absent |
| `compressionUnaccounted` | compression is used without a recoverability or residual account |
| `contradiction` | sector evidence directly conflicts with a required law |
| `promotionLeak` | the object is being consumed above its certified status |

Only `clean` may feed a future positive admissibility theorem. All other
statuses remain obstruction or diagnostic data.

## No-Promotion Boundary

This document is not a theorem, not an accepted classifier, and not a public
truth oracle. It does not provide:

- a canonical fallacy taxonomy theorem;
- a natural-language parser;
- an empirical claim-validation engine;
- authority to reject or accept a claim outside its typed context;
- promotion from rhetorical diagnosis to mathematical contradiction;
- promotion from a compressed summary to a fully recovered argument.

Future Agda modules should keep the same boundary. `FallacyExamples` inhabits
toy arguments and demonstrates sector joins, but the examples are not exported
as external authority receipts or general-purpose public-claim verdicts.

## Compression Interpretation

Fallacy diagnosis is useful as compression: a sector label can compress a
longer dependency failure into a short handle. That compression is admissible
only when the residual is explicit. The full typed obstruction must still
recover:

- which argument object was inspected;
- which bridge or transport failed;
- which sector recorded the failure;
- which witness would close the sector;
- which promotion boundary prevents overclaiming.

Thus "fallacy" is treated as an indexed residual class, not as a replacement
for the proof obligation. A compact label may appear in summaries, but the
formal object remains the typed obstruction receipt.

## Integration Notes

The core and example modules are integrated in `DASHI/Everything.agda` after
targeted typechecks:

```text
import DASHI.Reasoning.FallacyCatalogue
import DASHI.Reasoning.FallacyExamples
```

Do not use this document to weaken existing promotion gates in physics,
empirical adequacy, authority, or paper-claim surfaces.

## Worker C Validation Notes

Validation for this documentation step is repository hygiene plus targeted Agda
checks for the corresponding modules:

- `agda -i . -l standard-library DASHI/Reasoning/FallacyCatalogue.agda`
- `agda -i . -l standard-library DASHI/Reasoning/FallacyExamples.agda`
- aggregate check attempted with the include paths from `dashi-agda.agda-lib`;
  it reached unrelated physics closure imports and failed in
  `DASHI/Physics/Closure/PressureBelow15SpectralProbe.agda`.
