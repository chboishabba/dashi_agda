# Cross-ontology contradiction attribution weld

This tranche turns the existing Wikidata/PNF derivation machinery into an
end-to-end attribution surface for structural ontology diagnostics.

The target question is not merely:

> did a contradiction occur?

It is:

> against a pinned source ontology, concrete transcription, explicit alignment,
> and target graph, which layer supports/refutes the scoped claim and which
> required obligations remain open?

## Existing DASHI reused

No parallel epistemic theory was introduced.  The implementation reuses:

- `DASHI.Algebra.DisagreementFourViewBoundary.PolarAssessment` for the two-bit
  `(supports P, supports not-P)` carrier;
- `DASHI.Interop.WikidataDerivationFibreBridge` for claim-centred derivations,
  axes, provenance, obligations and the four outcomes `satisfied`, `violated`,
  `both`, `undetermined`;
- `LeanWikidataSourceRegressionBridge` for independently certified source-KB and
  bad-alignment negative examples;
- `LeanWikidataExistingContentAudit` for source/input-graph matching;
- `LeanWikidataRdfExactnessBridge` for representation exactness;
- `LeanWikidataAlignmentBridge` for explicit subclass/instance/disjointness
  alignment contracts;
- `LeanWikidataWholeBridge.sourceMismatchCannotManufactureConflict` for the
  open-world non-promotion boundary.

## Support squares before trits

`DASHI.Interop.WikidataDerivationSupportSquareExact` welds the existing
`PolarAssessment` carrier to the existing derivation-fibre outcomes.

The four states remain distinct:

```text
(false,false)  neither / undetermined
(true,false)   support only / satisfied
(false,true)   refutation only / violated
(true,true)    conflict / both
```

The old `EpistemicTrit` projection remains useful as a display/review surface,
but it is deliberately lossy:

```text
(true,true)   -> unresolved
(false,false) -> unresolved
```

Thus conflict and ignorance must be distinguished before trit collapse.
Opposite certified derivations are pooled by coordinatewise Boolean OR, yielding
`(true,true)`.

This matches the later supplied JMD/Aristotle source:

- **James Michael DuPont / Aristotle**,
  `RequestProject.Epistemic.Tetralemma`;
- source SHA-256
  `d043a72b73401c8d7642bca4683f3a12939fb208a2a4b7aeade09574873ac512`;
- exact source theorems include `Epistemic.collapse_not_injective` and
  `Epistemic.merge_then_collapse_ne_collapse_then_merge`;
- no DOI is asserted for the supplied source artifact.

`LeanWikidataLatestEpistemicConformanceBridge` additionally pins the later
Observer, Quotient, ClassAlgebra, Alignment, Lens, ParentingFibres and
ParentingAuthority source modules and their load-bearing theorem contracts.

## Four attribution layers

`CrossOntologyContradictionAttributionExact` uses one `ClaimBase` with four
explicit derivation axes:

1. source ontology;
2. source-to-concrete transcription;
3. cross-ontology alignment;
4. target graph.

Each layer has its own derivation polarity, evidence, provenance and obligations.
The generic alignment-local stress witness proves:

```text
source        support-only
transcription support-only
alignment     refute-only
target        support-only
```

while the pooled support square is `(true,true)` / `both`.

A trit presentation of the same pool is merely `unresolved`; the derivation
fibre still identifies alignment as the refuting layer.

Missing evidence is `neither`, not refutation.

## Full finite-KB disjoint-union contract

The later JMD source
`RequestProject.Wikidata.ClassAlgebra` (SHA-256
`18c413bdd2720de4e60797a953168d28f5a8b93ad046d01326989ed3a8ca27c9`)
defines:

```text
IsUnionOn kb c ms :=
  every member is a subclass of c
  AND every known entity that is an instance of c belongs to some member

IsDisjointUnionOn kb c ms :=
  IsUnionOn kb c ms
  AND distinct members are pairwise disjoint on the known finite carrier
```

and proves `Wikidata.dunOk_iff` for its executable checker.

`DisjointUnionLatticeJMDBridgeExact` therefore keeps three independent
diagnostic coordinates:

- component-not-subclass;
- known-instance coverage/exhaustivity;
- pairwise known disjointness.

A crucial scope boundary is retained: coverage is over the finite known KB
carrier.  It is not a closed-world claim that the list contains every possible
real-world instance.

The SensibLaw sibling tranche implements the same three checks at runtime while
reusing its existing `P2738`/`P11260` overlap and culprit diagnostics.

## Alignment adequacy is inference-language indexed

The later JMD Alignment source separates two facts that should not be collapsed:

- `alignOk_iff` checks mapped subclass-edge obligations;
- `disjoint_reflect` requires an additional source-instance -> target-instance
  transport hypothesis together with target disjointness.

`InferenceLanguageIndexedAlignmentSafetyExact` therefore gives a constructive
countermodel:

```text
safe for subclass language = true
safe for disjointness language = false
```

for the same alignment profile.

Hence there is no useful intrinsic Boolean `goodMapping` independent of the
inference language being transported.

## Literal BFO / Wikidata control

`BFOContinuantOccurrentWikidataAttributionExact` pins the source side to:

- **Basic Formal Ontology (BFO 2020)**;
- BFO-ontology development source;
- `BFO-ontology/BFO-2020` commit
  `0900316ea9d330f599bd110f7f6504ed33a87fc8`;
- source path `21838-2/owl/bfo-core.ttl`;
- standard context **ISO/IEC 21838-2:2021 — Basic Formal Ontology (BFO)**;
- no DOI is asserted for the source TTL/standard artifact.

The pinned source states that `BFO_0000002` continuant is a subclass of entity
and `owl:disjointWith BFO_0000003` occurrent.

The corresponding Wikidata identifier surface is:

```text
Q35120     entity     -> P12602 0000001
Q103940464 continuant -> P12602 0000002
Q67518978  occurrent  -> P12602 0000003
```

The important result is a *non-manufactured contradiction*:

```text
source        satisfied
transcription satisfied
alignment     undetermined
target        undetermined
```

The alignment remains open because the explicit instance-transport premise of
`Wikidata.Alignment.disjoint_reflect` has not been supplied.  The target remains
open because project intent to add BFO-related disjointness constraints is not
promoted to a checked target-graph fact.

Therefore the same mapping can currently serve the weaker subclass/identifier
language while remaining unlicensed for the stronger disjointness language.

## Runtime handoff and acquisition boundary

The SensibLaw branch `agent/wikidata-disjoint-union-attribution` adds:

- `src/ontology/wikidata_disjoint_union.py`;
- `src/ontology/wikidata_contradiction_attribution.py`;
- deterministic scripts and regressions;
- `data/ontology/bfo_wikidata_continuant_occurrent_attribution_v1.json`.

A bounded runtime diagnostic is candidate evidence by default.  Passing or
failing `finite_dun_ok` is not automatically promoted into target-ontology
support/refutation unless acquisition completeness has explicitly been certified
for the scoped `P2738/P11260/P279/P31` claim.

This preserves the end-to-end distinction:

```text
source fact
!= acquisition/transcription
!= alignment
!= target graph
!= derived structural diagnostic
!= global world truth/edit authority
```

## Cross-kernel parent regression

PR #581 now also contains
`ProgenitorParentLatestJMDConformanceExact`, pairing the later source-pinned JMD
ParentingFibres/ParentingAuthority theorem contracts with actual Agda proof terms
already established on that branch for:

- parent-slot non-separation;
- hidden legal finalisation;
- residual motion under exact reopening;
- authority-route nonfactorability;
- coarse authority-policy unsafety.

The bridge states mathematical contract conformance only.  It does not identify
Lean and Agda proof terms or promote imported theorem metadata into world-truth
authority.
