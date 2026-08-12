# Future equivalence, dynamic residuals, and stroboscopic contraction — Round 13

This tranche advances the dynamic-provenance line beyond one-off quotient records. It formalizes the canonical relation induced by *all future consumer-visible observations*, proves its universal kernel property, gives actual factorization when a section is constructively available, closes dynamic projection composition over finite traces, and instantiates the resulting ideas in phased lattices, spoken-word ambiguity, Wikidata repair, path-dependent accessibility, finite residual optimization, global C3 frustration, and a concrete contractive depth wheel.

## 1. Canonical future observation language

`DASHI.Core.FutureObservationLanguageQuotientExact` works directly over the repository's proof-bearing `DependentActionSystem`, which may be nondeterministic. Rather than assuming a hidden deterministic step, it defines a trace-indexed future observation language:

`FutureObservation system project x actions observation`

is inhabited exactly when some admissible execution of `actions` from `x` reaches a state with the declared observation.

Two states are `FutureObservationEquivalent` iff these languages coincide for every action trace and observation. Reflexivity, symmetry, and transitivity are proved constructively.

The key universal property is kernel-level:

> every projection certified as future-language safe has its equality kernel contained in `FutureObservationEquivalent`.

Therefore future-language equivalence is the largest relation that may be collapsed without identifying states with different consumer-visible future languages. This is the constructive relation-level form of the coarsest dynamically sufficient quotient.

No quotient HIT, function extensionality, or choice principle is assumed.

When an application supplies a concrete quotient presentation and a section of the coarse projection, `sectionedSafeProjectionFactors` constructs an actual factor map into the future-equivalence quotient code. The section is explicit precisely so the theorem does not hide a choice principle.

## 2. Dynamic projection composition

`DASHI.Core.DynamicProjectionCompositionExact` treats the complementary functional/deterministic case. `DynamicProjection` requires a commuting square for every action:

`project(stepX a x) = stepY a (project x)`.

The module proves this commutation for every finite trace and proves that dynamically compatible projections compose. Hence for

`X --pi1--> Y --pi2--> Z`

with both action squares commuting, the composite also commutes with all traces.

This is quotient compatibility only. It is intentionally separate from metric contraction.

## 3. Minimal residual becomes an optimization theorem

`DASHI.Core.FiniteOptimalResidualSelectorExact` builds on the hidden-phase zero-residual no-go. In the explicit candidate family

- visible only, cost 0;
- phase only, cost 1;
- phase plus duplicated visible state, cost 2;
- full fine-state receipt, cost 3;

only the latter three receive safety certificates, and the phase-only receipt is proved no more expensive than every other certified-safe candidate. Its exact reopening certificate is imported from `MinimalDynamicResidualExact`.

This is a finite exact MDL-like optimization theorem over certified-safe residual schemes, not a universal minimization theorem.

## 4. Exact versus relevant residual complexity

`DASHI.Cognition.PNF.ExactVsRelevantResidualExact` makes an important distinction concrete. For the bounded consumer asking only "who was seen?", the two telescope parses are relevant-equivalent, so residual cost 0 is enough to preserve that answer. Exact reconstruction of the represented semantic branch still requires the parse coordinate, cost 1.

Thus consumer-relevant residual complexity can be strictly lower than exact residual complexity.

## 5. Spoken-word dynamic insufficiency

`DASHI.Cognition.PNF.SpokenTelescopeConsumerProjectionExact` gives a complete finite semantic example for:

> "I saw John with the telescope."

The instrumental and possession parses both project to `John` for the query "who was seen?" but differ for "who had the telescope?". A later discourse action switches the consumer-visible query to telescope holder and exposes the hidden parse distinction.

So present query equality is explicitly weaker than future semantic equivalence. The parse is retained as a reopenable residual.

## 6. Path-dependent accessibility

`DASHI.Core.PathDependentAccessibilityExact` proves the generic provenance-conditioned transition-geometry claim in finite form. Two states expose the same current Boolean observation but carry different history coordinates. The same probe action then reaches different visible futures because history selects a different accessibility kernel.

No theorem promotes inaccessibility to nonexistence.

## 7. Global C3 constraint obstruction

`DASHI.Cognition.PNF.ConstraintNetworkObstructionExact` moves beyond pairwise phase mismatch. The triangle constraints

- `A = B`;
- `B = C`;
- `A = next(C)`

are globally unsatisfiable because the first two imply `A = C`, while the third would force a fixed point of the order-three successor map.

For the indicator violation potential, every assignment has cost at least 1 and an explicit assignment attains cost 1. Hence the global minimum is strictly positive because of incompatible constraints, not merely asynchronous phase labels.

## 8. Phased relational evidence propagation

`DASHI.Cognition.PNF.PhasedRelationalEvidencePropagationExact` reuses the existing signed `TypePressure` machinery. At fixed node, fixed representation depth, and fixed process phase, an H3 cell with empty pressure is semantically neutral. Expanding to H6 and adding one positive second-hop predicate-role contribution changes the derived semantic phase to reinforcing while process phase remains unchanged.

This is the exact finite theorem that a role may become legible only at a wider relational horizon.

## 9. Wikidata bounded repair mini-world

`DASHI.Cognition.PNF.WikidataTypePressureMiniWorldExact` separates declared ontology from relational-role evidence. When a node declared as an event series participates like an edition, or conversely, the bounded repair endpoint is `underspecifyType`; mismatch evidence does not automatically promote a latent replacement type.

This is the finite regression for:

`wrongly specific < correctly underspecified`.

It is not a claim about a particular live Wikidata item.

## 10. Concrete stroboscopic contraction

`DASHI.Foundations.DepthWheelStroboscopicContractionExact` closes the previously open distinction between address-wheel isometry and depth-evolution dynamics.

On the existing `Base369State` ultrametric carrier, define the three depth-wheel phases as:

- F0 = identity;
- F1 = identity;
- F2 = the existing strict `base369Kernel` contraction.

Then

`W = F2 o F1 o F0`

is definitionally `base369Kernel`, so the existing contraction theorem gives

`d(Wx, Wy) <= pred(d(x,y))`.

The stroboscopic sequence sampled at `3q` satisfies the one-wheel recurrence and contracts at every macro step.

This proves existence of a genuinely contractive depth-evolution wheel. It does not claim all depth wheels contract and does not alter the independent p7 address-wheel isometry theorem.

## Claim boundary

The tranche does not claim:

- a set-quotient construction without an explicit presentation;
- a universal minimal sufficient statistic theorem;
- deterministic semantics for the repository's proof-bearing action system;
- a theorem about all natural-language parses;
- automatic Wikidata ontology truth;
- a clinical trauma model;
- contraction of every depth-wheel system.

The strengthened master statement is:

> **A distinction is safe to forget exactly to the extent that collapsing it preserves the complete consumer-visible future language; if exact or relevant reopening is still needed, retain the least-cost residual for which that obligation is proved.**
