# Digital-ESD roadmap addendum: experimental-design and claim ceilings

**Branch:** `agent/digital-esd-paper-methodology-primary-sources`

**Status:** roadmap refinement. This addendum narrows the current live roadmap around study-level evidentiary discipline. It does not create evidence or alter the requirement to reconcile the feature branch with current `master` before a large integration tranche.

## Why this changes the roadmap

The paper now has enough conceptual architecture. The main empirical risk is no longer only *which papers are found*, but *what each admitted paper is allowed to prove*.

The controlling rule is:

```text
study design + exact source + realised sample + measurement + uncertainty + scope
-> admissible claim ceiling
```

not:

```text
interesting result -> strongest narrative interpretation
```

This turns experimental-design extraction into a P0 review obligation rather than a later quality note.

## Existing repository grammar reused

The digital-ESD claim-ceiling layer reuses four canonical families:

1. `EvidenceDesignAdmissibilityExact` — study designs afford different evidence questions; there is no universal method hierarchy.
2. `ExperimentalAssertionPNFImplicationConeExact` — measured result, bounded contrast, association, causal effect, mechanism, transport and practice recommendation are separate implication edges.
3. `CausalEstimandStatisticalRealisationExact` — estimand, estimator, realised sample/estimate, uncertainty and confidence-interval coverage remain separate receipts.
4. `CausalEstimatorGuaranteesExact` — bias, consistency, dispersion, coverage and power remain separate guarantees.

The digital-ESD owners add no new probability calculus.

## New digital-ESD owners

- `DigitalESDStudyClaimCeilingExact.agda`
- `DigitalESDStudyClaimCeilingRegression.agda`
- `DigitalESDStudyClaimMethodBridgeExact.agda`

The claim profile is indexed by an exact `AttributedSource`, not a free-form citation label.

## Effective extraction structure

The existing manuscript method retains 19 top-level coordinates.

The method bridge appends a structured study-claim-ceiling coordinate:

```text
19 base coordinates + 1 claim-ceiling bundle = 20 effective top-level coordinates
```

The claim-ceiling bundle has 16 subcoordinates:

```text
source population
reported/enrolled n
analysis n
allocation
comparator
measurement validity
attrition/missingness
confounding control
implementation fidelity
multiplicity
effect size
uncertainty / confidence interval
time horizon
external validity / transport
participant role
strongest supported implication
```

Missing quantities remain explicitly unreported unless a same-object derivation receipt pays them.

## P0 — operational review completion, revised

P0 should now be executed in this order:

1. **Reconcile the digital-ESD branch with current `master` before another large formal tranche.**
2. **Translate the frozen query families into exact database-specific syntax.**
3. **Run the human sustainability challenge on search vocabulary and candidate principles.**
4. **Execute the five declared database searches and retain exact exports/counts/query receipts.**
5. **Deduplicate and screen with exclusion reasons.**
6. **For every included empirical/review source, populate the 20-coordinate extraction surface, including the 16-field study-claim ceiling where applicable.**
7. **Do not synthesize a stronger claim than any source's admitted implication edge.**

Step 6 is now a hard gate into P1 rather than optional quality annotation.

## P1 — corpus challenge and manuscript synthesis, revised

For each candidate principle and transformation-level claim:

1. collect the admitted source-specific claims;
2. retain which implication level each source actually pays;
3. preserve uncertainty, sample and transport limitations;
4. distinguish convergent evidence from repeated citation of the same upstream source;
5. distinguish a study supporting a mechanism/association from a study supporting an effect;
6. distinguish local effects from population transport;
7. distinguish learning effects from institutional/system transformation;
8. revise/narrow/split/merge/defeat the candidate principle accordingly.

A synthesis claim may therefore be narrower than the rhetoric of one of its source papers if the design receipts do not support the source's broadest prose interpretation.

## P2 — residual experimental design

New experimental design or residual coordinates should be added only when an admitted source/claim exposes a literal unmet obligation.

Examples:

- an intervention claim lacks a valid comparator;
- a causal statement lacks assignment/confounding support;
- an apparent null result is underpowered or has incompatible uncertainty semantics;
- a broad population recommendation exceeds the sampling/transport domain;
- an outcome is statistically estimated but practical significance is unpaid;
- a qualitative result is promoted into prevalence without a prevalence design;
- system transformation is inferred from a short-term individual outcome.

The existing blocked-implication / experiment-backprop machinery should be reused to express those missing obligations rather than creating a new generic experimental-design theory.

## Statistical reporting stop rules

The review should explicitly refuse:

```text
large n -> representativeness
p < threshold -> cause
narrow CI -> cause
CI -> transport
power -> truth
statistical significance -> practical significance
association -> recommendation
single positive study -> system transformation
```

Confidence intervals should be reported with their actual confidence procedure/coverage interpretation where available; an interval should not be treated as a generic visual certificate of certainty.

## Qualitative and mixed-methods stop rules

The claim ceiling is not a quantitative-only hierarchy.

Qualitative and participatory work may be the stronger source for lived experience, interpretation, acceptability, implementation and epistemic agency. Their ceiling should retain participant selection, role, context, analytic method and interpretive authority rather than forcing pseudo-quantitative uncertainty onto them.

Conversely:

```text
situated qualitative finding != population prevalence
consultation != constitutive authority
local co-design != universal transfer
```

## Attribution / genealogy rule

Every extracted design/statistical surface stays bound to the exact attributed paper.

```text
same DOI/source object + exact locator/design receipt
-> source-specific claim profile
```

but:

```text
nearby paper / review / shared author / shared construct
!= permission to fill a missing n, CI, effect size, comparator or limitation
```

Likewise, multiple visible papers tracing to the same upstream evidence should not be counted as independent corroboration.

## Relationship to externality incidence

The claim ceiling and externality-incidence audit are orthogonal:

```text
inferential precision != distributional completeness
```

A high-quality effect estimate may say little about who bears externalities. A detailed incidence account may say little about causal effect magnitude. Final synthesis must not let one pay the other.

## Current roadmap consequence

The paper has moved from:

```text
find papers -> summarize themes
```

to:

```text
find papers
-> screen exact sources
-> extract design/statistical/attribution receipts
-> assign each source a claim ceiling
-> synthesize only admitted claims
-> challenge the seven principles
-> write Results/Discussion
```

This is now the operational interpretation of “each paper should prove only as much as it is able to.”
