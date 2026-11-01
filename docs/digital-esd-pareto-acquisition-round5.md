# Digital-ESD Pareto acquisition round 5

Status: source-acquisition / proof-search note. This document does not create manuscript inclusion, database-search completion, causal authority, or Agda/kernel certification.

## Governing rule

Each study/source is reduced to the literal predicates its own evidence pays. Attribution, PNF scope, design, sample/analysis carrier, uncertainty and first unpaid implication stay attached to the same source object.

```text
source identity
!= population transport
!= causal authority
!= intersectional completeness
!= lifecycle completeness
```

## Intersectional disability extension

Primary source:

- Rachel N. Bonnette; Samuel Abramovich; Adrienne Decker; Gregory A. Fabiano,
  *The Need for an “Intersectionality Variable”: Examining Differences in Challenging Experiences of Multiply Marginalised Neurodivergent Students in Higher Education STEM Programs*,
  DOI `10.1080/1034912X.2025.2571758`.

Source-paid carrier:

- 66 STEM-program survey respondents before source-defined exclusions;
- 54 analysed respondents who answered required prompts and self-identified as neurodivergent;
- singly versus multiply marginalised comparison;
- Wilcoxon rank-sum comparison of challenge variety;
- chi-squared comparisons across ten challenge types;
- open-ended elaboration retained as a distinct qualitative surface.

The strongest paid implication is a bounded within-study contrast. Population transport remains unpaid.

The key intersectional result is methodological as well as substantive:

```text
neurodivergent/disabled label
!= homogeneous challenge surface
```

and:

```text
one constructed intersectionality variable
!= complete representation of race × gender × disability × power
```

The source itself reports that small racial-category cells prevent analysis of specific multiply marginalised subgroups. Nonrespondent characteristics also remain unknown. Absence therefore remains an acquisition residual rather than a license to infer motive, disability, trauma or access failure.

A second primary comparator was acquired conservatively:

- Danielle A. Waterfield; Jaira Ferreira de Vasconcellos; Meriah Crawford; Mariane Doyle; Jessica Taggart; Breana Bayraktar; Dayna Henry,
  *Exploring Generative AI Use and Perceptions Among Students With and Without Disabilities in Higher Education*,
  DOI `10.1177/01626434261454347`.

The current publisher-accessible surface pays 383 total responses and 48 respondents self-identifying as disabled plus the existence of a disability-status comparison. Detailed subgroup effect sizes, response denominators and analysis-set handling remain unpaid in this acquisition pass.

This complements but does not merge with Zhao/Cox/Chen. Same topic and disability label do not create the same study population or evidence object.

## AI inference scale / rebound calibration

Primary source:

- Felipe Oviedo; Fiodar Kazhamiaka; Esha Choukse; Allen Kim; Amy Luers; Melanie Nakagawa; Ricardo Bianchini; Juan M. Lavista Ferres,
  *Energy use of AI inference, efficiency pathways, and test-time scaling*,
  Joule (2026), DOI `10.1016/j.joule.2026.102430`.

Source-paid model/scenario receipts include:

- standard-query median `0.31 Wh/query`, IQR `0.16-0.60`;
- long/test-time-scaling median `3.91 Wh/query`, IQR `2.15-7.05`;
- approximately 13x energy increase for the modeled long-query regime;
- `1 billion queries/day -> 0.7 GWh/day` in the baseline scenario;
- `10%` long reasoning queries -> `1.7 GWh/day`;
- illustrative efficiency scenario -> `0.8 GWh/day`;
- line-of-sight modeled per-query efficiency reductions of roughly `8-20x` across model/serving/hardware interventions.

This pays a bounded scale-sensitivity predicate:

```text
lower per-query energy
!= guaranteed lower aggregate inference energy
```

because workload length, serving geometry, query volume and usage dynamics remain live coordinates.

It does **not** pay an empirically observed rebound elasticity. The billion-query/day cases are scenarios/model outputs, not a longitudinal before/after demand panel following an efficiency shock.

```text
modeled scale sensitivity
!= observed rebound effect
```

It is also a technical AI-inference source, not an education-specific deployment footprint. The named educational workload/provider/model/hardware/grid/lifecycle allocation remains a separate same-object obligation.

## TSMC / manufacturing / LES cross-pollination boundary

The current environmental braid should now be read as three non-interchangeable layers:

```text
semiconductor manufacturing / supply-chain substrate
    (TSMC primary sustainability/manufacturing evidence)
                ↓
AI inference workload / serving allocation
    (Oviedo; Fernandez et al.; EcoLogits/Woo-style allocation)
                ↓
education-specific workload/scenario
    (Lupetti workshop; Pinzone education LCA)
                ↓
named deployed educational-AI lifecycle footprint
    (still unpaid)
```

The LES/material-allocation lesson remains consumer-relative: total manufacturing or infrastructure burden cannot be assigned to a learner/request without an explicit functional unit, allocation rule, utilisation/lifetime denominator and system boundary.

TSMC's current sustainability reporting is therefore valuable as manufacturing/value-chain context, but corporate aggregate energy/water/emissions do not become a per-query or per-student footprint without a valid allocation bridge.

## Pareto result

This round pays two concrete residuals without changing the flat 20-coordinate review extraction surface:

1. an intersectional-disability source fixture showing that disability/neurodivergence does not determine a homogeneous experience surface;
2. a technical AI scale fixture showing that per-query efficiency does not determine aggregate inference demand.

No new generic calculus was added.

## Next frontier

Highest-value next payments are now:

1. obtain full same-object Waterfield methods/results or another primary comparator that reports disability-status subgroup statistics with confidence/uncertainty and response denominators;
2. acquire a source where rebound is actually estimated from observed demand response to an efficiency/cost change, while keeping non-AI rebound donors separate from AI-domain authority;
3. acquire a named educational AI deployment exposing provider/model/workload/hardware/region or datacentre route so TSMC/manufacturing and inference allocation can be connected without pretending aggregate corporate disclosures are deployment footprints;
4. recover exact intersectional subgroup cells where ethically/statistically possible, while retaining suppressed/small cells as explicit non-observation rather than imputing them;
5. continue database execution when authenticated Scopus/WoS access is available; execution-blocked receipts remain access residuals, not zero-result searches.

## Verification status

RED regression files were created before production owners and the production paths were observed absent/404. The production owners were then written and exported through `DASHI.EverythingDigitalESDReciprocalBraid`. Source files are connector-read-back only; no Agda/Nix kernel GREEN or CI receipt is claimed.
