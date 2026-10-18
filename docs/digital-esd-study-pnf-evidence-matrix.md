# Digital-ESD study PNF / evidence matrix

Status: pre-screen / method-validation matrix. Nothing in this document creates final manuscript inclusion.

## Governing rule

For each source, distinguish:

```text
paper rhetoric
!= extracted source-local result
!= PNF assertion
!= design-supported predicate
!= stronger downstream implication
```

The admissible synthesis object is therefore not "paper X supports principle Y" in the abstract. It is a bounded predicate with exact source identity, analytic carrier, design, statistical/uncertainty surface, time/context scope, and an explicit promotion frontier.

## Quantitative / longitudinal result audits

| Study | Analytic carrier | PNF force | Source-local predicate paid | Statistical / uncertainty surface | Strongest paid implication | First unpaid / next discriminator |
|---|---|---|---|---|---|---|
| Deng, Sun, Ho & Lee 2026 | 1,408 Grades 5-10 students across five Asian regions | comparative | immediate within-student IAQ knowledge scores increased after the programme in the analysed sample | mean gain +9.25; 95% CI [7.58,10.92]; Cohen's dz=.289; regional eta-squared=.070 | bounded pre/post contrast | causal effect; requires a counterfactual comparator, not a narrower CI on the same paired gain |
| Braßler 2024 | reported study N=409; inferential analysis N unresolved | comparative | digital-competence scores increased more over the semester in the OER-production group than the same-cohort comparison group under the reported model | Time x Group F(1,191)=22.4, p<.001, partial eta-squared=.105; no numerical effect CI | bounded group/time contrast | causal effect; recover analysis-set/missingness denominator and separately address non-random allocation |
| Descamps et al. 2025 | 164 session participants; 107 complete pre/post cases; active groups 57/50 | comparative | two active digital-sobriety scenarios showed similar maturity gains, with some outcome-specific motivation/collective-efficacy contrasts | maturity gains 27.63%/25.85%; W=1531, p=.051; other outcome p-values; no standardized between-group effect or effect CI | bounded active-scenario contrast | causal effect of digital-sobriety education; requires estimand-specific control and missingness/attrition account |
| Green, Molloy & Duggan 2022 | 106 validated randomized datasets; analysis-local simulation n=24 vs control n=27 after exclusion | associational at current review ceiling | simulation exposure is associated with higher immediate Quiz-1 score in the reported analysed contrast | M=78.4 vs 71.9; p=.018; Cohen's d=.6; no numerical effect CI | treatment-outcome association | causal effect; requires explicit admissibility/estimand decision for post-randomization analysis-set changes |
| Collado, Moreno & Martín-Albo 2022 | T0/T1 n=257 from 120+137; one-year complete n=98 | comparative | intervention/control differences in measured knowledge, personal norm and self-reported behaviour remain at one year under the reported mixed-effects model | T2 b=.74/.34/.69; 95% CIs [0.35,1.14], [0.02,0.67], [0.40,0.98] | bounded longitudinal intervention/control contrast | causal effect; voluntary allocation and 61.87% dropout require allocation/attrition repair |

## Heterogeneous evidence audits

| Study | Analytic carrier | PNF force | Source-local predicate paid | Statistical / uncertainty semantics | Next consumer question |
|---|---|---|---|---|---|
| Ardila et al. 2025 | two five-member HE student design teams | descriptive | documented design-thinking practices in the two cases show context-specific ways sustainability competencies appeared to emerge or be hindered | no population effect/CI applies; qualitative process evidence | which process/context coordinate discriminates support from hindrance across cases? |
| Gouseti & Shaw 2026 | 71 leaders/teachers/students/parents in two schools | descriptive | participants describe platformisation as having practical benefits and situated burdens including surveillance, exclusion and wellbeing concerns | no participant-effect CI applies; uncertainty is interpretive/contextual | which governance/power/context coordinates explain different burden patterns? |
| Martínez García et al. 2026 | 33 included studies; 502,701 underlying participants | descriptive review synthesis | benefits are synthesised as conditional on pedagogy, teacher mediation, infrastructure/policy and equitable access rather than as one pooled effect | no pooled effect/CI; kappa=.81 is reviewer agreement only | which primary-study predicates support or defeat each candidate principle under our own ceilings? |
| Böhme 2026 | conceptual literature/discourse | descriptive conceptual | sustainability/ESD and digitality are framed as a mutually coupled twin transformation | empirical n/effect/CI not applicable | what observations operationally discriminate coupled transformation from rhetorical co-location? |
| Pinzone, Sarti & Amodeo 2026 | modelled educational scenarios under a 25-hour-per-student functional unit | comparative model claim | under declared LCA assumptions, modelled online scenarios have lower global-warming outputs than face-to-face | example 17.2 vs 5.88 kg CO2eq; Monte Carlo 95% model uncertainty; not a participant CI | which deployment-specific inventory/boundary values alter the ordering for the target institution? |
| Holst et al. 2024 | 11,061 formal-education documents | descriptive longitudinal monitoring | ESD input integration increased over time but commonly remained isolated/partial across sub-indicators | no learner-effect CI applies; uncertainty is corpus/coding/indicator validity | do stronger documented inputs correspond to matched process/output/learner outcomes? |
| Fishlock et al. 2023 | 40 registered students; survey n=14; focus-group n=5 | descriptive implementation | right-to-repair principles were implemented in a PBL module and small responding subsets reported strong engagement/future intentions | no inferential CI/effect; analysis populations are method-specific | does the pedagogy change observed repair/sustainable-design behaviour under comparator and follow-up? |
| UNECE fifth ESD evaluation 2026 | 31 national implementation reports | descriptive institutional synthesis | regional reports show continuing implementation progress alongside digital-access, educator-competence, governance, monitoring and outcome-assessment gaps | no intervention-effect CI; uncertainty is self-report/report coverage/synthesis/heterogeneity | which institutional changes are independently observable and linked to matched learner/process outcomes? |

## CI / uncertainty typing rule

The phrase `95%` has no universal evidentiary meaning. Preserve what the interval is an interval **of**.

```text
Deng 95% CI
= paired mean-gain uncertainty in a one-group pre/post sample
!= causal treatment-effect CI

Collado 95% CI
= mixed-effects time-by-condition coefficient uncertainty in a non-random longitudinal sample
!= randomised causal-effect interval

Pinzone 95% interval
= Monte Carlo model/parameter uncertainty
!= participant-sampling CI
!= measured footprint of another deployment

Green "95% confidence level"
!= numerical confidence interval endpoints
```

Likewise:

```text
no CI
!= weak evidence
```

when the admissible claim is qualitative lived experience, implementation context, conceptual structure, document monitoring or institutional synthesis.

## Proof-search rule

For each study, the next acquisition/probe targets the **first unpaid consumer-relevant predicate**, not another citation that repeats the already-paid statement.

Examples:

```text
precise pre/post gain + no control
-> seek counterfactual comparator
not more precision

quasi-experimental contrast + unresolved selection
-> seek allocation/confounding receipt
not another effect-size citation

randomized design + post-randomization analysis change
-> resolve estimand/analysis-set admissibility
not "RCT" label repetition

input-level document integration
-> seek matched process/output/outcome evidence
not more input documents alone

model LCA result
-> seek target-deployment inventory/boundary evidence
not treat model CI as field measurement
```

The generic discriminator/search semantics remain owned by the existing Aristotle experimental proof-search machinery. These digital-ESD fixtures supply consumer-specific collisions and residuals only.

## Attribution boundary

All numerics and predicates remain indexed by the exact attributed source object and source-local locator. Same author, DOI family, review citation, topic, figure host, or semantic similarity cannot backfill a missing `n`, effect size, CI, comparator, analysis set, model boundary or source passage.

```text
same topic
!= same evidence object

citation
!= proof
!= authority

reported source conclusion
!= automatically admitted review predicate
```
