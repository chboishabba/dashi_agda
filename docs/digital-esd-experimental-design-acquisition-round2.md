# Digital-ESD experimental-design acquisition — round 2

Status: source-acquisition / method-validation note. No source in this document is promoted into the final included corpus merely by appearing here.

## Why this round exists

The review's claim ceiling should not collapse statistical precision, comparison design, randomization, construct validity, analysis-set integrity, or transport into one quality score.

This round deliberately acquired sources that pay different subsets of those obligations.

## Braßler 2024 — effect magnitude without effect CI

Primary source: Mirjam Braßler, *Students' Digital Competence Development in the Production of Open Educational Resources in Education for Sustainable Development*, Sustainability 16(4), 1674, DOI `10.3390/su16041674`.

Exact extraction retains:

- stated study N=409;
- OER-production group n=83;
- same-cohort control n=326;
- Time main effect F(1,191)=59.7, p<0.001, partial eta-squared=.238;
- Time×Group F(1,191)=22.4, p<0.001, partial eta-squared=.105;
- OER group 2.49 -> 3.42, control 2.22 -> 2.54;
- source-reported quasi-experimental/self-selection limitations.

The source does not explain in the visible primary text why the stated N=409 corresponds to an inferential denominator df=191. The analysis n therefore remains unresolved rather than being reconstructed from the F statistic.

```text
effect magnitude reported
!= analysis n resolved
!= confidence interval reported
!= causal population effect
```

The review ceiling is `derivesBoundedContrast`.

## Deng, Sun, Ho & Lee 2026 — effect magnitude + 95% CI without control group

Primary source: Wen-Jing Deng; Jiayue Sun; Wingkei Ho; John Chi-Kin Lee, *Short-Term Knowledge Gains and Regional Heterogeneity in a STEM-Based Indoor Air Quality Education Intervention for Sustainability Across Asian Regions*, Sustainability 18(14), 7165, DOI `10.3390/su18147165`.

Exact extraction retains:

- n=1408 Grades 5-10 students across five Asian regions;
- paired mean knowledge gain +9.25 points;
- 95% CI [7.58,10.92];
- p=2.30e-26;
- Cohen's dz=.289;
- ANOVA regional heterogeneity eta-squared=.070;
- sensitivity analysis around post-test-zero records.

The design has no non-intervention comparison group and no delayed follow-up.

```text
precise paired-gain interval
!= counterfactual treatment-effect interval
```

The review ceiling is `derivesBoundedContrast`, not `attributesCausalEffect`.

## Green, Molloy & Duggan 2022 — randomized design with analysis-set residual

Primary source: Caroline Green; Owen Molloy; Jim Duggan, *An Empirical Study of the Impact of Systems Thinking and Simulation on Sustainability Education*, Sustainability 14(1), 394, DOI `10.3390/su14010394`.

The source pays a strong randomized-design receipt:

- randomized 2x2 factorial assignment;
- 227 people signed up;
- 80 did not follow up;
- 8 started then withdrew;
- 33 datasets were incomplete or invalid;
- 106 complete datasets remained after validation;
- complete randomized groups: control 28, systems thinking 26, simulation 24, combined 28;
- quizzes/surveys pilot tested; data reported as openly available;
- simulation-vs-control Quiz-1 contrast reports simulation n=24, M=78.4, SD=14.1 versus analyzed control n=27, M=71.9, SD=9.3, p=0.018 and Cohen's d=.6.

However, the source reports post-randomization analysis exclusions:

- the Quiz-1 control outlier was removed before inferential testing;
- the extreme Quiz-2 control outlier was removed;
- two Quiz-2 datasets were removed after page analytics indicated non-engagement with the fisheries section.

Therefore the review does not promote the mere RCT label directly into `attributesCausalEffect` for the reported analyzed contrast.

```text
random assignment
!= every post-randomization analysis set preserves the causal estimand automatically
```

The current ceiling is `associatesTreatmentAndOutcome`. Causal promotion is an explicit residual requiring a consumer-level decision about the estimand, analysis set and admissibility of the exclusions. Even if that promotion were later paid, it would remain bounded to the measured quiz outcome and sampled population.

## Proof-search result

These three sources independently demonstrate:

```text
effect size != confidence interval
confidence interval != causal identification
randomization != analysis-set admissibility
causal identification != construct completeness
construct validity != population transport
population transport != system transformation
```

No additional top-level extraction coordinate is required by this round.

The existing claim profile can represent the relevant distinctions through:

- exact source identity;
- study/enrolled n;
- analysis n;
- allocation;
- comparator;
- measurement validity;
- attrition/missingness;
- confounding;
- effect-size surface;
- uncertainty surface;
- time horizon;
- external-validity domain; and
- claim ceiling.

The remaining residuals are source-specific rather than evidence for another generic ontology.

## Attribution / authority discipline

- new Braßler extraction uses publisher spelling `Mirjam Braßler`; the older ASCII `Brassler` object remains provenance ancestry, not a separate person;
- Pinzone/Sarti/Amodeo author correction remains in force for the education LCA;
- effect magnitudes, CIs and group Ns belong to their exact source/analysis surfaces;
- a p-value cannot backfill a missing confidence interval;
- degrees of freedom cannot silently backfill analysis n;
- a source's causal rhetoric cannot promote beyond the review's extracted design receipts;
- deterministic extraction or content hashing remains procedural evidence only, not empirical authority.

## Next proof-search / acquisition frontier

1. recover Collado same-object full methods/results to pay n, retention, model, effect and uncertainty coordinates;
2. inspect Braßler supplementary/data material for the N=409 versus F(1,191) analysis-set explanation;
3. seek a clean controlled/randomized digital-ESD source with an explicitly reported effect interval and predeclared/transparent analysis population, so `attributesCausalEffect` can be tested positively rather than assumed;
4. ingest an institutional/government evaluation where the analytic carrier is a jurisdiction/system/document corpus rather than participants;
5. promote none of these pre-screen acquisitions into final Results before the manuscript's own database search and eligibility screening are paid.

## Certification boundary

This round is source-written and connector-read-back. It has no Agda/Nix kernel receipt and no CI/Actions claim. The existing Python V1 structural checker is a procedural/static tool only and cannot promote empirical or proof authority.
