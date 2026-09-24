# Digital-ESD source-ingestion / proof-search addendum

Status: working methodology + acquisition note. This document does not create scholarly evidence or final manuscript inclusion.

## Governing attribution rule

The current review uses exact source objects and source-local extraction. A DOI, author overlap, review citation, same topic, nearby figure host, or reproducible script cannot backfill a missing source-specific design/statistical coordinate.

```text
same topic / author / construct / DOI family
!= same evidence object

provenance
!= reproducibility
!= extraction correctness
!= empirical support
!= claim truth
```

The synthesis target remains bounded attributed claims rather than citation counts.

## Current heterogeneous pilot surface

The claim-ceiling pilot now exercises the following evidence modes:

1. Ardila et al. — qualitative case / implementation-context evidence;
2. Gouseti & Shaw — qualitative lived-experience evidence;
3. Martínez García et al. — systematic-review synthesis;
4. Böhme — conceptual-framework evidence;
5. Descamps et al. — bounded quantitative educational contrasts;
6. Pinzone, Sarti & Amodeo — model-based education LCA with sensitivity/Monte Carlo uncertainty;
7. Holst et al. — longitudinal input-level document monitoring;
8. Fishlock et al. — mixed-method implementation pilot with multiple method-specific analysis Ns;
9. Collado et al. — quasi-experimental one-year longitudinal association with unresolved same-object numeric extraction debt;
10. Braßler — quasi-experimental two-group pre/post digital-competence study with source-reported partial-eta-squared effect sizes and unresolved analysis-N discrepancy;
11. Deng, Sun, Ho & Lee — multi-region short-term sustainability-education program evaluation with n=1408, Cohen's dz and an explicit 95% CI for the paired mean gain.

These are method-validation/pre-screen profiles only. They do not pay final eligibility or this manuscript's database search.

## Attribution corrections / normalisations discovered by ingestion

The existing feature-branch source object for DOI `10.1007/s11367-026-02656-7` retained incorrect co-author given names. Publisher metadata identifies:

- Marta Pinzone;
- Francesca Sarti; and
- Elisa Amodeo.

`DigitalESDSourceAttributionCorrectionExact` now owns the corrected source object. The legacy source remains reachable only as correction provenance and must not seed new extraction.

The existing OER/HESD object for DOI `10.3390/su16041674` used the ASCII transliteration `Mirjam Brassler`. Publisher metadata displays `Mirjam Braßler`. This is treated as an orthographic normalization of the same person/source identity rather than as a wrong-person attribution; new exact extraction uses the publisher spelling while the earlier source object remains provenance ancestry.

The important rule is:

```text
correct DOI identity
!= every attached metadata field is automatically correct
```

## Descamps quantitative contrast

Same-object publisher material pays:

- 164 students participating in the learning session;
- 107 complete pre/post cases used for analysis;
- reported random division at scenario assignment;
- analytic scenario groups 57 and 50;
- maturity relative gains 27.63% and 25.85%;
- Mann-Whitney maturity comparison W=1531, p=0.051;
- p=0.038 for amotivation and p=0.015 / p<0.001 for two collective-efficacy contrasts.

It does not pay a standardized between-group effect size, educational-effect confidence interval, long-term persistence, universal transport, or system transformation.

The profile ceiling is therefore a bounded contrast rather than a universal causal-effect claim.

## Braßler effect-size pilot

Same-object primary material pays:

- two-group pretest-posttest quasi-experimental design;
- reported study sample N=409, with 83 OER-production students and 326 same-cohort controls;
- five-item Creative Internet Skills Scale with alpha=.84 at baseline and .88 post-course;
- OER-group means 2.49 -> 3.42 and control means 2.22 -> 2.54;
- Time main effect F(1,191)=59.7, p<0.001, partial eta-squared=.238;
- Time×Group interaction F(1,191)=22.4, p<0.001, partial eta-squared=.105;
- explicit source limitations covering quasi-experimental group equivalence, self-selection and subjective self-report measurement.

The source does not explain in the visible primary Methods/Results why the inferential model reports denominator df=191 while the stated study sample is N=409. Therefore:

```text
study N = 409
analysis N = unresolved
```

No analysis N is reverse-engineered from degrees of freedom. The source pays an effect magnitude but not an educational-effect confidence interval. Its ceiling is `derivesBoundedContrast`, not `attributesCausalEffect`.

## Pinzone lifecycle-model evidence

Same-object publisher material pays:

- functional unit: 25 hours of education per student (10 lecture + 15 independent-study hours);
- scenario LCA comparing face-to-face, hybrid and online modes;
- global-warming examples including 17.2 kg CO2eq per functional unit for face-to-face and 5.88 kg for fully online asynchronous delivery;
- explicit sensitivity analyses;
- Monte Carlo uncertainty with 95% intervals;
- low variability for the face-to-face key indicators (reported CV around 2%);
- substantially wider hybrid uncertainty because of attendance/ICT parameter variation.

It does not pay a participant sampling effect, pedagogical effectiveness, or the measured footprint of another deployment.

This source forced one legitimate extension of `AdmissibleClaimKind`:

```text
modelBasedEnvironmentalImpactClaim
```

and the firewall:

```text
model 95% interval
!= same-object deployment measurement
```

## Deng–Sun–Ho–Lee positive uncertainty path

A new primary source was acquired specifically to exercise the positive `effect + uncertainty` path:

- Wen-Jing Deng; Jiayue Sun; Wingkei Ho; John Chi-Kin Lee;
- *Short-Term Knowledge Gains and Regional Heterogeneity in a STEM-Based Indoor Air Quality Education Intervention for Sustainability Across Asian Regions*;
- Sustainability 18(14), 7165 (2026);
- DOI `10.3390/su18147165`.

Same-object source material pays:

- n=1408 Grades 5-10 students across Sri Lanka, Nepal, Malaysia, Indonesia and Guangxi (China);
- overall knowledge gain +9.25 points;
- 95% CI [7.58, 10.92];
- p=2.30e-26;
- Cohen's dz=.289;
- significant regional heterogeneity (ANOVA eta-squared=.070);
- sensitivity analysis for post-test-zero records.

But the design is a one-group pre/post program evaluation with no comparison group. Therefore the interval belongs to the observed paired mean-gain estimand, not to a counterfactual treatment effect.

```text
precise paired-gain CI
!= causal treatment-effect CI
```

The source ceiling is `derivesBoundedContrast`. This acquisition demonstrates that the existing effect/uncertainty coordinates can represent a genuine CI without adding another schema dimension, provided the estimand and design interpretation remain attached.

## Holst input-monitoring ceiling

Holst et al. analyze a latest cumulative corpus of 11,061 documents across German formal education and explicitly define the outcome as SDG 4.7.1 input-level implementation. Lexical searches were manually checked; uncertain codings were peer-debriefed by three researchers; external expert evaluation supplements the document analysis.

The strong longitudinal/document-monitoring receipt therefore stops at documented input integration, depth and speed of change.

```text
input-level integration
!= learner outcome
!= behavioural change
!= digital-ESD intervention effect
!= system transformation
```

No new claim-kind constructor was required: `restatesMeasuredResult` is sufficient.

## Fishlock multi-analysis-N residual

The right-to-repair pilot reports:

- 40 registered students;
- survey n=14;
- focus-group n=5.

There is no honest single study-wide analysis n. The current profile therefore leaves the primary `analysisN` unresolved and separately types the survey and focus-group analysis counts.

```text
one paper
!= one analysis population
```

This is a live schema residual, but a global multi-analysis-N redesign remains deferred until another admitted study demonstrates that the structure recurs and is consumer-relevant.

## Collado same-object acquisition debt

Same-object publisher/repository material currently pays:

- quasi-experimental ESD intervention design;
- intervention vs non-participation control comparison;
- self-reported pro-environmental knowledge, personal environmental norm and behaviour;
- immediate assessment and one-year follow-up;
- reported persistence of intervention/control differences at one year.

It does not, in the same-object material currently acquired here, pay exact group/sample counts, retention counts, model specification, effect magnitudes or interval endpoints.

Those remain explicit acquisition debt. A figure surfaced by a secondary platform showing 95% CIs is not promoted into the profile as same-object numeric payment.

## Proof-search result

The current source-driven loop is:

```text
exact source
-> extract only paid coordinates
-> instantiate claim ceiling
-> detect mismatch / missing consumer coordinate
-> ask whether existing schema can represent it honestly
   -> yes: retain source-specific residual
   -> no: add the least new coordinate/type required by the concrete source
-> do not generalize the repair beyond its demonstrated consumer need
```

This acquisition sequence produced:

- one real schema extension: `modelBasedEnvironmentalImpactClaim`;
- one deferred schema residual: multiple method-specific analysis Ns;
- one metadata correction plus one publisher-orthography normalization;
- two source-specific numeric acquisition debts: Collado's unresolved n/effect/CI details and Braßler's unresolved analysis denominator;
- one positive effect-size path without a CI (Braßler);
- one positive effect-size + 95% CI path whose causal ceiling remains blocked by the absence of a comparison group (Deng et al.).

No generic proof-search calculus was added.

## Immediate acquisition frontier

Highest-value next acquisitions are now:

1. recover Collado full same-object methods/results to pay exact sample/retention/model/effect/CI coordinates;
2. recover/explain the Braßler N=409 versus F(1,191) inferential-denominator discrepancy from same-object supplementary/data material if available;
3. ingest a controlled/randomized digital-ESD/ESD intervention that reports effect magnitude plus CI, so the causal-identification path can be tested without confusing precision with randomization/control;
4. ingest an institutional/government evaluation source where the analytic carrier is jurisdiction/document/system rather than participants;
5. continue lifecycle/circularity acquisition only where it supplies deployment-relevant measurement or model assumptions not already represented;
6. screen each acquired source before any promotion into final manuscript inclusion.

## Verification status

These owners are source-written and connector-read-back only. Python V1 structural tests exist and have a local-equivalent executed receipt; no Agda/Nix kernel certification or CI/Actions receipt is claimed for this acquisition tranche.
