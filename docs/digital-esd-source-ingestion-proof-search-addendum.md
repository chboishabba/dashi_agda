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
9. Collado et al. — quasi-experimental one-year longitudinal association with unresolved same-object numeric extraction debt.

These are method-validation/pre-screen profiles only. They do not pay final eligibility or this manuscript's database search.

## Attribution correction discovered by ingestion

The existing feature-branch source object for DOI `10.1007/s11367-026-02656-7` retained incorrect co-author given names. Publisher metadata identifies:

- Marta Pinzone;
- Francesca Sarti; and
- Elisa Amodeo.

`DigitalESDSourceAttributionCorrectionExact` now owns the corrected source object. The legacy source remains reachable only as correction provenance and must not seed new extraction.

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

This pass produced one real schema extension (model-based environmental-impact claim kind), one deferred schema residual (multiple analysis Ns), one metadata correction, and one source-specific numeric acquisition debt. No generic proof-search calculus was added.

## Immediate acquisition frontier

Highest-value next acquisitions are now:

1. recover Collado full same-object methods/results to pay exact sample/retention/model/effect/CI coordinates;
2. ingest another quantitative digital-ESD/ESD intervention that reports an actual effect magnitude plus uncertainty interval, to test the positive statistical path;
3. ingest an institutional/government evaluation source where the analytic carrier is jurisdiction/document/system rather than participants;
4. continue lifecycle/circularity acquisition only where it supplies deployment-relevant measurement or model assumptions not already represented;
5. screen each acquired source before any promotion into final manuscript inclusion.

## Verification status

These owners are source-written and connector-read-back only. Python V1 structural tests exist and have a local-equivalent executed receipt; no Agda/Nix kernel certification or CI/Actions receipt is claimed for this acquisition tranche.
