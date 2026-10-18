# Digital-ESD study-results unpacking — round 3

Status: source-acquisition / experimental-design working note. This does not create final manuscript inclusion.

## Governing rule

Each paper contributes only the strongest claim paid by its exact attributed source, design, analysis set, estimand, effect/uncertainty surface and scope.

```text
reported effect != causal identification
reported 95% CI != transport
study N != every analysis N
source rhetoric != review claim ceiling
```

## Collado, Moreno & Martín-Albo — longitudinal ESD intervention

Primary source: DOI `10.1108/IJSHE-07-2021-0315`.

Same-object full text now pays the previously missing numeric cells.

### Analysis sets

- immediate T0/T1 complete cases: experimental `n=120`, control `n=137`, derived total `n=257`;
- source explicitly states participants self-selected and were not randomly assigned;
- approximately 18% of T0 respondents dropped out, missed a workshop and/or did not complete T1 and were excluded;
- one-year T2 completers: experimental `n=49`, control `n=49`;
- overall T2 dropout: `61.87% (n=159)`;
- final sample with all measures: `n=98`.

Thus:

```text
n(T0/T1 complete) = 257
n(T2 complete longitudinal) = 98
```

and these are retained as distinct analysis-set receipts.

### Model

The source fits three linear mixed-effects models, one each for environmental knowledge, personal environmental norms and self-reported pro-environmental behaviour. Condition, Time and Time×Condition are fixed effects; participant is a random intercept.

### Immediate Time×Experimental contrasts

- knowledge: `b=1.04`, 95% CI `[0.65, 1.43]`, `t=5.19`;
- personal environmental norm: `b=0.53`, 95% CI `[0.21, 0.86]`, `t=3.22`;
- self-reported behaviour: `b=0.83`, 95% CI `[0.54, 1.12]`, `t=5.63`.

### One-year Time×Experimental contrasts

- knowledge: `b=0.74`, 95% CI `[0.35, 1.14]`, `t=3.72`;
- personal environmental norm: `b=0.34`, 95% CI `[0.02, 0.67]`, `t=2.06`;
- self-reported behaviour: `b=0.69`, 95% CI `[0.40, 0.98]`, `t=4.70`.

### Claim ceiling

The paper pays bounded immediate and one-year intervention/control contrasts under a non-randomized quasi-experimental design. It does not pay randomized causal identification, attrition repair, objective-behaviour validation, population transport, universal long-term durability or system transformation.

```text
precise longitudinal CI
!= random assignment
!= low attrition
!= transport
!= system transformation
```

`DigitalESDColladoLongitudinalClaimExact` therefore retains `derivesBoundedContrast`.

## Braßler — unresolved inferential analysis set

Primary source: DOI `10.3390/su16041674`.

Same-object material pays:

- study sample `N=409`;
- OER-production group `n=83`;
- control group `n=326`;
- Time main effect `F(1,191)=59.7`, `p<.001`, partial eta-squared `.238`;
- Time×Group interaction `F(1,191)=22.4`, `p<.001`, partial eta-squared `.105`;
- quasi-experimental/non-random group-equivalence and self-selection limitations.

The currently verified primary text still does not pay the bridge from declared `N=409` to the repeated-measures denominator `df=191`.

Therefore:

```text
study N = 409
exact inferential analysis N = unpaid
```

The analysis N is not reconstructed from degrees of freedom and no CI is manufactured from the reported p-value/effect size without a separately declared derivation receipt.

## Proof-search frontier

The next highest-value study-result acquisition is now not another generic framework source. It is one of:

1. same-object supplementary/data material that explains Braßler's repeated-measures analysis set;
2. another longitudinal controlled study with exact retention and interval reporting;
3. a source reporting effect estimate + SE/CI where the estimand is explicitly causal under a design whose post-randomization analysis set is also paid.

The source-driven stop rule remains: repair the schema only when a recurring consumer collision requires it.
