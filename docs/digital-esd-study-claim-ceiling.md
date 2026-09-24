# Digital-ESD study-claim ceiling

**Status:** paper-method working artifact. This document describes the extraction and interpretation rule implemented by `DigitalESDStudyClaimCeilingExact` and `DigitalESDStudyClaimMethodBridgeExact`. It does not create evidence and it does not upgrade any source.

## Core rule

Each included paper may support only the strongest implication paid by that paper's own source identity, design, realised sample, measurement, uncertainty and transport receipts.

```text
paper finding
  -> design-relative admissible implication
  != automatically causal effect
  != automatically mechanism
  != automatically population transport
  != automatically practice recommendation
  != automatically system transformation
```

A narrower claim is not a failed paper. Qualified evidence remains useful when its scope and inferential force are retained honestly.

## Provenance first

Every study-claim profile is indexed by an exact `AttributedSource` object. The design/statistical profile therefore remains attached to the paper whose sample, effect estimate, interview material, confidence interval or other result is being interpreted.

A citation label, DOI, nearby review or thematically similar study may not donate an unreported sample size, uncertainty estimate, comparator, design feature or limitation to a different source.

## Effective extraction schema

The existing manuscript methodology retains 19 top-level extraction coordinates. The study-claim method bridge appends one structured study-claim-ceiling coordinate, yielding **20 effective top-level extraction coordinates**.

The appended bundle contains 16 subcoordinates:

1. source population;
2. enrolled/reported sample size (`n`) where applicable;
3. analysis sample size where applicable;
4. allocation/assignment mechanism;
5. comparator or comparison structure;
6. measurement validity;
7. attrition/missingness handling;
8. confounding control;
9. implementation fidelity;
10. multiplicity handling;
11. effect-size surface;
12. uncertainty / confidence-interval surface;
13. time horizon;
14. external-validity / transport domain;
15. participant epistemic role; and
16. strongest supported implication.

A coordinate may be `not reported`. Missing values remain missing unless a same-object derivation receipt pays them.

## Claim ladder

The repository's experimental implication cone distinguishes at least:

```text
measured result
-> bounded contrast
-> residual envelope
-> association
-> causal effect
-> mechanism
-> population transport
-> practice recommendation
```

These are not interchangeable. A paper may close one edge and leave all stronger edges qualified or blocked.

## Quantitative studies

Where applicable, extraction should retain:

- reported/enrolled `n`;
- analysis `n`;
- allocation/randomisation or assignment mechanism;
- comparator;
- baseline and endpoint measurement design;
- attrition and missing-data handling;
- confounding adjustment;
- multiplicity handling;
- effect estimate and scale;
- uncertainty semantics, including confidence interval or standard-error surface where reported;
- coverage/calibration claims only when the source actually supplies them;
- study duration/follow-up;
- source population and transport domain.

The following promotions are blocked:

```text
large n != representative population
p-value/significance != causal identification
narrow confidence interval != causal identification
confidence interval != population transport
power != effect truth
statistical significance != practical significance
positive association != practice recommendation
positive study result != system transformation
```

## Qualitative and participatory studies

The same claim-ceiling rule is deliberately not a quantitative evidence hierarchy. Qualitative interviews, focus groups and participatory designs may support situated experience, interpretation, acceptability, mechanisms or implementation questions for which a quantitative intervention study may be comparatively weak.

But:

```text
rich qualitative finding != population prevalence estimate
participant consultation != constitutive epistemic authority
one local context != universal transport
```

Sample composition, recruitment, participant role, analytic procedure, context and limitations remain part of the evidentiary ceiling even when confidence intervals are not the relevant uncertainty representation.

## Reviews, standards and institutional sources

For systematic/scoping reviews, standards, evaluations, charters and policy/framework documents, the claim ceiling is source-role relative. A review may synthesize a corpus without becoming a same-object intervention. A standard may define a measurement coordinate without supplying deployment data. An institutional evaluation may support programme-level implementation claims without proving local causal effects.

## Relationship to transformation levels

A study-level finding must not skip the manuscript's transformation ladder:

```text
technology presence
!= implementation activity
!= input integration
!= task performance
!= learning/outcomes
!= institutional durability
!= system transformation
```

The claim ceiling therefore sits upstream of synthesis. A source first receives its design-relative admissible claim. Only then may that claim enter a transformation-level synthesis cell.

## Relationship to externality incidence

The study-claim ceiling and externality-incidence audit are independent.

A statistically precise estimate can still omit who contributed, benefited, bore burden, controlled the decision or lacked exit. Conversely, a rich distributional account can remain weak on causal identification or population transport.

```text
inferential precision != distributional completeness
```

Both must be retained when the consumer requires both.

## Practical extraction question

For every included source, the review should be able to answer:

> What exactly did this paper observe or estimate; from whom; with what design, sample, comparator and uncertainty; over what time; and what is the strongest implication that those receipts support without overreach?

That question is the paper-level implementation of the repository rule:

```text
source evidence pays only the claim it can actually support.
```
