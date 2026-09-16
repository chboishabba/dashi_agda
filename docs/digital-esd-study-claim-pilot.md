# Digital-ESD study-claim pilot

**Status:** method-validation pilot. These profiles do not create final study inclusion and do not pay the manuscript's database-search receipts.

## Purpose

The study-claim ceiling was tested against three deliberately different source types already present in the pre-screen scholarly snowball:

1. Ardila Echeverry et al. (2025) — qualitative case study / design-learning context;
2. Gouseti & Shaw (2026) — qualitative multi-stakeholder school platformisation study;
3. Martínez García et al. (2026) — systematic review.

The purpose was not to score the papers. It was to test whether the extraction grammar could represent what each source actually supports without coercing it into a stronger or inappropriate design category.

## Pilot finding 1 — source-reported design must outrank ontology convenience

Ardila et al. describe a qualitative case study of two five-member HE student design teams. The generic `EvidenceDesignAdmissibilityExact.DesignKind` currently has no exact `qualitativeCaseStudy` constructor.

Therefore the application layer now retains:

```text
source-reported design
+ optional canonical mapping receipt
```

rather than:

```text
nearest available constructor
```

The same issue appears for Gouseti & Shaw, whose qualitative methodology combines focus groups and individual interviews. A combined qualitative design must not be silently relabelled as only `qualitativeFocusGroup` or only `qualitativeInterview`.

## Pilot finding 2 — participant epistemic role may be not applicable

A systematic review has no single direct-participant epistemic role at review level. Participant roles belong to the underlying primary studies.

The application layer therefore supports:

```text
reported role
| role unresolved
| role not applicable
```

instead of forcing every source into `respondent`, `informant`, `domainExpert`, etc.

## Pilot finding 3 — strongest admissible claim is not always a causal-cone edge

The generic implication cone is appropriate for measured-result / association / causal / mechanism / transport / recommendation promotion.

But qualitative and review evidence can legitimately support other consumer questions. The application layer therefore adds first-class claim kinds:

```text
causal/experimental implication
lived-experience claim
implementation-context claim
review-synthesis claim
conceptual-mechanism claim
```

This does not weaken the causal cone. It prevents non-causal evidence from being artificially squeezed into it.

## Ardila pilot ceiling

Source: `10.3390/su17104289`.

Retained source facts:

- analytic focus: two five-member HE student design teams (`n = 10`);
- ten-week postgraduate design-thinking module;
- 60 Year-5 children participated in co-design/test sessions and two children acted as advisors, but these populations are not silently added to the HE analytic `n`;
- design artefacts, participant-observer field notes and reflection materials are used to analyse the design process;
- no randomized comparator or population-effect estimate is promoted.

Pilot ceiling:

```text
implementation-context claim
```

The source can contribute context-bounded evidence about design-thinking practices associated with the emergence/hindrance of sustainability competencies. It does not by itself pay universal learning effects, population causal effects, institutional durability or system transformation.

## Gouseti & Shaw pilot ceiling

Source: `10.1080/17439884.2026.2653746`.

Retained source facts:

- two English secondary schools;
- `n = 71`: 4 senior leaders, 21 teachers, 36 students and 10 parents;
- semi-structured focus groups and interviews;
- reflexive thematic analysis;
- contextual comparison of differently platformised schools, not an experimental comparator;
- no effect-size or confidence-interval surface is manufactured.

Pilot ceiling:

```text
lived-experience claim
```

The source can contribute situated evidence about platform use, monitoring/surveillance, communication, exclusion, digital wellbeing and local domestication of platforms. It does not estimate population prevalence or a causal platform effect.

## Martínez García et al. pilot ceiling

Source: `10.3390/su18157979`.

Retained source facts:

- PRISMA systematic review;
- Scopus + Web of Science + reference checking;
- 33 included empirical studies;
- 502,701 participants reported across the included studies;
- MMAT quality appraisal;
- two independent reviewers with discrepancies resolved by consensus;
- Cohen's kappa `0.81` for reviewer agreement;
- no inferential meta-analysis because designs, stages, tools, durations, outcomes and statistical reporting were heterogeneous.

Pilot ceiling:

```text
review-synthesis claim
```

The review can contribute synthesis about definitional ambiguity, implementation conditions and recurrent limitations. Its kappa is reviewer-agreement evidence, not an educational-effect confidence interval. Its Scopus/WoS execution belongs to that review and does not pay this manuscript's database execution.

## Current Python V1 verification surface

`scripts/check_agda_static.py` is a standard-library Python structural checker with optional Tree-sitter support.

It checks:

- Agda module declaration versus repository path;
- local `DASHI.*` import path existence;
- nested block-comment/string/delimiter structural balance;
- required symbol presence;
- optional Tree-sitter `ERROR` / `MISSING` nodes when `tree-sitter-agda` is installed.

It explicitly does **not** claim typechecking.

The lexical-state scanner was smoke-tested locally against:

- a structurally valid module;
- an unmatched delimiter;
- nested Agda block comments;
- a string containing a delimiter.

All four behaved as expected.

The current sandbox cannot install `tree-sitter` / `tree-sitter-agda` because outbound package-network access is blocked. The optional hook remains useful on a local workstation where those packages are available.

## Roadmap consequence

This pilot strengthens the P0 gate:

```text
screen source
-> retain source-reported design without coercion
-> retain applicable / unresolved / non-applicable participant role
-> retain sample and uncertainty surfaces without invention
-> assign strongest admissible claim kind
-> only then allow source into thematic/principle synthesis
```

The pilot should remain small until actual database screening begins. Its job was to falsify weak assumptions in the extraction grammar, and it has already done so three times.
