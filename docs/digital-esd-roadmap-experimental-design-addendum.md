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


## 2026-10-22 EfS / Digital Pedagogy source-grounded survival audit (PR #1237)

**Authoritative scope:** This is an update to the review-work roadmap, **not** admission or empirical validation. The actual ESD/Digital-ESD working manuscript currently targets the *Sustainability* special-issue conceptual/integrative review. A separate *Nature* journal submission roadmap is not established by these Digital-ESD files; references to 'nature' in this lane commonly describe nature-connected learning, not a verified *Nature* submission. Do not rename or silently change the target journal.

**Canonical added owner:** `DASHI/Education/DigitalESDPrincipleSurvivalAuditExact.agda` + regression, consuming existing seven-principle sources and independent EfS challenge. The earlier `DigitalESDEfSCanonicalReuseAdapterExact` consumes `DigitalESDEvidenceBraidTensionExact`, the Alice corpus and the DB-native extraction owner without duplicating their ontologies. Both are source-written and need exact-head Agda checks.

### What survives the *conceptual* cross-corpus challenge (NOT the full search)

| Candidate digital principle | Current conceptual status | Main EfS discriminator |
| --- | --- | --- |
| Situated relational engagement | provisional revise/retain | engagement vs actual EfS teaching, ecological and community practice |
| Feedback as revisable signal | provisional revise/retain | feedback classification vs critical values deliberation |
| Constitutive learner agency | provisional split candidate | individual voice vs group decision rights / collective action |
| Adaptive support with local choice | provisional revise/retain | accessibility gains vs fragmentation of common inquiry |
| Plural situated observers | provisional revise/retain | distinct source authority, non-human ecological observations, Indigenous knowledge permissions |
| Contextual custodianship | provisional revise/retain | contextual representation vs measured systems thinking |
| Iterative evidence return/recharting | provisional revise/retain | revision of feedback vs futures literacy and durable change |

**None of the seven is yet supported by a completed screened-and-admitted independent EfS corpus at an intervention-effect claim ceiling.** This is a typed candidate-status report, not a quantitative support vote. Independent EfS coding additionally leaves ecological/more-than-human pedagogy unmatched by the seven *labels* (though the wider DASHI has ecological machinery). Keep it as an open possible augmentation, not an automatic eighth principle.

### Executable evidence pipeline already owned

- Real ERIC: 46,597 query occurrences -> 43,996 distinct metadata/abstract records -> 2,601 duplicate occurrences. These are not 43,996 full texts or review inclusions. A 43,996-row **synthetic SLR scale fixture is unrelated** except by intentionally matching its scale.
- `interop_scripts/digital_esd/run_world.py`: review/retrieval -> byte verification/text materialisation -> SCALE-1 DB-native PostgreSQL parse/PNF -> processing census/world revisions -> bounded review projections. Never treat a parser nomination as source-level admission or source truth.
- Exact 19 coordinates from `DigitalESDManuscriptMethodologyExact` stay unchanged. Route EfS nominations through pedagogy/competence, sustainability, time, authority, context-transfer and uncertainty; do not add 6x7 universal enumerative cells.
- `DigitalESDAcademicCorpusWorldCrossPollinationExact` and `DigitalESDStudyClaimCeilingExact` continue to own source identity, distinct manifestations/revisions/spans, design-specific claim ceiling, study-family genealogy and independence.

### Ranked scientific P0/P1

**P0-A** Execute/verify authoritative screened full-text/admission receipts (including precise text spans) on local real ERIC artifacts; retain missing/inaccessible/source-only stages. *Not paid by this source-written tranche.*

**P0-B** Independently code Tilbury et al. (2002) chapters, Tilbury & Wortman (2004) practice framework, GreenComp (2022), Elliott's EfS essay, Vikane/Høydalsvik's Norwegian ECE study and relevant empirical Digital-ESD studies; distinguish conceptual prescription from empirical results and from an actual human blind-coding exercise. Record rival codes and disagreements.

**P0-C** Run deliberate discriminators: awareness vs systems understanding; reported student voice vs consequential collective authority; individual adaptive scaffolding vs common inquiry; ecological source provenance and access permissions; participation as classroom activity vs observed collective action; future scenarios vs futures competence; short-term response vs institutional durability.

**P0-D** Reevaluate each of the seven via actual admitted study-by-study/context-specific evidence. Each gets source spans, claim ceiling, proposed method, reviewer disagreement, and one of support/narrow/split/merge/defeat/extend/unresolved. A conceptual fit alone never pays an effect claim.

**P1** Update manuscript results only when P0 paid; publish a transparent evidence table showing each relationship, contextual transfer, source-role, independent evidence units and unresolved contradictions. Reconcile the review draft's outdated statement that ERIC has never been executed with the ERIC retrieval evidence, without conflating retrieval with screening closure.

**Non-goals:** new parser/DB ontology, new generic non-factorability calculus, claiming all 43,996 records were semantically coded, or attributing DASHI mathematical results to EfS/Indigenous scholarship.


## 2026-10-22 correction from coauthor correspondence: manuscript phase, meta-synthesis and deliverables

**Decision evidence**: Alice Brown's 13 October 2026 team email and the follow-up 14 October exchange, inspected in the connected Gmail (private working correspondence; do not quote/distribute without authors' permission), point to an **integrative conceptual review with a bounded author-nominated scholarship corpus, explicit relevance rationales, independently challenged ESD competency mapping, and retrospective/prospective scholarly praxis**. Do not claim the collaboration agreed on statistical meta-analysis. The letter explicitly cautions against describing the authors' work as a 'meta-analysis' and against committing the whole manuscript to a new action-research case study. The seven existing principles are an intermediate, revisable output rather than the headline novelty.

### Correct paper type and conditional meta-analytic lane

Canonical primary consumer: `DigitalESDPaperTypeRequirementParetoExact.integrativeConceptualReview`. The cross-paper operation is **interpretive evidence synthesis / candidate qualitative meta-synthesis** under transparent source-role, scope and alternative-interpretation discipline. A systematic mapping of admitted external studies may supplement this; avoid calling it completed or a quantitative meta-analysis.

Statistical meta-analysis is a **conditionally enabled secondary consumer only** after accepted studies show: (1) a common estimand/intervention-comparator/outcome and compatible population/time horizon, (2) recoverable effects plus uncertainty, (3) reviewed study-family genealogy to avoid double-counting, (4) heterogeneity/explanatory context and missingness review, (5) risk-of-bias/publication-bias and sensitivity receipts, and (6) an explicit reason pooling is meaningful. Otherwise deliver stratified narrative evidence tables and falsification/claim-ceiling analysis. Existing `DigitalESDAcademicCorpusWorldCrossPollinationExact` and `DigitalESDStudyClaimCeilingExact` already own much of this; do not introduce another pooling ontology.

### Updated publication phases / deliverables

| Phase | Current status | Acceptance/deliverable |
| --- | --- | --- |
| 0. Target, rubric, governance | Owner implemented / editorial deadline reverify | Named MDPI *Sustainability* special issue; exact call + paper-type rubric + ethics/AI disclosures, coauthor agreement |
| 1. Bounded author scholarship selection | Partly formalised, author decisions required | Nominated paper list with reasons, source boundaries and accepted/rejected candidates; not just the original nine-item starter |
| 2. Source reconstruction and conceptual synthesis | Seven-principle starter + survival audit source-written | Exact source/revision/span/claim ceiling and rival theme audit; preserve what each source can prove |
| 3. EfS competency and reciprocal challenge | Initial EfS-first formal owner and candidate comparisons committed | Reviewer-audited GreenComp/Tilbury/Elliott/Vikane mappings; relationships support/narrow/split/merge/defeat/extend |
| 4. Broader external review | 43,996 ERIC metadata universe acquired/dedup reported; full review not demonstrated | Actual eligibility decisions, retained full texts, source-audit admission, cross-database status, reviewer disagreement |
| 5. Synthesis and worked applications | Partial manuscript; revised framework not final | One bounded retrospective reconstruction and one prospective research-design demonstration, both source-grounded |
| 6. Quantitative pooling gate | Not demonstrated eligible; optional | Either justified statistical pooled model with full diagnostics OR explicit documented 'pooling not warranted' decision |
| 7. Writing and submission | Working draft only | Revised abstract; introduction, methods, evidence tables, discussion/limitations, references, declarations, coauthor signoff, submission-ready package |

**Phase judgment:** conceptual/methodological architecture and processing apparatus are substantially built; manuscript execution is between phases 2–4, with phases 4–7 *not yet closed*. This is not a finished meta-analysis and not yet a completed external review.

### Highest-alpha deliverable order

1. Obtain collaborative acceptance of the question, paper type, selection logic and retrospective/prospective contributions; retain exact team feedback.
2. Complete the nominated-author-corpus ledger including the additional named works in Alice's 13 October proposal, and make study-level claim ceilings visible.
3. Turn existing EfS source candidates into reviewed source spans and author adjudications, not just further source-written Agda types.
4. Run admitted external screening on real ERIC artifacts and other databases as available, with denominator and missingness receipts.
5. Publish a principle-survival table and two contrasting worked applications, then make a deliberate pooling-feasibility determination.
6. Assemble the *Sustainability* submission, subject to current journal/editorial requirements and responsible GenAI disclosure.

**Hard boundaries:** Being one of ~43,996 ERIC records does not make a study included; reviewer nomination != evidence; team mail != methodological execution; interpretive meta-synthesis != statistical meta-analysis; reflexive worked application != prospective human-subjects research; author invitation != finding.


## Current-week checkpoint — 22–23 October 2026

**Current authoritative planning packet:** [digital-esd-weekly-brief-2026-10-23.md](digital-esd-weekly-brief-2026-10-23.md). It inventories PR #1237, evidence/source boundaries, the repo's integrative-review paper-type owner and the coauthor October correspondence. **This week's P0 is coauthor decisions** on research question, both directions of sustainability, paper type, title/abstract owner, optional 6 November abstract target, and 30 April manuscript milestone. The intended deliverable is a recorded decision packet and abstract outline, **not** statistical meta-analysis or completion of the ERIC corpus. 6 November and 30 April remain proposed internal targets pending team confirmation.
