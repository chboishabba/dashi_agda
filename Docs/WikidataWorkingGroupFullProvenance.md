# Wikidata / JMD full provenance and externalities handoff

## Purpose

This document describes the **full convergence surface** carried by PR #582.  The
smaller `WikidataWorkingGroupEverything` root remains useful for a focused
ontology/checker review, but it is not the provenance boundary of the handoff.

The full root is:

```text
DASHI/Ontology/WikidataWorkingGroupFullProvenanceEverything.agda
```

It retains the relevant source-bearing and cross-domain lineages so that a
reviewer can trace not only a theorem dependency but also the origin, scope,
externalities, interpretation frame and authority boundary that travel with it.

## Real ancestry, not detached copies

The convergence branch preserves the relevant PR histories as branch ancestry.
At the current convergence point the following lineages are contained by #582:

- **#555 / #558 — James Michael DuPont / Aristotle Wikidata Lean bridge.**
  Complete 39-module source manifest, source hashes, theorem/checker contracts,
  data-model/RDF/alignment/diagnostics bridges and the local Lean execution
  receipt producer.
- **#561 — empirical genealogy / source-role provenance.**  Relation kind is
  separated from evidence strength; Alice Brown institutional-agency material,
  Bringing Them Home, Kimmerer attribution, quote/context and claim-manifest
  boundaries are retained.
- **#570 — proof-relevant correspondence and edit transport.**  Occurrence
  identity, unique correspondence, ambiguity fail-closed behaviour, and
  reverse-dependency locality are preserved as full ancestry.
- **#573 / #586 — Alice-linked intersectional early learning and
  counterfactual/externality evidence.**  The first tranche retains situated
  capability, eKindy, developmental affordances, child/family/community
  authority and extensive source registries; the second retains counterfactual
  heterogeneity, outcome vectors, quality/workforce constraints, evidence
  vintage/reopening, uptake stratification and the DOI-bearing comparative
  evidence round-two registry.
- **#581 — JMD-linked parent/progenitor hyperfabric.**  Parent roles, genetic /
  gestational / legal / social distinctions, P8810 projection fibres, exact
  reopening, predicate descent, dynamic authority and JMD theorem conformance.
- **#584 — observer refinement, future-language safety and provenance
  dynamics.**  Exact receipt motion, future-language defects, factorized
  refinement, recoverable towers and the separation-vs-world-authority boundary.
- **#585 — section/alignment provenance and mathematical reconstruction
  noncanonicity.**  Retained as an adversarial mathematical provenance lineage;
  domain-specific arithmetic conclusions are not required by the Wikidata root.
- **#587 — operator-indexed evidence and 3/6/9 / ternary fibre geometry.**  The
  branch retains the action-indexed opposition discipline, the `27^3 = 3^9`
  stratified carrier, variable-rank residual fibres and aggregate-loss
  countermodels as generic mathematical pollen.
- **#588 — SIO semantic surfaces.**  SIO supplies interoperable entity,
  attribute/measurement, information, process, role and evidence vocabulary;
  DASHI supplies the stronger projection/provenance/reconstruction/authority
  semantics.

The convergence process keeps the current #582 implementations authoritative
where independently-developed generic cores overlapped, but merge ancestry is
retained so source history is not erased.

## Full Alice Brown / ecology-of-data contribution

The full handoff imports:

```text
DASHI/Biology/AliceBrownEpistemicGovernanceEverything.agda
DASHI/EverythingEarlyLearningIntersectionalReappropriation.agda
DASHI/Governance/EmpiricalGenealogyRound3Everything.agda
```

The first already exposes the repo's mature object:

```text
fine carrier
+ consumer family
+ consumer-indexed question family
+ relevance measure
+ projection
+ reopening residual
+ admissible dynamics
+ coarse policy
+ governance.
```

It also brings the source-bound Alice corpus loom, OEF multi-fibre feedback,
measurement policy, Brown/Kimber governance profile and exact SoTL quotient
pipeline into the provenance closure.

The second and third retain the broader externalities Alice's work was being used
to model: situated accessibility, child/family/community agency, counterfactual
care environments, uptake, workforce and quality, developmental horizon,
evidence vintage, institutional-choice constraints, Indigenous/community source
boundaries and heterogeneous downstream outcomes.

These are not imported as claims that educational findings prove ontology
results.  They are retained because their **formal provenance discipline** is
part of the requested handoff: interpretation frame, context, missingness,
contestability, participant/collective authority, non-compensatory evidence
axes, versioned evidence and exact source-to-recommendation reopening.

## SIO public semantic surface

The convergence includes `DASHI.Semantics.SIOSemanticSurfaceBridge` and the
source lineage from PR #588.

Primary bibliographic source:

- Michel Dumontier et al., *The Semanticscience Integrated Ontology (SIO) for
  biomedical research and knowledge discovery*, Journal of Biomedical
  Semantics 5:14 (2014), DOI `10.1186/2041-1480-5-14`.

The intended layering is:

```text
fine carrier
  -> DASHI proof-relevant observer / provenance fibre
  -> SIO semantic surface
  -> RDF / Wikidata / ITIR consumer.
```

An SIO evidence assertion is not thereby a proof theorem, and an SIO role
assertion is not thereby current authority.

## Source and DOI policy

The public source policy is formalized in:

```text
DASHI/Ontology/WikidataWorkingGroupSourcePolicyExact.agda
```

and reuses `DASHI.Core.AttributedSourceCore`.

For bibliographic sources the preferred carrier retains:

```text
author
title
publication context
year
DOI state
canonical URL
source kind
relationship to the formalisation
attribution visibility.
```

DOI state is typed:

```text
doiRecorded <doi>
noDOIRecordedByAtlas
```

An empty string is not the no-DOI sentinel.  `noDOIRecordedByAtlas` is an
atlas-local provenance statement, not a universal assertion that no DOI could
exist anywhere.

For executable formal sources, source identity is instead carried by exact
archive/revision identity, content hash and theorem/checker contract.  The JMD
Lean bridge therefore keeps the supplied archive/source hashes and exact theorem
names rather than inventing bibliographic metadata for source code.

A citation does **not** import proof or create ontology/edit authority.  Source
counts are provenance descriptors, not truth weights.

## Selected DOI-bearing provenance now retained

The convergence retains source registries containing, among many others:

### Alice / participation / ecology

- Alice Brown & Megan Kimber, *Repositioning Student Voice and Agency: A Call for
  the Epistemic Expansion of Scholarship of Teaching and Learning Inquiry*, DOI
  `10.1177/14697874261426374`.
- Roxanne Finn & Alice Brown, *Custodians of an ecology of data: Foundational
  theory and practice for data analysis in a complex world*, DOI
  `10.1177/14687941241234293`.
- Getenet, Burke, Fanshawe & Brown, *Supporting online learning in teacher
  education: student-identified strategies and social constructivist
  implications*, DOI `10.1080/01587919.2026.2669288`.
- Leslie, Fanshawe, Larsen & Brown, *The Perceptions Parents of Dyslexic Children
  Have on Barriers to Meaningful Parent-School Partnerships in Australia*, DOI
  `10.1080/09362835.2024.2389081`.
- Leslie, Brown & Larsen, *Parental Allyship for Children With Dyslexia: A
  Conceptual Lens on Disability Experience*, DOI
  `10.1177/07319487241251730`.

### Counterfactual / quality / policy externalities

- Cornelissen, Dustmann, Raute & Schoenberg, *Who Benefits from Universal Child
  Care?*, DOI `10.1086/699979`.
- Duvander & Ellingsaeter, *Cash for childcare schemes in the Nordic welfare
  states*, DOI `10.1080/14616696.2015.1124903`.
- Sipila & Korpinen, *Cash versus Child Care Services in Finland*, DOI
  `10.1111/1467-9515.00102`.
- Gruber, Kosonen & Huttunen, *Paying moms to stay home*, DOI
  `10.1016/j.jpubeco.2025.105496`.
- Laaninen, *Duration of child home care allowance period and school success*,
  DOI `10.1016/j.rssm.2025.101063`.
- OECD, *Starting Strong VI*, DOI `10.1787/f47a06ae-en`.
- OECD, *Providing Quality Early Childhood Education and Care*, DOI
  `10.1787/301005d1-en`.

### Generic information / interpretation mathematics

- Nuel D. Belnap, *A Useful Four-Valued Logic*, DOI
  `10.1007/978-94-010-1161-7_2`.
- J. Michael Dunn, *Intuitive Semantics for First-Degree Entailments and
  'Coupled Trees'*, DOI `10.1007/BF00373152`.
- David Blackwell, *Equivalent Comparisons of Experiments*, DOI
  `10.1214/aoms/1177729032`.
- Patrick Cousot & Radhia Cousot, *Abstract interpretation: a unified lattice
  model for static analysis of programs by construction or approximation of
  fixpoints*, DOI `10.1145/512950.512973`.

The individual source registries remain the authority for their exact role and
promotion boundary; this document is a navigation index, not a substitute for
those records.

## Working-group ontology pipeline

The ontology-facing path remains:

```text
pinned source ontology / source code
  -> unique provenance-bearing correspondence
  -> concrete transcription / acquisition
  -> explicit alignment
  -> declared inference language
  -> source/transcription/alignment/target support squares
  -> active-obligation completeness
  -> diagnostic interpretation with frame + missingness + contestability
  -> review-only repair candidate
  -> exact reopening receipt to the source state.
```

Important non-collapses retained by the full provenance surface include:

```text
conflict != missing evidence
identifier mapping != semantic equivalence
subclass-safe != disjointness-safe
product observation != permission to pool semantics
checker false != target ontology false
source support != edit authority
reopening != truth promotion
later evidence != erasure of earlier evidence
intervention label != situated effect
public entitlement != complete action router
same role/label != same ontology scope.
```

## Review roots

Full provenance / externalities:

```text
agda -i . DASHI/Ontology/WikidataWorkingGroupFullProvenanceEverything.agda
```

Focused ontology/checker review:

```text
agda -i . DASHI/Ontology/WikidataWorkingGroupRegression.agda
agda -i . DASHI/Ontology/WikidataWorkingGroupEverything.agda
```

This document does not claim those commands have been run in the current
connector environment.  A fresh kernel-clean claim requires the repository's
Agda 2.9 toolchain.
