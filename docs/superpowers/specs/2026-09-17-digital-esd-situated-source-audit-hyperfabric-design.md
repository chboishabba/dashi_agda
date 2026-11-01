# Digital-ESD Situated Source Audit Hyperfabric Design

Date: 2026-09-17
Status: approved architecture, source-written design
Branch: `agent/digital-esd-paper-methodology-primary-sources`

## 1. Goal

Make every source admitted to the Digital-ESD synthesis carry a provenance-preserving, observer-indexed evidence audit rather than a flat quality score. Retain a mandatory 0–5 visibility projection for comparison, but treat that score as a derived view of a richer situated evidence hyperfabric.

The core invariant is:

```text
score != evidence
visibility != quality
conformance != outcome
convergence != same provenance
coordination != fusion
participation != authority
disagreement != invalidity
single observer != whole situated system
coarse score profile != intersectional adequacy
```

## 2. Repository reuse boundary

This tranche MUST reuse existing owners instead of introducing replacement machinery:

- `DASHI.Core.AttributedSourceCore`
- `DASHI.Core.SnowballAttributionProvenanceInvariantExact`
- `DASHI.Core.IntersectionalNonFactorability`
- `DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact`
- `DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact` where available to a consumer
- `DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact` as a structural donor, not environmental evidence for education
- existing Digital-ESD disability/intersectionality, study-absence, externality-incidence, material/lifecycle, political-economy, social-provisioning and durability owners.

Current-master and recent-PR donors are design inputs but are not silently imported if absent from this stale branch. In particular, newer Ibrahim residual/re-entry machinery, PNF/Dewey/QID/DOI bridges and PR #984/#991 refinements should be transplanted only after branch reconciliation or through already-present stable interfaces.

## 3. Attribution and identity discipline

Every source-bearing receipt retains the canonical attributed source object. Where independently verified and applicable, DOI/PMID/PMCID/PDB/taxon/QID/Dewey coordinates remain attached as identity/classification/traversal metadata. Missing or unresolved identifiers remain unresolved and are never guessed.

Identity does not create evidence or authority:

```text
DOI != proposition truth
QID != source authority
Dewey != evidence completeness
citation count != independent support
Pareto position != proof authority
identifier completeness != PNF/evidence completeness
```

External sources own their bounded propositions. DASHI owns the typed reconstruction, observer/index structures, finite collisions, factorisation obstructions, tension receipts, sparse intersection fibres and admission logic.

Two-Eyed Seeing and Kimmerer material are source-bounded interpretive/coordination donors only. Coordinated use does not fuse epistemic histories or transfer authority.

## 4. Primary carrier

The audit is conceptually a situated evidence hyperfabric:

```text
H_ESD =
  Source
  x Observer
  x Context
  x Axis
  x Evidence
  x Provenance
  x Authority
  x Time
  x Relation
```

The 0–5 score is a projection from a situated observation, not the primary evidence object.

## 5. Visibility scale

`Score0to5` has exactly six constructors:

- `score0Absent` — the source does not address or evidence this axis;
- `score1Mentioned` — background/context mention only;
- `score2Indirect` — partial, proxy or indirect evidence;
- `score3DirectIncomplete` — direct source-bounded evidence, materially incomplete;
- `score4Substantial` — substantial direct coverage including important subdimensions/affected groups and explicit limitations;
- `score5UnusuallyComplete` — unusually complete source-specific coverage: object/population, evidential basis, relevant subgroup/incidence, boundaries and limitations are explicit.

The scale measures visibility/coverage only. It does not raise claim ceiling, rank source quality, infer study validity, or transfer empirical authority.

No authoritative grand total exists.

## 6. Mandatory core axes

Every admitted source gets a visibility receipt for all ten core axes:

1. educational outcome/transformation;
2. representation / who is not at the table;
3. disability / effective accessibility;
4. participant voice / interpretation / decision authority;
5. environmental / material lifecycle;
6. externality incidence;
7. political economy;
8. social provisioning / community;
9. maintenance / institutional durability;
10. context / transfer / time / intergenerational scope.

A zero is meaningful absence of coverage. `notApplicable` is separate and belongs to standard-lens applicability, not the core evidence axis.

## 7. Situated observers

Observations are indexed by an explicit observer position. Initial constructors:

- learner/participant;
- disabled/access-needs participant;
- teacher/support worker;
- family/carer;
- institution;
- community;
- worker/supply-chain participant;
- environmental/material observer;
- political-economy observer;
- technical/security/privacy observer;
- normative/standards/process observer;
- researcher/model observer.

Observer positions are not ranked.

A source can contain multiple observations over the same axis from different observer positions. Divergence is retained rather than averaged.

## 8. Situated observation receipt

Each `SituatedAuditObservation` retains:

```text
source
observerPosition
consumerQuestion
axis
evidenceCarrier
score
scoreReason
supportingLocator
limitation
context
time
claimCeilingReading
```

An integer/constructor without a source-specific reason is not an admissible score receipt.

## 9. Tension braid

When two admissible observations cannot be collapsed without loss, retain a typed relation:

```text
convergence
complementarity
productiveTension
unresolvedConflict
scopeDifference
authorityDifference
provenanceDifference
prohibitedCollapse
```

A `TensionReceipt` retains both observations, their provenance, the relation, and the reason they must not be collapsed.

The intended theorem-level discipline is:

```text
disagreement != bad data
same score != same observer state
same observation != same provenance
```

No forced consensus score is required.

## 10. Sparse intersection fibres

Intersectionality is not additive demographic arithmetic. Higher-order intersection receipts are instantiated only when:

- the source actually studies the interaction;
- a declared consumer requires it; or
- a concrete `FactorsThrough` collision shows the flatter projection is insufficient.

Initial required intersection families:

- disability/access × affordability;
- disability/access × maintenance/durability;
- disability/access × social provisioning;
- representation × participant authority;
- political economy × externality incidence;
- political economy × material lifecycle;
- political economy × labour/maintenance;
- environmental burden × place/community;
- present benefit × future/intergenerational burden;
- delivery mode × household care/provisioning;
- vendor dependence × practical exit/accessibility;
- disability/access × interaction usability;
- disability/access × privacy/disclosure;
- participant authority × data governance/privacy;
- AI governance × participant authority;
- AI risk × externality incidence;
- security availability × practical accessibility;
- service continuity × disability-support continuity;
- service management × maintenance labour/funding;
- quality improvement × participant-defined outcomes;
- process efficiency × absolute environmental throughput;
- human-centred design × represented-in-design population;
- physical-space accessibility × online-delivery substitution;
- privacy/security × practical exit/data portability.

A source can score highly on each component axis while scoring zero on their interaction if the interaction is not actually observed.

## 11. FactorsThrough refinement rule

`FactorsThrough` is the formal test for whether a score/observer projection is too coarse for a downstream consumer.

When two states share the same projection but differ on the declared consumer:

1. retain the collision;
2. identify the missing distinction;
3. reopen the affected fibre;
4. add the least consumer-relevant refinement that separates the states.

Do not grow the ontology merely because a concept exists.

## 12. WrongType firewalls

The audit must reject the following category promotions:

```text
coverage score -> source quality
standard mentioned -> standard satisfied
standard satisfied -> observed outcome
claims conformity -> certified conformity
participant present -> participant authority
access provided -> effective accessibility
AI governance -> AI safety
security availability -> human accessibility
environmental efficiency -> environmental sustainability
market efficiency -> distributive justice
open source -> commons governance
Indigenous citation -> Indigenous authority
shared conclusion -> shared epistemology
```

These are modelled as uninhabited promotion types / explicit no-promotion boundaries, reusing canonical WrongType structures where practical after branch reconciliation.

## 13. Normative standards/framework atlas

A canonical standards atlas retains exact version identity and scope for applicable normative/process lenses. Initial families include:

- ISO 9001:2026;
- ISO/IEC 42001:2023;
- ISO/IEC 27001:2022;
- ISO/IEC 27701:2025;
- ISO/IEC 23894:2023;
- ISO 9241-110:2020;
- ISO 9241-161:2025;
- ISO 9241-210:2019;
- ISO 24552:2020;
- ISO 16817:2017;
- ISO 9241-306:2018;
- ISO 24505-1:2025;
- ISO 24505-2:2025;
- ISO 22727:2007 plus separately represented successor/draft lineage when acquired;
- NIST AI RMF 1.0;
- ITIL 4 practice families;
- Six Sigma / DMAIC;
- ISO/IEC 42005:2025 as an adjacent AI impact-assessment candidate where source acquisition is paid.

For copyrighted ISO standards, retain bibliographic identity and legitimately acquired public scope/abstract-level propositions only; do not reproduce proprietary standard text.

Every standard lens has a relationship enum:

```text
addresses
operationalises
evaluatesAgainst
claimsConformity
certifiedConformity
notApplicable
```

Standards are normative/process evidence, not empirical educational-effect evidence.

## 14. Admissibility

Synthesis is query/consumer-relative. Evidence enters a conclusion only through an admissible evidence fibre for that question.

Examples:

- ISO/IEC 42001 can be admissible for an AI-governance requirement but not student learning effect;
- a learner interview can be admissible for lived accessibility but not national prevalence;
- a semiconductor report can be admissible for reported fab water use but not a specific school's AI water footprint.

Admissibility never upgrades the source's underlying claim ceiling.

## 15. Admission contract

No source enters Digital-ESD synthesis without a `SourceAuditAdmission` carrying:

```text
source
sourceRole/claim-ceiling reading
complete core-axis coverage
situated observations
standard-lens applicability declarations
required sparse-intersection checks
tension receipts where present
provenance-retention witness
no-promotion/WrongType boundary
admission/admissibility receipt
scoring protocol version
```

The source does not need nonzero scores. Complete audited absence is a valid profile.

## 16. Corpus-level analysis

Allowed corpus summaries include distributions and residual searches such as:

- proportion of sources with score 0 on disability/access;
- political-economy sources with direct externality-incidence evidence;
- environmental studies with little/no participant authority evidence;
- AI governance sources with no material-lifecycle evidence;
- durability sources that omit accessible-service continuity;
- usability sources without representation evidence;
- locations where admissible observers diverge.

Do not publish one authoritative summed source-quality score.

## 17. Planned owners

Create thin owners with one responsibility each:

```text
DigitalESDSourceAuditScaleExact
DigitalESDNormativeStandardsAtlasExact
DigitalESDSituatedAuditObserverExact
DigitalESDSourceAuditAdmissibilityExact
DigitalESDSourceIntersectionalAuditExact
DigitalESDEvidenceBraidTensionExact
DigitalESDSourceAuditHyperfabricExact
DigitalESDSourceAuditAdmissionExact
```

Matching focused regressions precede production owners where the branch permits a meaningful source-order RED receipt.

## 18. Integration boundary

The existing Digital-ESD branch is heavily diverged from current `master`. This tranche may be source-written here to preserve immediate dependencies, but must not claim current-master integration. Before final production/corpus use, reconcile/transplant onto a current base and bind any newer Ibrahim/PNF/external-identity/Pareto improvements through their canonical interfaces.

## 19. Certification boundary

Source-written != statically checked != Agda-kernel certified.

No Agda/kernel success may be claimed without an exact-head execution receipt. Connector read-back is evidence of repository contents only.
