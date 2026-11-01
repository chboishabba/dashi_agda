# Digital-ESD as a situated, source-governed hyperfabric: implications and execution contract

**Status (1 November 2026):** reusable *structural* hypothesis and executable source-written Agda fixture; **not** an already completed education literature synthesis or a statistical estimate. Read with [research origins](digital-esd-research-origins-and-derivation.md), [live roadmap](digital-esd-roadmap-live.md), and the canonical source owners linked below. The independent source cases are on [#1448](https://github.com/chboishabba/dashi_agda/pull/1448), not a separate corpus.

## 1. The research object is not seven labels, a list of papers or a 7×6 matrix

**Core correction:** the unit of reasoning is a *situated relation whose relevance is question-dependent*, with source, author/reviewer, learners, community, nonhuman/environmental relations, institutional action, resources and time retaining independent identity. Seven named principles are a provisional **projection** of that richer field for manuscript readability. They do not define the field.

A useful schematic (not a new canonical data schema) is:

```text
H = (source/work, manifestation/revision, exact span, source role,
     study/report-family, population/setting, pedagogy, digital substrate,
     participant/collective authority, educator/institution,
     ecological/material/lifecycle relation, temporality/memory,
     benefit/burden/exit, interpretation/rival/uncertainty,
     reviewer decision, claim ceiling, requested research consumer)
```

There is **no implied complete Cartesian table** and no universally sufficient coordinate subset. Existing [SourceAuditHyperfabric](../DASHI/Education/DigitalESDSourceAuditHyperfabricExact.agda), [intersection fibre](../DASHI/Education/DigitalESDSourceIntersectionalAuditExact.agda), [SLR review packet](../DASHI/Education/DigitalESDSLRSourceReviewBridgeExact.agda), [source-audit admission](../DASHI/Education/DigitalESDSourceAuditAdmissionExact.agda) and [PG world](../DASHI/Education/DigitalESDDBNativeAcademicWorldExecutionExact.agda) own the actual types and runtime, not this conceptual tuple.

**Implication 1 — local sections before global syntheses.** Every paper, chapter, institution, community account, learning episode or review decision is a potentially partial local view. Comparing two local views requires a scoped overlap question, exact provenance and an explicit check of whether the shared part truly agrees. Similar labels or similar outcomes do not establish identical actors, context, power, epistemology, measures or histories. Different legitimate accounts may remain in productive tension; this is *not a failure to normalise*.

**Implication 2 — every projection is consumer-indexed.** A 200-word abstract, seven principles, 19-coordinate evidence view, stakeholder survey, learner dashboard, publication count and an aggregate effect estimate are different coarse views. Each is only sufficient for particular questions if their fibre collisions have been ruled out or retained residuals are reopenable. The exact mathematical statement is the existing [intersectional non-factorability theorem](../DASHI/Core/IntersectionalNonFactorability.agda): if two situated states agree after projection but a consumer's answer differs, no post-processing of that projection can recover the answer.

**Implication 3 — first-order and pairwise adequacy are not enough.** Learning, action, ecological/collective consequence, authority and temporal durability can have *joint* interactions invisible in marginal or pairwise tables. The new [finite joint-hyperfabric consumer](../DASHI/Education/DigitalESDJointHyperfabricConsumerExact.agda) constructs two synthetic four-record populations: every cell in the three pairwise joint tables (pedagogy × agency, pedagogy × ecology, agency × ecology) is exactly equal, but their three-way parity differs. This is a rigorous representational counterexample, not an empirical report about education. It is distinct from, and complementary to, the existing [trialectic three-dyads versus face theorem](../DASHI/Cognition/PNF/TrialecticMemoryLearningHyperfabricExact.agda). It proves that a synthesis which reports only pairwise relationships cannot in general answer every higher-order consumer question.

**Implication 4 — dynamic adequacy is stronger still.** A classroom intervention and its immediate outcomes do not determine future capability, remembered history, delayed burden, institutionally retained learning, consent revisions or future choices. Existing [learning/memory hyperfabric](../DASHI/Cognition/PNF/TrialecticMemoryLearningHyperfabricExact.agda) and [situated education trajectory](../DASHI/Education/EducationSituatedInvestmentTrajectoryExact.agda) must be interpreted with the long-horizon, child/family/teacher/community authority and seven-generation *non-appropriation* boundaries. No imported trauma model diagnoses a learner; neither a seven-generation horizon nor a Kimmerer-derived interpretation grants cultural authority to the analyst.

**Implication 5 — academic synthesis is itself a situated intervention.** Who nominated the original source list? Who decided there were seven themes, not six or eight? Who defined sustainability, what was excluded by the database vocabulary, and which voices can approve or contest the final paper? These are coordinates in the **research-method hyperfabric**, not just in the educational systems being studied. Coauthor feedback, blinded EfS coding, bibliographic provenance, unpublished draft permissions and negative case selection therefore need their own historical/reviewer receipts. An exact PR chronology cannot replace those decisions.

**Implication 6 — ontology and outcome can be co-constituted.** Community involvement may alter the *question, criterion and observer* used to judge an educational intervention, not merely change a value of a fixed KPI. Collective authority, ecological relationships and intergenerational consequences are not additional weightings on a fixed individual engagement score. They may require a different relevant question, new source fibres, changed admissibility conditions, and retained dissent. This is precisely why a scalar impact score or standard meta-analysis is not the master consumer.

## 2. Precise formal implementation

The canonical [new Agda owner](../DASHI/Education/DigitalESDJointHyperfabricConsumerExact.agda) is thin:

- `CandidateJointHyperedge case` is indexed by a specific [#1448 CrossPollinationCase](../DASHI/Education/DigitalESDEfSSourceCrossPollinationExact.agda), and reuses the **exact same source-role and canonical braid receipts** from that case; source attribution and EfS locator are welded to one `AttributedSource`. It stays `candidateOnly = true`.
- `JointReviewHyperedge case` cannot be populated *from a candidate alone*: it separately requires an **actual reviewed observation belonging to the source's SLR packet**, a canonical evidence candidate welded to that review, its exact evidence span, an observation revision matching the reviewed full-text revision and packet-analysis full-text identity. It also demands `SourceAuditAdmission` indexed by **the same source**, a study-claim profile whose source is proven equal, and a conditional context-transfer receipt. This is a *type-level specification of further obligations*, **not a verified guarantee that human reviews occurred**.
- `everyPairCountMatches` checks all 12 cells of three 2×2 pairwise tables; `pairwiseTabulationCannotPayThreeWayPattern` reuses `IntersectionalNonFactorability`, with recharting ruled out for any subsequent coarse view.
- Existing trialectic learning and LES socio-ecological/justice hyperfabric boundaries are imported as independent structural donors. They confer neither psychological diagnosis nor community/Indigenous authority.
- The [new regression](../DASHI/Education/DigitalESDJointHyperfabricConsumerRegression.agda) checks a concrete Adefila/EcoCOIL candidate link, all pairwise count equality, non-factorability and non-promotion. It is imported into the existing `EverythingDigitalESDReciprocalBraid` aggregate.

**No new evidence schema, PostgreSQL table, independent indigenous epistemology, SLR corpus or learning theory has been introduced.** Formal source written != Agda checked != scholar-approved/observed.

## 3. Why this changes the seven-principle research strategy

| Candidate principle | Higher-order questions the label can obscure | Review discriminator |
| --- | --- | --- |
| Relational engagement | Activity can be high while inquiry rights or ecological consequence are absent | Did learners help define the relevant problem? What was observed beyond activity? |
| Revisable feedback | Efficient AI feedback may suppress critical values or plural epistemic frames | Can actors reject the model categories and revise what counts as success? |
| Constitutive learner agency | Individual choice may coexist with zero collective/community authority | Trace who can frame, decide, decline, change and review actions; include affected nonparticipants |
| Adaptive support/local choice | Accessibility support may enable collective action or fragment it | Measure accessibility × collective agency × shared outcomes **jointly**, not as separate positive scores |
| Plural situated observers | Equal reported observations can come from different knowledge traditions and authority relations | Retain source role, cultural protocol, observer and consequence rather than forcing shared interpretation |
| Contextual custodianship | Data care may not capture ecological kinship, material supply chains, land or future options | Test ecology × place × governance, not just participant-context descriptors |
| Iterative evidence return | Revision may rebrand unchanged power relationships or forget previous refusals | Reopen historical consent, memory, institutional control, long-horizon burdens and outcomes |

The six initial EfS themes remain an independent source-derived *coding proposal*, not a reverse label mapping. New candidate cases on #1448 do not promote any of these seven labels. There is no guarantee the final synthesis is seven-dimensional; principled **splits, merges, defeaters, unmatched constructs and consumer-relative views** must remain live.

## 3A. Principle survival is a *section over contexts/consumers*, not a scalar

The existing `DigitalESDPrincipleSurvivalAuditExact` deliberately records provisional global-readable snapshots for seven principles. The new joint-consumer owner adds a finite **consumer-relative non-descent witness**: two questions, *digital-course learner voice* and *EfS community decision rights*, share the exact original `constitutiveLearnerAgency` label but yield different provisional classification needs (`provisionallyRetain` and `provisionalSplitCandidate`). By the canonical non-factorability theorem no single function of *the label alone* can answer both.

This is **not an empirical finding** that agency is effective in one setting and ineffective in the other. It is a methodological proof that **the requested research question and situated context belong in the evidence unit**. A final seven-principle survival count is therefore inappropriate without an explicitly declared consumer, population, transfer rule and aggregation criterion. Report a *context-by-question survival matrix with reasons, counterexamples, dissent and missingness*; a single “five of seven survived” headline is at best a bounded, qualified projection, not the authoritative research object.

## 4. Evidence review: how to use the 43,996 ERIC records without fabricating a 43,996-study hypercube

The already acquired/deduplicated metadata universe is a *search denominator*, not a full-text study denominator. Keep canonical PG world revisions, exact manifestation/source revision/span, semantic proposal, reviewed observation, SourceAuditAdmission, study-family independence and claim ceiling. The 19 extraction coordinates and existing 16-subcoordinate study-claim ceiling are *available projections*, not a theorem that every intersection is represented in every source.

**Sparse work rule:** materialise an interaction only when (a) the research consumer requires it, (b) a source explicitly reports it, (c) a contradiction/flat-quotient collision reveals missing adequacy, or (d) a reviewer identifies a material omitted observer. Otherwise record `unreported` or `not applicable` with reasons, rather than a fabricated zero. Never enumerate 43,996 × 7 × 6 × all context axes.

Proposed review packets/queries, all **not yet executed**:
1. **Pedagogy × learner/community authority × ecological/learning outcome.** Search the retained corpus for nominal participation that lacks decision rights; contrast measured competence and meaningful authority, with negative cases.
2. **Digital activity × values reflection × model-category contestation.** Contrast task completion or survey positivity with learner-generated critical or normative interpretations.
3. **Adaptive accessibility × collective-action possibility × institutional resources.** Retain disability, household/work/time, platform exit and burdens alongside participation data.
4. **Place/ecological knowledge × cultural provenance × governance rights.** Retain knowledge tradition, authorship, community partnership, material/ecosystem evidence and permissions; never turn a Kimmerer/Two-Eyed conceptual source into proxy Indigenous consent.
5. **Short-term outcomes × memory/revision × long-run option preservation.** Distinguish observed follow-up from proposed durability or futures competence.
6. **Literature-selection history × coding authority × claim-survival outcome.** Identify whether the seven-provisional labels bias the discovery of independent EfS constructs; retain coding disagreements and source exclusions.

For every packet, require source revision, exact spans, source kind/role, study design/comparator (or explicitly missing), population and setting, source-family identity *hypothesis versus reviewed independence*, temporal horizon, observed participant voice and authority, ecological consequences, rival interpretation, evidence ceiling and reviewer decision. Pairwise table completeness or thematic citation count does not constitute sufficient proof of a triple-level outcome.

## 5. Statistical synthesis consequence

A classical effect-size meta-analysis remains a *possible consumer* over a genuinely comparable subset: specific estimand, outcome and timing, sampling unit, comparator, independence, uncertainty and risk-of-bias. It cannot stand in for the broader situated synthesis, and random-effects heterogeneity alone does not repair incompatible causal questions, unmeasured community authority or absent ecological burdens.

A context-indexed synthesis may legitimately conclude: *this mechanism is supported under setting A and contested under setting B; neither permits generalised efficacy.* That is more informative than a pooled number produced by collapsing incompatible fibres.

## 6. Current-week reviewer-facing decisions and following gates

**6 Nov 2026 (proposed internal abstract approval):** decide whether the main contribution is the *reciprocal, source-governed, situated review method*, **not** the claim that DASHI proves a new pedagogy; preserve the seven as candidate views, the 16 new EfS cases as evidence debts, and the two directions (education for sustainability / sustainability of digital education). Title/abstract should not say “validated seven principles,” “44k studies reviewed” or “novel coupling of digital learning and sustainability.” Request coauthor permission for public use of any draft.

**13 Nov:** two independent EfS readers code without the seven labels; log alternative partitions and meaningful disagreements. Prioritise cases that exercise a three-way consumer, including individual-versus-collective agency and ecological outcomes.

**20 Nov:** make a single retrospective worked case trace `source → span → rival coding → provenance/authority → explicit three-way consumer → review status → possible principle challenge`. Keep prospective worked study-design application separate. Run actual PG world census only with source artifact and DB receipts.

**January–April 2027:** review and extract eligible sources, cross-database coverage, study genealogy, negative cases, retrospective/prospective application, final evidence-sustained principle verdicts and publication gates. April is an unconfirmed internal manuscript milestone; the publicly advertised special-issue submission deadline remains 30 August 2027, to be rechecked.

## 7. Exact unresolved obligations

- **H1 — source history:** identify the seven→eight original corpus registry commit and coauthor source-selection decisions, not only chronology.
- **H2 — derivation:** record real alternative principle partitions and their author adjudication, including why a higher-order community/ecological construct is or is not independent of original seven labels.
- **H3 — source review:** obtain actual span-level review of #1448 cases and independent EF-Side coding; prior study review totals are not substituted.
- **H4 — same-object:** connect every proposed joint review case to source-family, artifact hash/revision/statement/span and reviewed admission; distinguish a paper reporting a review from the primary studies that review covers.
- **H5 — empirical:** identify direct evidence of joint pedagogy × agency × ecology/learning rather than infer it from individually positive marginal themes.
- **H6 — method:** publish counterexamples, negative cases, non-identifiability and the outcome of an explicit meta-analysis feasibility assessment.
- **H7 — governance:** get collaborator selection/coding/approval/attribution receipts; keep private material out of public source.
- **H8 — execution:** Agda 2.9 exact-head checks of the new finite proofs; real PG corpus receipt; documentation and manuscript updated from what those checks actually establish.

**Bottom line:** hyperfabric is not “connect everything so everything supports everything.” It is **connect precisely enough to know what cannot be collapsed, what remains local, what changes under interaction and time, and who has authority to speak for each claim**. That is the substantive methodological contribution the paper can develop and test, not an automatic empirical finding of the code.
