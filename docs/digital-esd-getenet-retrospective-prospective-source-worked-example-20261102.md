# Source-bound retrospective + prospective worked demonstration: Getenet et al. (2026)

**Status 2 November 2026:** ORIGINAL PUBLICATION OBSERVATION + CANDIDATE DASHI RECONSTRUCTION. The full article is open access, but this document is not an independently signed SLR review/admission receipt, and no coauthor has approved this as the paper's Results. It is a concrete first analysis packet for source review, not a substitute for it.

## Recoverable source and code owners

**Original authors:** Seyum Getenet, Katie Burke, Melissa Fanshawe and Alice Brown (2026), "Supporting online learning in teacher education: student-identified strategies and social constructivist implications", *Distance Education*, DOI [10.1080/01587919.2026.2669288](https://doi.org/10.1080/01587919.2026.2669288), published online 20 May 2026. Original section headings below are exact article locators (not byte-stable `EvidenceSpan`s). Actual source version, content SHA, text offsets and independent review need to be captured through the existing SLR `FullTextArtifactReceipt` and `ReviewedSLRAuditObservation` routes.

**Already-owned formalisation:** `DASHI/Biology/EducationCorpusSourceRegistry.agda`, `StudentIdentifiedSupportStrategiesBridge.agda`; source-specific decomposed extension `DASHI/Education/DigitalESDGetenetSourcePartCandidateExact.agda`. Reuse `DigitalESDOpenAxisStudyPartWorldExact`, `DigitalESDSLRSourceReviewBridgeExact`, `DigitalESDStudyClaimCeilingExact`, `DigitalESDSourceAuditAdmissionExact`, `TypedHyperfabricCore`, `IntersectionalNonFactorability` and existing Alice selective invalidation owners. No parallel paper/PNF/SLR ontology.

## A. Retrospective reconstruction of the *original* study

The paper asks: (1) what online learning practices pre-service teachers considered helpful; (2) how perceptions relate to social constructivism; (3) implications for initial teacher education design. The study spans 2019–2024 and a compulsory mathematics course in a regional Australian four-year teacher-education programme. Its questionnaire was distributed to **885 students** in **12 course offerings**; **584 responses** were analysed, with the original paper reporting a response rate of **65.98%**. These are student **responses**, not a randomised intervention sample or evidence from all eligible/nonresponding positions.

The original methodology uses a single, open-ended *one helpful online-learning idea* question, inductive thematic analysis drawing on Braun and Clarke's six phases, NVivo coding/Excel frequency tables, an initial two-researcher coding phase and subsequent team negotiation. The original authors declare teacher-educator/researcher positionality and note that one of the initial coders was not a course-team member. **Specific cohort demographic information was not collected.** The ethics identifiers in the original methods are `ETH2020-0100` and `ETH2023-0847`; ethics clearance does not itself establish student co-decision authority.

The five favourable themes are original study-reported findings. The article also reports a *sixth contrasting/negative* theme and outliers:

| Original paper theme / occurrence | Author-reported coded count | Source section |
|---|---:|---|
| Autonomy and flexibility | 101 | Results, Theme 1 |
| Accessible/centralised resources | 126 | Results, Theme 2 |
| Interaction, community and support | 146 | Results, Theme 3 |
| Scaffolding and guidance | 100 | Results, Theme 4 |
| Organisational self-management | 115 | Results, Theme 5 |
| Negative experiences | 26 | Results, Theme 6 |
| Outliers | 15 | Results, discussion of contrasting answers |

The original reports **45 responses coded twice**. Thus the arithmetical *coding assignment* reconciliation is:

`101+126+146+100+115+26+15 = 629 = 584+45`.

That is a consistency check on the paper's reported numbers, not independent verification of coding, a new participant count, a quantitative pooled effect, or a sustainability outcome. The source's own limitations include its single prompted question, self-report/recall and limited capture of negative and nonrespondent experiences. Do not add percentages of overlapping codes and call that an outcome prevalence.

## B. Decompose ALL research objects, not just five themes

The source-specific Agda `StudyPart` enumerates **15 candidate analysis units**: original questions, theoretical lens, population/sampling, instrument, thematic method, researcher position, five positive themes, negative/outlier responses, bounded original conclusion, omitted/unsampled positions, and retrospective recomposition. Each must be considered across every currently declared research axis. The initial seven-axis example comprises pedagogy/learning, student voice, effective disability access, consequential decision authority, material/ecological burden, temporal/institutional durability and researcher epistemic position. This seven-axis list is an **extensible test projection**, not the world's total axis family or the seven manuscript principles.

Original source-reported coordinates are explicitly `sourceReportedPendingReview`. Other coordinates are `notYetAssessed` pending review; `unmeasuredForQuestion` requires a scoped evidence review that establishes the relevant information was not measured or reported. Do **not** replace these statuses with a false direct-reviewed `JointReviewHyperedge`. An independent reviewer can narrow, modify or invalidate any proposed axis account after checking exact passages.

## C. Retrospective ESD/EfS questioning: legitimate reuse vs overclaim

| Independent sustainability question | What this source can inform | Missing information / limit |
|---|---|---|
| Student agency | Respondents identified online practices they valued | Preference expression is not veto power, research co-design, curriculum governance or collective decision authority |
| Accessible education | Favourable experiences with centralised, asynchronous and printable materials | Does not measure disability-specific assistive usability, access costs, nonrespondent barriers or accessibility continuity |
| Intersectionality | Some statements connect care commitments, time and online flexibility | No collected cohort demographic dataset; cannot estimate disability × care × finances × institutional power effects |
| Relational/collective learning | The paper reports experiences of peer forums, community and teacher contact | Does not establish consequences for community sovereignty or interdisciplinary ecological inquiry |
| The sustainability of digital education | Offers methods to ask which technical arrangements students valued | Does not report actual device/infrastructure/worker/environmental lifecycle burdens or equitable procurement |
| Durability and transformation | Source spans six years of course offerings and reports contemporary preferences | Multi-year sampling is not a within-person longitudinal sustainability-effect measure |
| Negative/outlier epistemics | The sixth theme shows some respondents reported poor online experiences | The supportive themes cannot be promoted to universally successful or harmless online learning |

**Candidate inference:** The contrasting theme and unsampled positions make a five-positive-theme-only manuscript projection unsafe for some research questions. That is a source-inspired *DASHI methodological inference*, not a claim about the original authors' intent and not a proven participant-level intersectional outcome.

## D. Cross-study gap routing (not evidence backfilling)

A separate EfS case (for example Taimur–Onuki 2022, `10.1016/j.ijer.2022.101994`) may suggest research questions about transformative pedagogy, systems and collective ecological learning. Such comparison may *point to* Getenet's omitted ecological/institutional observation coordinates or suggest a future measurement. It **cannot** supply measured effects for Getenet's 584 respondents, establish group equivalence, transport environmental outcomes, grant community authority or resolve a contradiction without source-specific comparison/transfer receipts. Preserve the original author attribution on both sides.

## E. Prospective study redesign: questions and evidence to acquire

Future researchers should distinguish **reported preference** from **actual control over educational decisions**; document who was eligible but absent or declined, without interpreting undisclosed identities as zero; obtain appropriately consented disability- and access-specific lived evidence where relevant; observe care/work/affordability × course-platform interaction rather than independent marginals; measure teacher/infrastructure maintenance and material externalities; permit adverse/contradictory participant experience to remain in the analysis; compare distinct observer roles without forced consensus; and observe institutional/learning change over meaningful time horizons.

At each source-part and current `n`-axis address, state direct reviewed / author reported pending review / not-yet-assessed / conditional candidate / contested / source-reviewed unmeasured / inaccessible / justified N/A. Do not force a full higher-order Cartesian tensor; instantiate an interaction when evidence, a consumer question or a constructive `FactorsThrough` obstruction requires it. Recomposition must reopen omitted information and preserve incompatible local interpretations.

## F. Exact reproducibility gates before manuscript Results

1. Resolve a legal open-access full-text snapshot with DOI, source identity, text digest, exact passage offsets or structured evidence coordinate and signed reviewer receipt.
2. Confirm the article's full coded tables and category definitions; check the 629-assignment arithmetic against original supplementary materials and reviewers' interpretation of outliers.
3. Reconcile every one of the 15 candidate parts with the actual source passage and investigate omitted parts, source interpretation and existing literature-review context.
4. Apply the versioned open `n)-axis family to every part; when adding an axis, reaccount each part; record review, missingness and inapplicability separately. Audit study-world and author/synthesis epistemics, not just participant observations.
5. Only then instantiate `ReviewedPartAxisEvidence`, `JointReviewHyperedge` and actual reviewed temporal world values, with source revision and selective invalidation receipts.
6. Independently adjudicate the EfS comparison and coauthor approve retrospective/prospective manuscript statements. **No human participants have been recruited for a prospective study by writing this protocol.**

**D5 search deferral:** This first example and the existing ERIC/SLR pipeline do not require the extra four database searches to be executed now. The review coverage limits must remain explicit until that later, separately authorised work is performed.
