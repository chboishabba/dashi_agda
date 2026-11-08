# CCDCOE cognitive-warfare primary-source / DASHI formalisation

Status (2026-11-04): **source-written, not kernel-checked in this pass**.
This is an attributed *finite structural model*, not a validation of a
military, clinical, political, or empirical diagnosis.

## Sources and interpretation boundaries

**Primary research:** Fedir Korobeynikov, Andrii Davydiuk, Volodymyr Mokhor,
*Ontological Foundations of Cognitive Warfare* (NATO CCDCOE, Tallinn, 2026),
https://ccdcoe.org/uploads/2026/04/ONTOLOGICAL_FOUNDATIONS_OF_COGNITIVE_WARFARE.pdf .
The CCDCOE published its announcement on **10 April 2026**, not on the date
shown in the viral video's overlay. The publication warns that it does **not
necessarily represent NATO policy**.

**User-supplied commentary:** an SRT transcript of a short video whose
speaker identifies himself as Adam Rosner. It presents an
“arbiter/narrative/projection-surface/in-group–out-group” interpretation,
Plato's cave, literacy statistics, and Russian reflexive-control history.
These are the speaker's assertions. Do **not** attribute that four-mechanism
model to the CCDCOE paper.

**Related, independently published 2026 source:** the same authors'
*A Structural Model of the Human Agent in Cognitive Warfare*:
https://ccdcoe.org/library/publications/a-structural-model-of-the-human-agent-in-cognitive-warfare/ .
It moves from group/system layers to personal invariants, transition
connections, altered holonomy, and invariant compatibility. Those are
additional research proposals, not proved by this finite graph.

## Prior art reused (never re-owned)

- `CognitiveWarfareAdmissibleDetectionExact`: same present appearance, differing
  underlying origins; future admissible provenance inspection may separate them.
- `CognitiveWarfarePlatoTraumaDetectorWeldExact`: content / reachable cone /
  provenance independence, query-specific observation, no hostile-intent
  inference from a cone change.
- `PlatoCaveTraumaMemoryDecisionBridgeExact`: projected shadow is not
  automatically false; refinement does not confer ultimate-reality authority.
- `IntersectionalNonFactorability`: generic witness blocking global
  factorizations through lossy observers.
- `AttributedSourceCore`: citation does not import proof or endorsement.
- `TrialecticMemoryLearningHyperfabricExact` and `EpistemicAttractorCore`:
  experience / truth / evidence / interpretation and self-sealing belief
  updates remain separately typed.
- Historical PRs: #317 (cognition), #531 (epistemic governance), #584
  (observer refinement), #1458 (higher-order hyperfabric).
- Direct predecessor: commit 82f5bcba73fc32ae08d4a80909075b0f5ae841d1.

## New finite theorem surface

`DASHI/Cognition/CCDCOECognitiveMultiplexInvariantExact.agda`

1. Exact five-layer constructors: epistemic, axiological, identificatory,
   social, teleological. Every layer has the **same two actor nodes**.
2. Local within-layer operation is preserved when a chosen cross-layer
   bridge is removed (`localOperationUnchangedByCut`).
3. A four-bridge dependency chain is a selected spanning path. For all
   three other Boolean edge values, losing the third bridge cuts this path
   (`singleCutBlocksPath`). This is a **chosen path** theorem, not a claim
   that any single edge disconnects an arbitrary multiplex.
4. The intact and cut configurations have the same visible
   `OutwardReport` but different path states; generic
   `NonFactorabilityWitness` rules out perfect inference of this
   structural property from outward functionality alone.
5. A four-episode source case shows **both** directions fail:
   architecture does not determine organic-versus-influence provenance,
   and provenance does not determine architectural integrity.
6. Abstract bridge restoration makes the selected path pass again.
   This is not a validated, safe, consentful or feasible real-world repair.

No empirical coefficients, causal weights, observed agencies, adversary
identities, or field measurements are invented. These remain open gates.

## Formal model and boundaries

For the selected actor `a`, write the four interlayer links as
`e(a), v(a), i(a), s(a) ∈ {0,1}`, and define

```text
P(a) = e(a) ∧ v(a) ∧ i(a) ∧ s(a)
```

Then `P(a) = 0` whenever the selected `i(a)=0`, irrespective of
the other three link values. In the witness the within-layer relations
are all `1` while `P(a)` changes from `1` to `0`.
This is a proof of **structural possibility**, not that actual communities
always follow a four-bridge chain.

Observation/provenance non-equivalences:

```text
same outward report ≠ same cross-layer integrity
same architecture ≠ same provenance
same provenance ≠ same architecture
coherence ≠ truth
source citation ≠ proof of the source theory
```

The paper explicitly says that quantitative connectivity indicators,
connector-node identification, and metrics of cognitive coherence require
further research. Its “constitutive invisibility” claim concerns possible
unrecognised influence, not a theorem that detection is impossible for
every observer and every evidence-acquisition procedure.

## Attached video: audit

- **Genuine source, false novelty framing:** CCDCOE released the work in
  April 2026; an overlay dated 22 September is not its publication date.
- **“NATO has announced global war”**: not supported. A CCDCOE research
  publication is neither a war declaration nor necessarily NATO doctrine.
- **Four projection-surface mechanisms**: commentary's framework, not a
  formal four-step theorem in the actual paper. The Plato cave comparison
  is an analogy, not evidence of empirical completeness.
- **“Impossible to see”**: overstatement. The paper's relevant claim is
  that a target *may never become aware* and attribution can be difficult.
- **OECD literacy**: 2023 PIAAC OECD average ~11% at Level 4 and ~1% at
  Level 5, not a robust categorical 13%; “sixth-grade reading” is not a
  valid direct translation of adult PIAAC proficiency levels.
- **Surkov and Russia**: historical influence/reflexive-control material
  requires independently sourced causal analysis. It does not establish
  that Surkov invented the techniques or “engineered” the whole Ukraine war.
- **Protection**: verify primary sources, provenance, and observer-relative
  evidence; preserve epistemic suspension and revisability. Neither
  “absolute truth” rhetoric nor mere institutional trust is a mathematical
  or empirical guarantee of immunity.

## Exact open gates

G1. Kernel-run the new Agda file and its imports; add a focussed regression.
G2. Lift the toy actor set and four-link selected path to a general
    finite multiplex with vertex- and layer-indexed edges, arbitrary
    paths, and explicit connectivity proofs.
G3. Define source- and time-indexed measured connectivity indicators,
    sampling/provenance uncertainty and falsifiable coherence metrics.
G4. Identify causal perturbations using longitudinal/experimental designs;
    distinguish externally originated influence, intentional hostile
    operations, incidental divergence and legitimate criticism/dissent.
G5. Lift to real observer/action resources, admissible future queries,
    memory-preserving repair, individual consent and pluralism.
G6. Keep the later CCDCOE personal-holonomy model as a *separate*
    candidate bridge pending exact transport and measurement.

Source assertions, mathematical witnesses, candidate explanations, and
real-world attributions must remain distinct authority classes.

## 2026-11-06 exact max-cut (PR #1467)

**Implementation status: SOURCE-WRITTEN, NO AGDA KERNEL RECEIPT.**
The source audit has been rechecked against the attached 6m24s SRT,
the actual original CCDCOE April-2026 PDF (sections 5.1–5.4), and
the authors' later individual-agent paper. Explicit no-promotion
boundaries are preserved.

### Reused prior art, not reimplemented

- `DASHI.Core.IntersectionalNonFactorability`: every observer inadequacy
  witness uses the **existing** `NonFactorabilityWitness` and
  `FactorsThrough` definitions.
- `DASHI.Core.QueryIndexedProjectionAdequacyExact`: one outward
  observation is adequate for outward function and demonstrably
  inadequate for inter-layer integrity and provenance.
- `DASHI.Core.AttributedSourceCore`: research-paper attribution.
- `DASHI.Cognition.PNF.EventAlgebra`: actual `EventPNF`,
  `CandidatePNF`, revision and temporal coordinates.
- `DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact` and
  `CognitiveWarfarePlatoTraumaDetectorWeldExact`: existing noncausal
  provenance, action cone and coherence/truth firewalls.
- `DASHI.Cognition.PlatoCaveTraumaMemoryDecisionBridgeExact`:
  source-native refinements are conceptually separate from Plato
  metaphors or claims to possess 'ultimate truth'.

### Source-written mathematical deliverables

| Gate | New owner/proof | Exact result / limit |
| --- | --- | --- |
| M1 generic multiplex | `CCDCOEMultiplexGraphCutCoreExact` | Common actor carrier, two types of typed edges, arbitrary proof-bearing walks and concatenation, retained-edge partition and disconnection theorem |
| M2 five-layer cut | `CCDCOEFiveLayerCertifiedCutExact` | All original intra-layer links survive; exhaustive interlayer constructors certify a genuine cut separating epistemic from teleological layers, for **both actors** |
| M3 alternate-path safety | `scripts/check_ccdcoe_cognitive_multiplex.py` | Exhaustive 16 connector masks × four ordered actor pairs; bypass edge must *invalidate* cut certificate |
| M4 query sufficiency | `CCDCOEQueryPNFEvidenceBridgeExact` | Source-native `QuerySemantics` shows outward observer sufficient for function, insufficient for connectivity/provenance; recharting cannot restore lost information |
| M5 PNF interface | `EvidenceOf About episode question` | Actual PNF event and candidate, plus **application-provided typed `About` proof**; existing event/observation time and revision-retention fields reused, no synthetic observation promoted |
| M6 personal context | `CCDCOEPersonalHolonomyBoundaryExact` | Different loop transport under unchanged public role; finite non-factorability and no hostile-origin inference |
| M7 old example | `CCDCOECognitiveMultiplexInvariantExact` + regression | Boolean selected-path cut, independent origin/architecture, abstract repair and bounds |

### Why this is stronger than the previous four-edge example

A broken **specified path** does not imply graph disconnection when
alternative routes exist. The generic theorem first supplies a
partition map `side : V → Bool`, then requires every surviving
edge to be certified same-side. Only then can *any* walk from a
true-side node to a false-side node be ruled out. The five-layer
case discharges this stronger edge-by-edge obligation by exhaustive
constructor pattern matching. The Python counterexample adds a
cross-partition bypass edge: the certificate fails and reachability
returns.

```text
path missing != graph disconnected
every surviving edge side-preserving + endpoints opposite sides
    => no surviving path can join endpoints
```

### Exact still-open gates (do NOT claim completion)

| Gate | Remaining acceptance evidence | Why the graph proofs do not pay it |
| --- | --- | --- |
| KERNEL | `agda -i .` compile each new module, regression, and cognition umbrella, inspect CI and use explicit `--safe` where dependency graph permits | No Agda executable or CI kernel receipt accessible in this pass |
| MEASURE | independently measured, appropriately sampled, time-stamped layer membership, edge existence, confidence/uncertainty, and criterion-valid group-level indicators | Synthetic complete intra-layer relations do not represent measured networks |
| CAUSAL | longitudinal/experimental, confounder-sensitive discrimination between voluntary change, institutional failure, external influence, hostile intention, and independently verified events | Four-episode counterexample proves an identification **impossibility** from structural state alone |
| PNF-PRODUCER | source-licensed original `EventPNF` and `CandidatePNF` for a **specific** publicly inspectable event with typed `About` witness and revisable lineage | A contract requiring evidence is not an actual ingested evidence record |
| HUMAN | establish that observed decisions across real contexts are faithfully represented by a selected personal state/connection, and that holonomy transport is empirically meaningful | Two-state finite loop is mathematical analogy, not psychological measurement |
| INTERVENTION | consent, privacy, pluralism, reversible action, effectiveness, adverse effects and independent oversight in a declared setting | `abstractRepair` is only a mathematical map that resets an edge |
| EXTERNAL | distinguish CCDCOE original systemic paper, later human-agent/companion work, presenter commentary, and DASHI theorems in every claim | Citation, interpretation, and proof are different authority types |

### Falsifiability and ethical requirements for any real-world extension

A legitimate observational study must define its sampling frame and
decision-process outcomes first, collect only proportionate,
consent-governed **aggregate procedural** observations, pre-register
the connectivity indicator and negative controls, test stability
under measurement error, and explicitly measure alternative
explanations. Do not operationalise the model as surveillance,
psychological classification of individuals, or a label for dissent.
No manipulation of participant beliefs is required or authorised
by the formal programme.

### Regression commands

```sh
python3 scripts/check_ccdcoe_cognitive_multiplex.py
agda -i . DASHI/Cognition/CCDCOEMultiplexGraphCutCoreExact.agda
agda -i . DASHI/Cognition/CCDCOEFiveLayerCertifiedCutExact.agda
agda -i . DASHI/Cognition/CCDCOEQueryPNFEvidenceBridgeExact.agda
agda -i . DASHI/Cognition/CCDCOEPersonalHolonomyBoundaryExact.agda
agda -i . DASHI/Cognition/CCDCOECognitiveMultiplexInvariantRegression.agda
agda -i . DASHI/Cognition/Everything.agda
```

Until an actual successful Agda run is recorded, the formal status
is **source-written, not kernel-verified**. A successful finite
Python test is not an Agda proof receipt, and neither establishes
empirical cognitive warfare.

## 2026-11-06 P3 causal-trialectic source max-cut

P3 now has two additional golden Agda source owners, a regression, a finite
Python checker and a detailed source/PR archaeology ledger. Read
[CCDCOE P3 Causal-Trialectic Source Max-Cut](../roadmaps/CCDCOEP3CausalTrialecticSourceMaxCut20261106.md)
for the exact new theorems and evidence gates. These sources extend the original
five-layer certified-cut model, reusing in-repo climate-denial, S3, intersectional,
Brown, Indigenous/Two-Eyed, Žižek, Kimmerer and ITIR owners. The Sophontic,
Bolo, ESD and runtime Wiki PRs are explicitly provenance-controlled donors,
not silently imported unmerged implementations. Golden kernel verification
and real causal/intent identification remain OPEN.

## Intersectionality correction (6 November 2026, follow-up)

The P3 mathematical owner has been corrected after inspecting the actual
`IntersectionalConstraintGeometryExact`, `IntersectionalBinaryInteractionBridgeExact`,
`IntersectionalNonFactorability`, `BinaryInteractionNonseparabilityExact`,
`IndexedRelationalHyperfabricSpineExact` and longitudinal axis-bundle owners.
Two race-axis positions are **not** identified with two sex-axis positions
because both lists have cardinality two. Axis indices are distinct types;
cardinality, order and equal numerals do not supply a cross-axis coercion.
The new `CCDCOEP3TypedIntersectionalAxisExact.agda` consumes the original
rectangle obstruction and proves a full typed-coordinate observation can
still lose context and recognition outcomes; any recharting of that observer
also loses the distinction. The earlier `2x+2y+x*y` toy was removed as
an intersectionality formalisation, not merely relabelled. The definitive
P3 evidence/accounting roadmap is
[CCDCOEP3CausalTrialecticSourceMaxCut20261106](../roadmaps/CCDCOEP3CausalTrialecticSourceMaxCut20261106.md).

## Canonical verification route (parallel_checker)

The focused acceptance entrypoint is `bash scripts/check_ccdcoe_cognition_agda.sh`.
It runs both finite Python regressions, scans every focused module for holes,
then invokes the **existing** `scripts/run_agda29_parallel_check.sh` with
all focused Agda modules and `DASHI/Cognition/Everything.agda`. The
parallel checker owns Agda 2.9, cache and resource policy; do not run Nix
directly. Its exact-head success receipt is still required; this repository
edit is not a successful kernel execution.

## 7 November — primary-document empirical max-cut: April 1998 API plan

A primary-source discovery changes the case status. The Congressional Record
(vol. 144, issue 48, April 27, 1998, pp. H2323-H2327) reproduces the **April 3,
1998 draft Global Climate Science Communications Action Plan**. Authoritative
published HTML: https://www.govinfo.gov/content/pkg/CREC-1998-04-27/html/CREC-1998-04-27-pt1-PgH2323.htm.

The original document contains an accompanying draft-circulation note and a
proposed meeting (rendered lines 425-449), named contributors (550-560), an
explicit objective to influence views and a proposed before/after evaluation
(568-590), media training/outreach proposals (599-646), the proposed data
centre (652-723), and planned tracking measures (788-795). These statements
establish **documented coordinated planning by the identified draft group**,
not executed campaign activities, achieved effects on attitudes, or a unified
command structure for all historical climate-denial organisations.

New original source owner: `CCDCOEP3API1998PrimaryPlanExact.agda`.
It states the primary locator, separates proposed activity from observed
implementation, constructs finite compatible implementation worlds, proves
`draftDocumentDoesNotIdentifyImplementation`, and provides a conditional
archive `ExperimentBundle` discriminator. The 1998 primary document is now a
positive contrast to the existing Oreskes/Conway grade-B broader historical
genealogy; **no unreviewed causal/direct-transfer join is invented** between
them.

The source manifest at `Docs/research/ccdcoe_p3_climate_case_manifest.json`
now contains six source-span anchored plan claims and six proposed PNF intake
rows with source event/publication dates and typed roles. Original scanned
file digests, true parser character offsets, parser profiles, reviewer approval
and ingestion/observation times are explicitly null; the rows are not presented
as admitted `EventPNF` objects. The manifest validator rejects invented
review receipts and fabricated implementation/impact measurements.

**Original-source status:** public contemporaneous document and paragraph
coordinates ACQUIRED; source-to-PNF *candidate* schema SOURCE-WRITTEN;
canonical runtime PNF/parser and original content-digest admission OPEN.
**Causal status:** actual draft-group coordination planning DOCUMENTED;
execution, exposure, mechanism effects, institution-wide central command and
population outcomes UNIDENTIFIED. The original plan suggests monitoring public
opinion, but it does not establish a post-implementation effect estimate.

**Highest-alpha remaining factual cut:** find approval/funding and campaign
implementation records, dated delivery/exposure records and an actual
pre/post or suitable comparative public-opinion/media outcome dataset. Follow
with explicit overlap/selection/measurement validity, uncertainty and source
attribution. Do not try to substitute another finite logical proof for those
missing historical measurements.

## 7 November follow-up: original 1998 API response and later independent activity

A new contested-attribution tranche is integrated in
`CCDCOEP3ClimateContestedAttributionExact.agda`.

Source records, in **separate** evidentiary classes:

1. The 27 April 1998 Congressional Record preserves the 3 April 1998
   draft climate communications action plan and its proposed strategy.
   Source: https://www.govinfo.gov/content/pkg/CREC-1998-04-27/html/CREC-1998-04-27-pt1-PgH2323.htm
2. The 1 May 1998 public-radio `Living on Earth` programme reports the
   API vice-president's response that meetings and correspondence were
   personal initiatives of a lower-level employee. This is an
   **attributed contemporary institutional counterclaim** concerning
   authorisation; it does not erase the document or prove non-adoption.
   Source: https://www.loe.org/shows/segments.html?programID=98-P13-00018&segmentID=1
3. The 5 September 2017 `Washington Post` investigation independently
   reports later Cooler Heads Coalition advocacy, funding, interviews
   and political activity. Its quoted denial of overarching funder
   direction is retained as an attributed participant account. This is
   not a dated implementation receipt for the *specific* 1998 plan.
   Source: https://www.washingtonpost.com/investigations/a-two-decade-crusade-by-conservative-charities-fueled-trumps-exit-from-paris-climate-accord/2017/09/05/fcb8d9fe-6726-11e7-9928-22d00a47778f_story.html
4. The 23 October 2019 House hearing is a primary record of **later
   testimony and legislative scrutiny**, not proof that the 1998
   plan was executed or causally effective.
   Source: https://www.govinfo.gov/content/pkg/CHRG-116hhrg38304/html/CHRG-116hhrg38304.htm

Original source-kind segregation and a positive discriminator are
implemented. So is a finite pair of observationally equivalent
authorisation worlds demonstrating that the published draft cannot
identify API-wide approval. The new source code preserves
the original candidate-source categories without fabricating an
approval/funding/implementation receipt.

The structured case manifest now includes a **seven-question status
ledger** covering the public draft, planning, disputed API approval,
independently reported later coalition activity, 1998 execution,
campaign exposure/impact, and any purported link to Kyoto/Paris
policy outcomes. Distinct time and source identity are mandatory.
The fail-closed validator explicitly rejects a claim that source
presence proves execution or measured impact. The updated Golden
regression and checker import the contested-attribution owner.

**Additional exact empirical frontier:** locate the source-pinned
minutes/approvals for the proposed April 17 meeting, API governance
adoption and funding authorisation; trace any particular plan budget
through realised payments and communications activity; identify
actual participants/recipient audiences and independent pre/post
measurements; supply source review and time-specific PNF equivalence
certificates; assess interference and confounding. A 2017 policy
outcome cannot be assigned to an undocumented 1998 treatment sequence
merely from shared participants and a similar objective.

**Verification:** GitHub source read-back/manifest consistency checks
are not a parallel_checker receipt. The canonical Agda and Python
scripts have not been executed from a full checkout in this assistant
environment, which has no network path to git and no Agda executable.

## 7 November — independent realised communication and measured document coherence

This tranche now goes beyond proposed communications and purely synthetic
epistemic observations, while preserving campaign and target identity:

**Original/archived communication evidence (different historical sources):**

- 1991 Information Council for the Environment media campaign:
  Climate Files documentary index includes original advertising material
  and campaign documentation; this is a separate documented historical
  campaign, NOT execution of the April 1998 API draft.
  https://www.climatefiles.com/climate-change-evidence/weather-denial-documents/
- 1995 Global Climate Coalition public `Climate Change: Your Passport to
  the Facts` handout; archival materials evidence publication and report
  distribution. No downstream persuasion is measured by that fact alone.
  Same archival index.
- GCC science/technical committee 1995–96 draft/meeting records:
  archive synopsis and linked source material describe removal of
  a section dealing with `contrarian theories` from the science primer.
  Distinguish actual editorial document revision from asserted intent
  and downstream effects.
  https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/1996-science-technology-january-february-meetings/
- Original October 9, 1998 Cooler Heads Coalition briefing invitation:
  https://climateinvestigations.org/wp-content/uploads/2017/09/CHPDF.pdf
  This is an ACTUAL dated invitation specifying a session, venue and
  sponsors, not an independently verified attendance or exposure record,
  nor the same authorised event as the April API draft.

**Peer-reviewed measured documents (NOT population persuasion):**

Geoffrey Supran and Naomi Oreskes (2017), `Assessing ExxonMobil’s climate
change communications (1977–2014)`, Environmental Research Letters 12,
084019, DOI 10.1088/1748-9326/aa815f, analyses 187 company communications
and reports 83% peer-reviewed acknowledgements of human-caused warming,
80% internal-document acknowledgement, 12% acknowledgement in public
advertorials and 81% of public advertorials expressing doubt (the
percentages correspond to the study's stated coding/denominator rules;
do NOT fabricate microdata or impose unrelated common denominators).
This is an observed cross-document-type difference under the study's
coding model, not a causal effect of the 1998 draft, not a direct study
of reader belief changes, and not a reconstructed individual motive.
Within 36 advertorials, the 26 taking a position on human-caused warming are the subset: 3/26 acknowledge (rounded 12%) and 21/26 express doubt (rounded 81%). Do NOT use 36 as the denominator for those percentages. The publisher lists a 2020 correction; the corrected coding details
have not been separately reaudited in this tranche.

**New Agda original consumer**
`CCDCOEP3ClimateObservedActivityAndCorpusExact.agda` retains source
families and evidence stage, proves a broad `climate communication` label
does not recover whether evidence is an authored draft or an
independently published communication, and uses the existing
`DiscriminatorSynthesisExact` to identify a positive source-type
observation. It defines a bounded `PublishedCorpusMeasurement` with the
original study's numeric abstract summaries, with
`isHumanTreatmentEffect=false` by construction. This is an
**attributed measured-source record**, not a proved statistical estimate
from underlying respondent data.

**Integration**
`ccdcoe_p3_climate_case_manifest.json` now has four independently
source-qualified historical communication entries plus an actual
published 187-document study entry. The fail-closed validator enforces
different execution identities, publication/invitation status,
study source, study numerals and no fabricated persuasion effect.
Golden cognition, P3 regression and `check_ccdcoe_cognition_agda.sh`
import/check the owner.

**Revised empirical max-cut excluding kernel:**
1. Source-exact event identity and reviewer-approved ITIR/SLR EventPNF for
   a scoped collection of actual activities; original downloads, span
   and content hashes, dates, funders, actors, recipients.
2. Determine whether specific activities authorised/executed the
   April API draft (distinct from the documented 1991, 1995–96 and
   October 1998 materials).
3. If asking about empirical communication **content**, obtain and
   re-score actual microdata or source documents, calibration, coding
   reliability, changing document composition and uncertainty.
4. If asking about human belief or policy **effects**, obtain a
   separate measured exposure/outcome dataset with comparison design,
   selection/confounding, time alignment and interference controls.
5. If asking about central direction or hostile intent, acquire
   independently sourced authorisation/coordination and responsibility
   evidence for the particular organisation/time/action; do not promote
   cross-domain similarities.
6. Held-out transport to other institutions, with local custodianship,
   power/voice and safe source-governance gates preserved.

No new facts above prove the API April 1998 draft was fully
implemented. Real documented campaigns and a peer-reviewed document
analysis nevertheless make the P3 case materially more empirical.

## 7 November — preplan survey and real source-byte ingestion max-cut

The original April 3 1998 draft, published in the April 27 Congressional
Record, describes a Charlton Research survey of **1,100 'informed
Americans'** (printed plan lines 533-549). Under a stated conditional
question about scientists' uncertainty, **58% are reported** as more
likely to oppose Kyoto. The published excerpt does not expose the
original sample weights, questionnaire, randomisation, respondent-level
data or a campaign follow-up. This is evidence of **what the draft
reports about a preplan framing survey**, not an independently confirmed
causal treatment effect or a campaign effectiveness measurement.

The same record specifies **proposed**, not disbursed, amounts:
- $600,000 national media programme, excluding paid advertising;
- $5,000,000 projected data centre over a *different two-year horizon*;
- $300,000 direct outreach;
- $2,000,000 total required through November 1998.

The $5M and $2M have different timeframes: never sum them into a
historical expenditure figure. `CCDCOEP3API1998PrimaryPlanExact.agda`
now owns source-scoped `ReportedPreplanSurvey` and `PlannedAmounts`
records proving the published report is not a measured postcampaign
followup and its proposal is not a payment receipt. The source manifest,
validator and Golden regression reflect those exact distinctions.

**Actual raw-source bridge, rather than a placeholder hash:**
`scripts/build_ccdcoe_p3_primary_intake.py` is an OFFLINE reader that
accepts the original GovInfo HTML bytes obtained through a separately
controlled source acquisition workflow. It computes SHA256 of the
supplied original input, extracts a normalized text surface, requires
six **unique** anchored source phrases, and emits exact normalized
character offsets with six candidate-only, undetermined source claims.
It fails closed on duplicate/missing anchors, unrecognized source
identity and attempted candidate promotion. It emits null semantic
review approvals and no claim that these offsets are raw HTML byte
offsets. A deterministic `--self-test` including negative fixtures
is now included in `check_ccdcoe_cognition_agda.sh`.

Use:

```sh
python3 scripts/build_ccdcoe_p3_primary_intake.py --self-test
python3 scripts/build_ccdcoe_p3_primary_intake.py \
  --source /archive/CREC-1998-04-27-pt1-PgH2323.html \
  --output /archive/ccdcoe-p3-pnf-candidates.json
```

No archive file was fetched into this execution environment; no real
SHA256, normalized original-source offsets or PNF reviewer receipts
are claimed until the command is run against that specific file.

**Current high-alpha remaining original-world cut (excluding Agda):**
(i) obtain archived raw bytes and review the six candidate spans;
(ii) source-identity/authorisation/actual expenditure and event
delivery for the specific April 1998 draft; (iii) independent
pre/post and comparison outcome records with source and question
harmonisation; (iv) exposure/control/selection/interference
identification and uncertainty; (v) externally verified institutional
authority and governance voice. The 1991/1995 independent campaigns,
1998 invitation and the 187-document publication already evidence
some distinct communication and document-level outcomes, but not the
missing causal effect of the 1998 API plan.

## 8 November 2026 — source-exact approval/funding cut and versioned corpus

### Public primary-document conditions that narrow the historical question

The 3 April 1998 action-plan circulation text (Congressional Record,
27 April 1998, H2325; online lines 434–442) proposes review at an April 17
meeting, followed by seeking possible funding. The plan's own
implementation section (H2326, lines 659–664) explicitly conditions
future launch on plan approval, obtaining funding and arranging
resources. These are **preconditions described in the original text**,
not source receipts showing they happened.

`CCDCOEP3EvidenceStageIdentificationExact.agda` proves the
following finite witness chain using the canonical
`IntersectionalNonFactorability` owner:

- a published draft does not identify institutional authorisation;
- authorisation alone does not identify a payment or resource delivery;
- a payment does not by itself identify delivery of specific communications;
- delivered communications do not identify causal audience/policy effects.

The original `DiscriminatorSynthesisExact` experiment bundles now
specify separate approval, funding, delivery and effect evidence queries
for each edge. This is a source-relative **test specification**;
their synthetic alternative worlds are not claimed to be historically
observed. Imported by the Golden Cognition aggregate, P3 regression
and canonical checker.

The case manifest now contains a five-stage evidence ladder, with
`actual_receipt=null` on all stages beyond the original published
draft. Its validator checks the exact original-source conditional
launch spans, all gate statuses, the absence of fabricated receipts,
and four finite source-stage collisions.

### Two further bounded archival leads — not fused into April execution

The Climate Files documentary index locates a **27 February 1998
API climate strategy proposal**, discussing rapid media response,
and a **11 July 1995 Global Climate Coalition communications programme
report and budget for its board**. These are potentially useful for
chronology and comparing a separate realised communications programme,
but the actual original images/document bytes are not available to the
current reviewed PNF intake. Do not equate the February 1998 proposal
or July 1995 GCC report to April 1998 API-plan execution without a
document-identity, authorisation and delivery bridge.

Index: https://www.climatefiles.com/climate-change-evidence/weather-denial-documents/
GCC record: https://www.documentcloud.org/documents/21312427-1995-global-climate-coalition-communications-program-prepared-for-gcc-board-july-11-1995

### 2017 and 2020 Supran–Oreskes have different sampling frames

The published original 2017 ERL source (DOI 10.1088/1748-9326/aa815f)
analysed **187 communications**. Of **36 advertorials**, the selected
**26 that took a position** on warming as real and human-caused included
**3 acknowledgements** and **21 expressions of doubt** (12% and 81%
rounded, respectively). The expanded **2020 addendum**
(DOI 10.1088/1748-9326/ab89d5) screened **1,448** newspaper records,
identified **267** potentially relevant advertorials, and included
**61** adverts expressing a position on the real-and-human-caused
question. These counts have *different selection and search frames*
and cannot be pooled without a document-level crosswalk, coding
revision and denominator accounting.

`CCDCOEP3ClimateObservedActivityAndCorpusExact.agda` now exposes a
distinct `ExpandedAddendumCohort`, with exact 1448/267/61 selected
summary counts and a source-frame distinction. The manifest retains
both `document_analysis_versions`, with
`direct_pooling_authorized=false` and no inferred effect on actual
readers. The Python manifest validator separately checks both studies,
rounding of 3/26 and 21/26, and the no-pooling firewall.

### Real original byte acquisition now implemented

`scripts/build_ccdcoe_p3_primary_intake.py` now has a **pinned**
`--fetch-govinfo` mode. It retrieves only the exact official HTML
page, validates response status/content type/redirect/size, archives
unaltered bytes without overwriting earlier differing versions,
computes source and normalized-text SHA256, locates six distinct
source phrases in the correct order, and emits candidate-only PNF
intake with explicit normalized character offsets. It distinguishes
official-byte acquisition from unverified `--source` files. Its
offline `--self-test` includes missing, duplicate and reordering
negative fixtures. The earlier JSON trailing-newline escape defect
has been repaired.

Use in a network-enabled workspace:

```sh
python3 scripts/build_ccdcoe_p3_primary_intake.py --self-test
python3 scripts/build_ccdcoe_p3_primary_intake.py \
  --fetch-govinfo \
  --archive .cache/ccdcoe-p3/CREC-1998-04-27.html \
  --output .cache/ccdcoe-p3/intake-candidates.json
bash scripts/check_ccdcoe_cognition_agda.sh
```

Raw-source download and actual exact hash **remain unexecuted in this
assistant environment** (no external networking from container).
Candidate source spans still require review and actual ITIR/SLR EventPNF
admission; a hash or GovInfo page identity alone is not semantic
acceptance or proof of historical causal effect.

### Exact remaining primary-world acceptance cut (Agda separately)

P0: Run and review actual pinned GovInfo byte acquisition and PNF
source-span conversion. P1: Find signed April 17 follow-up/adoption and
authorised expenditure for this **same** plan. P2: Trace paid and
actually delivered communications, participants and recipients; avoid
transferring separate GCC/ICE activity. P3: Obtain independent
exposure/outcome microdata and a predeclared estimand; validate source
cohorts and confounding. P4: Establish actor-specific responsibility
and admissible coordination/intent evidence, not guilt by association.
P5: Replicate on separate institutional settings with voice, power and
custodianship controls. No finite theorem can substitute for absent
original receipts.

## 8 November 2026 — source-identity audit, contemporary nonapproval evidence and pre-API measured control

**New decisive documentary finding:** The *New York Times* article by
John H. Cushman Jr., April 26, 1998, is reproduced in the same
Congressional Record entry as the April 3 draft. It reports organiser
Joe Walker describing the plan as tentative with no executives yet
approached for funding, and industry representatives as confirming
that participating organisations had not formally approved it.
These are **contemporaneous attributed statements as of 25–26 April**,
not audited final approval/funding decisions. Source:
https://www.govinfo.gov/content/pkg/CREC-1998-04-27/html/CREC-1998-04-27-pt1-PgH2323.htm

A much later SourceWatch profile quotes Walker's retrospective belief
that this particular project was not funded and did not proceed. The
original correspondence/interview and corroborating final accounting
were not obtained here. Treat the statement as a secondary attributed
claim, not an authentic signed negative receipt. Source:
https://www.sourcewatch.org/index.php?title=Joseph_L._Walker_III

`CCDCOEP3ClimateContestedAttributionExact.agda` now source-writes
`contemporaneousNoApprovalReport` and
`walkerAttributedRetrospective`, with separate exact proof that no
final certified funding or approval receipt is present in the new
representations. The P3 regression imports those precise interfaces.
The manifest and fail-closed validator represent the contemporary
no-approval/no-executive-funder approach, the retrospective attribution,
and the still-missing final accounting as **different** claims.
The best bounded historical statement is **not formally approved
as of the contemporary interviews, with later uncorroborated
nonimplementation testimony**; no causal estimate of the proposed
campaign may be reported.

**Additional real measured opinion evidence, prior to the April plan:**
Krosnick, Visser and Holbrook, *American Opinion on Global Warming:
The Impact of the Fall 1997 Debate*, Resources for the Future,
31 October 1998; original article and later journal version:
https://www.resources.org/archives/american-opinion-on-global-warming-the-impact-of-the-fall-1997-debate/
DOI 10.1088/0963-6625/9/3/303.

Two US national cross-sections sampled 688 adults
(1 Sept–5 Oct 1997) and 725 adults (20 Dec 1997–13 Feb 1998).
The authors report 48→56% recalling relevant news coverage
(+8 percentage points), 54→65% thinking about global warming
a lot/moderately (+11 pp), 28→34% high opinion certainty (+6 pp),
and 4→17 pp strong partisan gap in belief warming occurred
(+13 pp). These are source-published rounded aggregate values
with question/subgroup-specific denominators and unknown
microdata/weights in this application. The second sample closed
**before the 3 April 1998 API draft existed**. It cannot
be used as a treatment response to that draft.

`CCDCOEP3PreAPIOpinionTemporalControlExact.agda` source-writes
these selected actual measurements, both source-specified dates and
sample sizes, exact descriptive percentage-point equalities, and an
existing `IntersectionalNonFactorability` witness against
attributing earlier measured opinion dynamics to a later campaign.
This is a real historical **temporal negative control**, not
synthetic measured people or a post-plan persuasion estimate.
Imported into cognition Golden root, P3 regression and canonical
checker. The manifest and validator check the original sample
sizes/dates/percentages and prohibit the later-plan causal inference.

**Importer issue found by checking the actual public HTML**:
The Congressional commentary (outside the reproduced plan) repeats
the Data Center proposal. Thus a globally unique source-phrase search
would incorrectly reject the official file. The source byte importer
now searches the specific April 3 attached memo and plan starting
from the unique `To: Global Climate Science Team` opening, retains
full-document normalized character coordinates, requires
the April 3 date and correct passage order, and has a negative
fixture containing the duplicated commentary phrase.
No actual original HTML byte digest is claimed absent an
actual network-enabled source acquisition run.

**Remaining decisive max-cut, excluding Agda certification:**

P0 — Run pinned GovInfo acquisition against official source, retain
immutable original bytes, verify extraction and semantic PNF candidates
and actual original source/revision hashes.

P1 — Obtain signed records of what happened **after** the 17 April
meeting: adopted/denied plan, budget vote, funding request/receipt or
documented administrative cancellation. These would test the organiser's
contemporaneous and later accounts.

P2 — If funded/adopted, identify programme-specific disbursement and
actual communication/delivery records. ICE 1991, GCC 1995 and Cooler
Heads 1998 remain distinct pre-existing/parallel activity unless
document identity and authority are proved.

P3 — For a causal claim, obtain plan-specific exposed recipients,
question-harmonised comparable measured outcomes, exposure times,
suitable counterfactual comparison, selection/interference control,
uncertainty and source-grade receipts. The two 1997 survey waves
demonstrate pre-existing public-opinion dynamics but cannot be the
April 1998 plan's effects.

P4 — Replication and transport of the institutional agency, voice,
dissent, positionality and source-authority framework, distinguishing
structural power from individual blame and documented planning from
hostile-intent allegations.

The first-order question is now quite narrow: **did the 1998 plan
receive formal approval or any funding after the contemporary leak?**
The current evidence leans toward no execution but cannot certify
the negative without approval/financial records. Completion of all
factual gates is impossible without acquiring such missing evidence,
and source-written alternatives do not constitute those receipts.

## 8 November 2026 — exact historic financing and causal-status adjudication

### The original document contains a contemporary report of nonapproval

The same Congressional Record that reproduces the 3 April 1998 draft
also reproduces *John H. Cushman Jr., New York Times, 26 April 1998,
"Industrial Group Plans to Battle Climate Treaty"*. Its reporting
attributes two decisive **as-of-publication** facts to the interviews:

- Organiser **Joe Walker** said the document was still tentative,
  and no industry executives had yet been approached to fund it.
- Industry participants confirmed the planning document was genuine,
  but said the participating organisations had **not formally
  approved** it.

These are *contemporary reported actor statements* about the specific
April draft, not a completed company-books inspection, legal
finding or a claim that separate climate-denial activity did not
occur. They strongly constrain the stage as of 25–26 April 1998.

A later SourceWatch profile attributes to Walker the retrospective
belief that the project was never funded and did not proceed; it is a
secondary republication without the original interview transcript or
financial closeout. Retain it as a **nonexecution hypothesis supported
by attributed testimony**, not a settled absence-of-funding fact.

A 20 March 2019 amici brief, *City of Oakland et al v BP et al*,
Ninth Circuit docket 18-16663, PDF page 39 / printed p. 26
(https://climatecasechart.com/wp-content/uploads/case-documents/2019/20190320_docket-18-16663_amicus-brief-4.pdf)
asserts that no organisation was ever formed under the planned
`Global Climate Science Data Center` name. This is a legal
advocacy filing, **not a verified corporate-registry certificate
or judicial finding**. It cannot rule out activity by differently
named groups or automatically prove the whole draft was cancelled.

The original public statement, the organiser's later attributed
belief and the amici assertion are three distinct provenance
objects. Neither retrospective nor litigation-derived claims may
silently upgrade the original contemporary source or constitute a
funding audit. The structured manifest and Python validator now
preserve these distinctions; the original
`CCDCOEP3ClimateContestedAttributionExact.agda` source owner
records the contemporary and retrospective categories, with regression
proofs that final audited receipts remain missing.

### Independent empirical observations occur BEFORE the April draft

Krosnick, Visser and Holbrook published their original fall 1997
national survey waves, N=688 (1 Sept–5 Oct 1997) and N=725
(20 Dec 1997–13 Feb 1998). Real reported descriptive
changes include recalled global-warming news 48%→56%, thinking
a lot/moderately 54%→65%, high opinion certainty 28%→34%, and
strong-party historical-warming belief gap 4pp→17pp. Both waves
*pre-date* the API plan. Their differences give genuine evidence of
pre-existing climate opinion and polarisation but are logically
incapable of measuring the effect of a proposed April 1998
campaign. Original source: RFF `American Opinion on Global Warming:
The Impact of the Fall 1997 Debate`,
https://www.resources.org/archives/american-opinion-on-global-warming-the-impact-of-the-fall-1997-debate/.

`CCDCOEP3PreAPIOpinionTemporalControlExact.agda` is now
source-written, directly imported in Cognition Everything/Golden and
cross-checked in the P3 regression. Its selected actual percentages
and sample dates are kept distinct from synthetic
`laterPlanHasIndependentEstablishedImpact` counterexample worlds.
The manifest validator forbids attributing the 1997 measurements
to the 1998 draft or inventing respondent microdata.

### Exact source-text ingestion defect repaired

The official 27 April 1998 Congressional Record HTML contains
a duplicate mention of the proposed science data centre in
congressional commentary **before** the attached 3 April memo.
An importer requiring global string uniqueness would incorrectly
reject this genuine record. The intake parser now isolates the
attached memo beginning `To: Global Climate Science Team`, requires
the original April 3 date, searches ordered candidate anchors only
inside that original memo context, and reports full-document
normalised-text offset coordinates. A negative/positive fixture
intentionally includes the earlier duplicate commentary reference.
These candidate source offsets are not misrepresented as original
HTML byte or canonical ITIR parser tokens.

### Actual closure status

- **Primary draft + contemporary nonapproval report**: source
  publicly located, bounded claim and provenance interfaces written.
- **Independent 1997 national public opinion response**: real
  published descriptive measurements source-written, correctly
  excluded from the later-plan causal estimand.
- **Independent 1991/1995/1998 communications + 2017/2020 coded
  documents**: separate source records; no automatic April plan
  execution identity or audience-effect pooling.
- **April 1998 specific-plan formal approval, direct payments,
  delivered interventions and postcampaign outcomes**: not found
  in the reviewed available sources; final verdict cannot be
  authenticated without original organisational/financial archives.
- **GovInfo original raw bytes**: official page accessible through
  the public text source; container source download failed
  (network/DNS unavailable). Source-hash receipt and source-specific
  PNF admission remain unavailable, not fabricated.
- **Python/Agda exact-head acceptance**: no executable full-checkout
  receipts in this session; GitHub read-back and structural checks
  are strictly weaker.

The high-alpha remaining empirical test is now **a positive same-plan
authorisation/funding record or reliable final negative accounting**,
followed by actual exposure/outcome data *only if* implementation
was established. If it was cancelled, the correct endpoint is
a supported **nonimplementation determination**, not a manufactured
causal campaign-effect estimate.

## 8 November 2026 — bounded case disposition from direct former-API executive testimony

A newly identified **first-person published interview**, not merely a
secondary paraphrase, materially narrows the 1998 April-plan frontier:

- **Russell Cook**, "Interview with William O'Keefe, former American
  Petroleum Institute executive", GelbspanFiles, **20 April 2021**,
  https://gelbspanfiles.com/?p=11851, lines 20–50.
- The named interviewee, former API executive VP/COO **William O'Keefe**,
  says (i) the **specific proposed communications plan** was never
  funded or implemented, (ii) API hosted/chaired a brainstorming
  workshop involving several organisations, which **Joe Walker did
  not convene entirely on his own**, and (iii) he contests the
  original attribution of a 1998 `Living on Earth` response. He
  says the resulting document was not an adopted API/Exxon policy.
- The interview's publisher and interviewer adopt a sympathetic
  position toward industry climate-policy arguments. The speaker is
  an interested former executive. His answers are **direct named
  participant testimony as printed**, not independent financial
  records, authenticated audio, a company vote, or judicial fact
  findings. Do not promote the speaker's other scientific claims
  into empirical climate-science conclusions or infer the absence
  of broader organised climate lobbying.
- This source is in substantive agreement with the contemporaneous
  April 1998 NYT record: no solicited executive funders and no
  formal approval *as of those interviews*. Walker's later
  SourceWatch-reproduced recollection also states the project did
  not proceed, but retains a weaker chain of attribution.

**New evidence type:** `direct_former_executive_interview` in
`ccdcoe_p3_climate_case_manifest.json` has four independently
scoped source claims, original interview date/locator/line ranges,
the dispute with the 1998 radio account, and null original audio,
company financial closeout and independent implementation audit.
`CCDCOEP3ClimateContestedAttributionExact.agda` and its P3
Golden regression retain the direct published assertions, real
multi-organisation planning and missing accounting independently.
The manifest validator checks this source type and refuses to
promote financial certification.

**Selected case disposition:** the April 1998 **specific** plan is
*historically supported as probably not formally funded or
implemented* based on contemporary status plus two named
participant accounts, **without a complete independent
financial/cancellation audit**. The planning meeting and draft
were real. This is not a determination that all industry
climate-communications ceased, nor a zero causal effect from
other campaigns.

**Next decisive proof-of-fact gate:** signed April 17 follow-up
minutes and decision, program-specific company accounts and
transfers, a documented cancellation/nonadoption or an actual
same-plan delivery trail. Until such evidence is obtained,
a causal-treatment study **of the alleged implemented April
draft** is not an admissible identified estimand. Independent
campaigns and real survey/document-content observations remain
separate scientifically viable study units.

**Importer:** The pinned GovInfo HTML source still lacks an
official raw-byte digest in the repository because container
networking cannot resolve the source host. The memo-scoped
source-offset extractor has its necessary duplicate-commentary
repair but still requires running on authentic fetched bytes,
followed by source-to-PNF semantic review.

**Verification boundary:** source read-back can establish that
these claims, proof statements and validators were written.
Neither Agda kernel nor checked-out Python runtime receipts
are claimed here. A named interview is not a company audit.
