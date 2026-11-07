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
The publisher lists a 2020 correction; the corrected coding details
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
