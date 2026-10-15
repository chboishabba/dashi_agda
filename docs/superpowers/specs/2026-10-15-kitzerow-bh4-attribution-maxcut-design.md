# Kitzerow BH4 / autism convergence, priority, and attribution max-cut — design

Date: 2026-10-15

Status: reviewed design target; implementation has not yet begun.

## Intent

Formalise Kimberly Kitzerow's Autism and the Comorbidities / BH4-shunt architecture as a **candidate empirical causal graph** and acquire the later studies she identifies as convergent evidence, while keeping three logically distinct questions separate:

1. **Scientific support** — does a source support, qualify, conflict with, or underdetermine a bounded node/edge claim?
2. **Priority / chronology** — did the Kitzerow articulation or a comparison source exist first for the specific claim being compared?
3. **Exposure / attribution** — is there a provenance-bearing record of contact, citation, access, notice, institutional response, or only public availability / originator report?

The implementation must never infer plagiarism, copying, derivation, independent replication, whole-model confirmation, clinical validity, or legal infringement from structural overlap alone.

## User constraints carried into the design

- Acquire external sources Pareto-first: primary paper / preprint / DOI / official institutional record before commentary.
- Preserve attribution and priority explicitly.
- Reuse existing Chemistry / Biology / Brain / reasoning machinery; do not create a parallel systems-biology framework.
- Complete the formal max-cut: typed graph, source atlas, bounded evidence receipts, chronology/exposure receipts, experimental discriminators, promotion firewalls, rollup, and regression/static checks.
- Claims of direct contact or institutional awareness require a concrete receipt. Public self-report or screenshot is represented as such and is **not** silently upgraded to independently verified institutional fact.

## Current external acquisition findings

### Kitzerow primary work

Publicly indexed records currently identify at least:

- Kimberly Kitzerow, *Autism & the Comorbidities Along the BH4 Pathway* (Jan 2024), DOI 10.13140/RG.2.2.23124.37761/1.
- Kimberly Kitzerow, *The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism and Systemic Comorbidities* (Aug 2024), DOI 10.13140/RG.2.2.18927.96167.
- Kimberly Kitzerow, *Neurodivergent Biochemistry and the Autism and the Comorbidities Theory* (Jul 2025), DOI 10.13140/RG.2.2.30248.89606.
- Kitzerow's public timeline reports earlier 2023 public articulations of the BH4 shunt / CSTL / autism-comorbidity architecture. Those timeline rows are source claims until the underlying timestamped artifact is acquired.

Primary public index:
https://coral-emu-hp9t.squarespace.com/researchgate-papers
ResearchGate profile:
https://www.researchgate.net/profile/Kimberly-Kitzerow

### Comparison studies already acquired at sufficient identity level

- Nomura et al., *ESC models of autism with copy-number variations reveal cell-type-specific translational vulnerability*, Cell Genomics 5(6):100877 (2025), DOI 10.1016/j.xgen.2025.100877. Public preprint chronology reported by Kitzerow's attribution page as 2022; this predates her later articulation of the shared genetic stress response, so it is an important **independence-supporting control**, not a plagiarism example.
- Jang / Takahashi / Huguenard et al., *Reticular thalamic hyperexcitability drives autism spectrum disorder behaviors in the Cntnap2 model of autism*, Science Advances (2025), PMID 40834072. Kitzerow publicly reports Stanford Neurodiversity Project contact on 2023-11-27 requesting model information. Until the email artifact is acquired, represent this as `originatorReportedDirectContact`, not `independentlyVerifiedDirectContact`.
- Litman et al., *Decomposition of phenotypic heterogeneity in autism reveals underlying genetic programs*, Nature Genetics 57:1611-1619 (2025), DOI 10.1038/s41588-025-02224-z. No Kitzerow reference was found in the accessible Nature page text.
- Colpani Filho et al., *Tetrahydrobiopterin and Autism Spectrum Disorder: A Systematic Review of a Promising Therapeutic Pathway*, Brain Sciences 15(2):151 (2025), DOI 10.3390/brainsci15020151. Kitzerow alleges later journal/author contact; this must remain a provenance claim unless the correspondence/official response is acquired.
- 2026 NO -> TSC2 -> mTOR Molecular Psychiatry study identified in the prior acquisition pass as a strong bounded internal-edge test; it does not by itself establish the upstream BH4-shunt edge.
- 2026 connectivity-subtype work and the 2026 Melillo/Leisman/Alfasi neuroimmune cascade are structurally relevant comparison objects; their role must be typed separately from direct experimental testing.
- IACC July 2026 developmental-systems material is an institutional framework / strategy source, not biological experimental confirmation. Kitzerow publicly reports a 2024 MedMaps contact pathway into IACC; represent this as originator-reported exposure until the contact record is acquired.

Kitzerow attribution/timeline pages used for discovery only:
https://www.kimberlyedu.org/kitzerow-documented-timeline
https://www.kimberlyedu.org/stanford-z944-treatment-study-kitzerow-attribution-rubric
https://www.kimberlyedu.org/japan-genetic-stress-autism-study-kitzerow-attribution-rubric
https://www.kimberlyedu.org/italy-functional-connectivity-subtypes-kitzerow-attribution-rubric
https://www.kimberlyedu.org/dr-melillo-neuroimmune-cascade-kitzerow-attribution-rubric
https://www.kimberlyedu.org/brazil-autism-and-the-comorbidities-along-the-bh4-pathway-kitzerow-attribution-rubric
https://www.kimberlyedu.org/iacc-integrated-developmental-systems-autism-pathology-framework-kitzerow-attribution-rubric

## Existing repo owners to reuse

### Source / attribution

- `DASHI/Core/AttributedSourceCore.agda`
  - canonical author/title/publication/DOI/URL/source-kind carrier;
  - explicitly non-promoting.

### Evidence dependence / replication

- `DASHI/Biology/DrosophilaSameTrialProvenanceDependenceExact.agda`
  - same-root versus independent replication distinction;
  - `independenceUndetermined` boundary is directly reusable as a semantic pattern.

### Allostasis and systems state

- `DASHI/Biology/AllostaticBodyStateExact.agda`
  - multisystem allostatic vector;
  - proves one projection does not determine complete allostatic state.
- `DASHI/Biology/Cell/CellStateAttractor.agda`
  - genome/chromatin/RNA/proteome/metabolism/membrane/environment/history coupled state;
  - molecular/regulatory stress -> cell-state bridge;
  - exact anti-collapse boundaries.

### Neurochemical / clinical promotion firewall

- `DASHI/Promotion/NeurochemicalAuthorityBoundary.agda`
  - blocks kinetics, mechanism, intervention, clinical, biomarker, and brain-state promotion without the appropriate authority receipts.

### Claim audit / experimental backprop

- `DASHI/Biology/ACPUEAEROClaimAuditProtocolExact.agda`
  - citation-by-citation PNF audit pattern.
- `DASHI/Reasoning/ExperimentalAssertionPNFImplicationConeExact.agda`
- `DASHI/Reasoning/BlockedImplicationExperimentBackpropExact.agda`
  - convert an unresolved implication edge into a missing experimental-design slot rather than inferring it from coarse overlap.

### Pareto acquisition / discovery

- `DASHI/Core/SnowballPluralLensDiscoveryAdmissionExact.agda`
- existing digital-ESD Pareto acquisition notes/scripts
  - candidate discovery does not create inclusion or authority;
  - experimental design and failed-factorisation are explicit discovery routes.

### Evidence relation vocabulary

Existing domain owners already demonstrate bounded relation types such as `supports`, `qualifies`, `conflictsWith`, `underdetermines` and assay-specific evidence relations. This implementation will **not** add another global evidence relation core merely to rename them. The Kitzerow owner will define only the additional relation granularity needed for this empirical graph and will map it to existing promotion semantics.

## Architecture

### 1. Candidate graph owner

New file:
`DASHI/Biology/KitzerowBH4CascadeExact.agda`

Represent the model as claims, not truths.

Core node families:

- upstream context: genetic, epigenetic, situational / biological demand;
- chronic allostasis;
- GCH1 / redox-regulated BH4 allocation;
- AAAH branch: TPH / PAH / TH, precursor allocation, monoamine / glutamate implications, E/I / CSTL candidate edge;
- NOS branch: NOS coupling/uncoupling, redox-sensitive protein regulation, mTOR / MMP / ACE / MTR candidate subedges, neural/systemic traits;
- AGMO branch: ether-lipid catabolism / lipid reorganisation, endocannabinoid signalling, social-regulatory traits;
- trait/comorbidity clustering;
- prolonged allostatic overload / chronic progressive conditions.

Every graph edge carries an `EdgeStatus` such as:

- `kitzerowProposed`
- `priorBiologyInherited`
- `boundedEmpiricalSupport`
- `directInterventionalSupport`
- `qualifiedSupport`
- `conflictingEvidence`
- `underDetermined`
- `unpaid`

No edge constructor is named `confirmed` unless the direct same-edge, same-context evidentiary conditions are paid.

### 2. Primary source atlas

New file:
`DASHI/Biology/KitzerowBH4SourceAtlasExact.agda`

Use `DASHI.Core.AttributedSourceCore`.

Separate lists:

- Kitzerow primary works;
- pre-Kitzerow BH4 / GCH1 / NOS / AAAH / AGMO / allostasis prior art;
- post-articulation experimental studies;
- later review / systems-model sources;
- institutional / policy sources;
- provenance/contact artifacts.

Each source relationship string must state what the source pays and an exclusion boundary.

### 3. Claim-to-source evidence receipts

New file:
`DASHI/Biology/KitzerowBH4ConvergentEvidenceExact.agda`

A receipt contains:

- graph edge / node under test;
- source identity;
- organism / population;
- tissue / cell type / brain region;
- genotype / exposure context;
- assay class;
- observational versus interventional design;
- direction of result;
- evidence relation;
- whether it tests the exact Kitzerow edge or only a downstream/adjacent projection;
- whether whole-model confirmation is claimed (must be false for current acquired studies).

Required canonical receipts include at minimum:

- BH4 ASD systematic review -> BH4-pathway relevance (review-level bounded support, not central-shunt proof);
- NO -> TSC2 S-nitrosylation/degradation -> mTOR dysregulation -> direct bounded mechanistic support for the NOS/mTOR internal edge;
- reticular-thalamic excitability intervention -> direct circuit-level support for a CSTL/E-I downstream node, upstream BH4 provenance unpaid;
- Nomura translational/NMD common vulnerabilities -> convergence on regulatory/translation state with chronology explicitly supporting independence;
- molecular / connectivity subtype studies -> support for context-sensitive/opposed state geometry, not single BH4 causal identification;
- Melillo neuroimmune cascade -> structural/model convergence, not experimental replication;
- IACC framework -> institutional conceptual convergence only.

### 4. Priority / contact / attribution owner

New file:
`DASHI/Biology/KitzerowPriorityAttributionExact.agda`

Do **not** encode a scalar plagiarism score as truth.

Types:

`ChronologyRelation`
- `kitzerowClearlyEarlier`
- `comparisonClearlyEarlier`
- `samePeriodUnresolved`
- `startDateUnknown`

`ExposureEvidence`
- `noExposureEvidenceFound`
- `publicAvailabilityOnly`
- `originatorReportedContact`
- `publicContactArtifactInspected`
- `institutionalAcknowledgementInspected`
- `directCitationInPaper`
- `citationAbsentInInspectedText`
- `exposureUndetermined`

`DerivationStatus`
- `independentDerivationSupported`
- `derivationUndetermined`
- `directUseDocumented`

`directUseDocumented` requires a direct provenance receipt; structural similarity is insufficient.

Canonical examples:

- Japan / Nomura: `comparisonClearlyEarlier` + no exposure path => `independentDerivationSupported` for the relevant shared-stress/translation claim.
- Stanford: Kitzerow earlier for the particular public CSTL/E-I articulation; contact currently stays `originatorReportedContact` unless the email artifact itself is acquired.
- Brazil review: chronology and post-publication contact allegations retained as separate fields; no derivation conclusion without the underlying correspondence / preregistration / manuscript-history evidence.
- Italy: structural convergence + public availability but no direct contact currently found => `derivationUndetermined`.
- Melillo: structural sequence comparison; public exposure possible; derivation remains undetermined absent a provenance bridge.
- IACC: originator-reported MedMaps / IACC awareness separated from the institutional document itself.

Firewalls:

- earlier publication != proof of copying;
- contact != proof of use;
- public availability != access;
- access != derivation;
- derivation != copyright infringement;
- scientific support != priority;
- priority != scientific correctness;
- absence of citation != plagiarism by definition;
- overlap score != legal conclusion.

### 5. Same-object prior-art subtraction

New file:
`DASHI/Biology/KitzerowBH4PriorArtSubtractionExact.agda`

For each comparison, partition overlap into:

- inherited prior biology;
- distinctive Kitzerow arrangement / prediction already public by the comparison date;
- later newly measured edge;
- unresolved common-source possibility.

This prevents crediting old BH4/NOS/mTOR/allostasis facts to Kitzerow while still allowing priority claims about a specific ordered synthesis to be represented.

### 6. Experimental discriminator / falsification frontier

New file:
`DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda`

Backpropagate the central unresolved hypothesis:

`chronic allostatic demand -> redox/GCH1-mediated BH4 resource reallocation -> coordinated AAAH/NOS/AGMO branch shifts -> downstream phenotype`

into explicit experiment slots.

Highest-value discriminators:

1. Same-system longitudinal BH4/GCH1/redox state with simultaneous AAAH, NOS and AGMO branch readouts.
2. Perturb BH4/GCH1/redox allocation while measuring whether the predicted branch trade-off occurs.
3. Rescue / reversal test separating BH4-centred mediation from parallel genotype-specific mTOR, immune, or circuit routes.
4. Context stratification: genotype, developmental stage, sex, cell type / brain region.
5. Pre-registered graph comparison between Kitzerow architecture and plausible competing DAGs.

Formal output is an experiment requirement, not a claim that the experiment has occurred.

### 7. Pareto acquisition frontier

New file:
`DASHI/Biology/KitzerowBH4AcquisitionParetoExact.agda`

Axes remain non-scalar:

- source primacy;
- chronology resolution;
- contact/exposure provenance;
- mechanistic specificity;
- experimental causal strength;
- context match;
- attribution relevance.

Do not scalarise into a single truth/plagiarism score.

Highest-yield unpaid acquisitions:

- underlying timestamped 2023 Kitzerow artifacts for each distinctive claimed edge;
- the Stanford 2023 contact artifact and exact sender/institution provenance;
- any paper that actually cites Kitzerow directly;
- MDPI / Latini correspondence or journal response supporting the Brazil exposure chronology;
- MedMaps/IACC contact artifact;
- manuscript preprints / received dates / protocol registrations for comparison papers;
- full reference lists where current accessible pages were insufficient.

### 8. Rollup and validation

New focused rollup:
`DASHI/Biology/KitzerowBH4Everything.agda`

Regression / static contract:
`DASHI/Biology/KitzerowBH4MaxCutValidation.agda`

Script:
`scripts/check_kitzerow_bh4_maxcut.py`

The validation contract must assert, at minimum:

- every source receipt is non-promoting by citation alone;
- no current canonical comparison receipt promotes whole-model confirmation;
- Japan is represented as an independence-supporting chronology control;
- Stanford contact is not promoted beyond the acquired evidence class;
- no plagiarism/legal-infringement conclusion exists without direct-use provenance;
- scientific-support, priority, and exposure projections are separately accessible;
- the central BH4 resource-allocation edge remains experimentally open unless paid by a direct discriminator;
- existing allostasis / cell-state / neurochemical-promotion owners are imported rather than reimplemented.

Import the focused rollup into `DASHI/Biology/Everything.agda` only after the focused validation owner exists.

## Testing workflow

TDD order:

1. Add validation owner / static check expectations first and record RED because production owners do not yet exist.
2. Add candidate graph + source atlas.
3. Add evidence receipts.
4. Add priority/attribution owner and direct-use firewall.
5. Add prior-art subtraction and experimental discriminator.
6. Add Pareto frontier.
7. Add focused rollup and Biology import.
8. Run static checker and Agda kernel checks where executable access exists.
9. If Agda executable is unavailable, report that explicitly; do not claim kernel-green.

## Max-cut stopping condition

The formal max-cut is exhausted when the repo can answer, for each acquired source:

- what exact Kitzerow node/edge it bears on;
- what the source actually measured;
- whether that is observational, interventional, review, model, or institutional evidence;
- whether the Kitzerow claim predates it;
- whether an exposure/contact/citation path is documented and at what evidence grade;
- what prior biology must be subtracted before a novelty/priority comparison;
- what stronger claim remains blocked;
- what experiment or provenance artifact would pay that blocker.

Anything beyond that requires **new same-object evidence**, especially the underlying contact artifacts, manuscript-history records, or direct BH4-allocation experiments. More abstractions without paying those leaves do not count as progress.
