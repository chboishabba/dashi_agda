module DASHI.Education.DigitalESDStudyEvidencePNFExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDStudyClaimPilotExact as Pilot
import DASHI.Education.DigitalESDStudyClaimPilotExtensionExact as ExtPilot
import DASHI.Education.DigitalESDInstitutionalEvaluationPilotExact as Institutional
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.AristotleExperimentalProofSearchExact as ProofSearch

proofSearchBoundary : ProofSearch.AristotleExperimentalProofSearchBoundary
proofSearchBoundary = ProofSearch.canonicalAristotleExperimentalProofSearchBoundary

record StudyEvidencePNFAudit : Set where
  constructor study-evidence-pnf-audit
  field
    studyKey : String
    profile : Ceiling.StudyClaimProfile
    assertion : PNF.PredicateNormalAssertion
    evidenceReceipt : String
    uncertaintySemantics : String
    nextConsumerQuestion : String
    proofSearchResidual : String

open StudyEvidencePNFAudit public

------------------------------------------------------------------------
-- Ardila et al. 2025: qualitative implementation/process evidence.
------------------------------------------------------------------------

ardilaScope : PNF.AssertionScope
ardilaScope = PNF.assertionScope
  "two five-member postgraduate student design teams"
  "one London-based postgraduate Education and Technology module"
  "ten-week design-thinking process with sustainability challenges and co-design/test activity"
  "two descriptive team/case trajectories; no causal control group"
  "observed/interpretive GreenComp-relevant sustainability-competence processes"
  "ten-week Spring 2023 module"

ardilaPredicates : List PNF.PredicateAtom
ardilaPredicates =
  PNF.predicateAtom "analytic-team" PNF.populationPredicate "student-designer × team"
    "the primary analytic carrier is the ten HE student designers, not every child who participated in co-design activities"
  ∷ PNF.predicateAtom "design-thinking-context" PNF.contextPredicate "team × module × challenge"
    "observations are situated in the declared ten-week postgraduate module and sustainability-design challenges"
  ∷ PNF.predicateAtom "co-design-process" PNF.interventionPredicate "team × design-practice"
    "students engage in iterative design-thinking/co-design practices during the module"
  ∷ PNF.predicateAtom "process-observation" PNF.outcomePredicate "design-practice × competence-expression"
    "field notes, artefacts and reflections support observations about practices through which sustainability competencies appeared to emerge or be hindered"
  ∷ PNF.predicateAtom "bounded-case" PNF.transportPredicate "case-context × target-context"
    "two-team case evidence does not establish prevalence or universal transfer"
  ∷ []

ardilaImplementationAssertion : PNF.PredicateNormalAssertion
ardilaImplementationAssertion = PNF.predicateNormalAssertion
  "ardila-2025-design-process-implementation"
  "In the two analysed postgraduate design teams, the documented design-thinking process exhibited context-specific practices through which sustainability competencies appeared to emerge or be hindered."
  PNF.studyPopulationQ
  PNF.descriptiveF
  ardilaScope
  ardilaPredicates
  "same-object DOI 10.3390/su17104289; qualitative case-study extraction"

ardilaAudit : StudyEvidencePNFAudit
ardilaAudit = study-evidence-pnf-audit
  "ardila-2025-designing-digital-education-futures"
  Pilot.ardilaPilotProfile
  ardilaImplementationAssertion
  "n=10 HE student designers in two teams; 60 Year-5 children and two child advisors have distinct co-design roles and are not collapsed into the analytic n"
  "no CI or population effect size applies to the qualitative process claim; absence of CI is not evidence weakness for this question"
  "which specific design-process feature discriminates contexts where sustainability competencies are supported versus hindered?"
  "next proof-search step is a context/mechanism discriminator, not a request for a larger p-value"

------------------------------------------------------------------------
-- Gouseti & Shaw 2026: situated platformisation experience.
------------------------------------------------------------------------

gousetiScope : PNF.AssertionScope
gousetiScope = PNF.assertionScope
  "71 leaders, teachers, students and parents"
  "two English secondary schools"
  "existing school platformisation practices"
  "contextual contrast between two differently platformised schools"
  "reported experiences of communication, monitoring, exclusion, surveillance and teacher digital wellbeing"
  "fieldwork across two 2024 collection windows"

gousetiPredicates : List PNF.PredicateAtom
gousetiPredicates =
  PNF.predicateAtom "stakeholder-account" PNF.populationPredicate "participant × school-role"
    "participants provide situated accounts from distinct school roles"
  ∷ PNF.predicateAtom "platformised-context" PNF.contextPredicate "school × platform-practice"
    "accounts are embedded in the two schools' specific platform infrastructures and routines"
  ∷ PNF.predicateAtom "experienced-benefit-burden" PNF.outcomePredicate "participant × platform-experience"
    "themes include administrative/pedagogical benefits together with surveillance, exclusion and wellbeing burdens"
  ∷ PNF.predicateAtom "analytical-transfer-only" PNF.transportPredicate "two-school-context × wider-population"
    "qualitative analytical relevance is not statistical prevalence or universal transport"
  ∷ []

gousetiExperienceAssertion : PNF.PredicateNormalAssertion
gousetiExperienceAssertion = PNF.predicateNormalAssertion
  "gouseti-shaw-2026-platformisation-experience"
  "Across the two studied schools, participants described platformisation as producing both practical benefits and context-specific burdens including monitoring, exclusion and teacher digital-wellbeing concerns."
  PNF.studyPopulationQ
  PNF.descriptiveF
  gousetiScope
  gousetiPredicates
  "same-object DOI 10.1080/17439884.2026.2653746; reflexive thematic-analysis extraction"

gousetiAudit : StudyEvidencePNFAudit
gousetiAudit = study-evidence-pnf-audit
  "gouseti-shaw-2026-platformisation"
  Pilot.gousetiPilotProfile
  gousetiExperienceAssertion
  "n=71: 4 senior leaders, 21 teachers, 36 students and 10 parents across two schools"
  "no participant-effect CI applies to reflexive thematic themes; uncertainty is interpretive/contextual rather than a sampling interval"
  "which platform/governance/context coordinates explain why similar services produce different experienced burdens across settings?"
  "next probe should separate power/governance/context hypotheses rather than infer prevalence from qualitative counts"

------------------------------------------------------------------------
-- Martinez Garcia et al. 2026: review-level synthesis.
------------------------------------------------------------------------

martinezScope : PNF.AssertionScope
martinezScope = PNF.assertionScope
  "33 included empirical studies"
  "face-to-face compulsory schooling, 2012-June 2025"
  "heterogeneous digital-education interventions/practices represented in the included studies"
  "study-level PICOS comparisons where present; no single pooled comparator"
  "review-level patterns in digital-education definitions, outcomes and implementation conditions"
  "review search window January 2012-June 2025"

martinezPredicates : List PNF.PredicateAtom
martinezPredicates =
  PNF.predicateAtom "included-study" PNF.populationPredicate "study × review-corpus"
    "the review synthesis is over 33 included studies rather than one participant experiment"
  ∷ PNF.predicateAtom "heterogeneous-designs" PNF.contextPredicate "study × design × outcome"
    "included studies differ in design, stage, technology, duration and reported outcome"
  ∷ PNF.predicateAtom "conditional-benefit-pattern" PNF.outcomePredicate "review-corpus × implementation-condition"
    "reported benefits are synthesized as conditional on pedagogy, teacher mediation, infrastructure/policy and equitable access"
  ∷ PNF.predicateAtom "no-pooled-effect" PNF.significancePredicate "review-corpus × meta-analysis"
    "heterogeneity prevents promotion to one pooled educational effect estimate"
  ∷ []

martinezReviewAssertion : PNF.PredicateNormalAssertion
martinezReviewAssertion = PNF.predicateNormalAssertion
  "martinez-2026-review-conditional-patterns"
  "Across the 33 included studies, the review synthesised digital-education benefits as conditional on pedagogical intentionality, teacher mediation, coherent infrastructure/policy and equitable access rather than as one pooled intervention effect."
  PNF.studyPopulationQ
  PNF.descriptiveF
  martinezScope
  martinezPredicates
  "same-object DOI 10.3390/su18157979; PRISMA/MMAT/PICOS review extraction"

martinezAudit : StudyEvidencePNFAudit
martinezAudit = study-evidence-pnf-audit
  "martinez-garcia-2026-systematic-review"
  Pilot.martinezPilotProfile
  martinezReviewAssertion
  "33 included studies; 502,701 participants reported across those underlying studies; Cohen's kappa=.81 applies to reviewer agreement"
  "no pooled educational-effect CI/meta-analytic interval is reported; kappa=.81 is not an intervention-effect uncertainty measure"
  "which included primary-study predicates actually support or defeat each candidate digital-ESD principle under our own claim ceilings?"
  "the review can seed primary-source acquisition but cannot pay this manuscript's database execution or replace source-level extraction"

------------------------------------------------------------------------
-- Böhme 2026: conceptual framework / prior-art proposition.
------------------------------------------------------------------------

boehmeScope : PNF.AssertionScope
boehmeScope = PNF.assertionScope
  "conceptual literature/discourse rather than a participant population"
  "German/Austrian/Swiss education and digitality/sustainability discourse"
  "conceptual coupling of sustainability/ESD and digitality"
  "not applicable"
  "conceptual twin-transformation / digitainability framework"
  "publication-level conceptual horizon"

boehmePredicates : List PNF.PredicateAtom
boehmePredicates =
  PNF.predicateAtom "digitality-sustainability-coupling" PNF.contextPredicate "digitality × sustainability"
    "the framework treats digitality and sustainability as mutually conditioning transformation domains"
  ∷ PNF.predicateAtom "conceptual-antecedent" PNF.outcomePredicate "framework × manuscript-positioning"
    "the source supplies prior-art vocabulary/structure rather than empirical intervention evidence"
  ∷ PNF.predicateAtom "no-empirical-promotion" PNF.transportPredicate "conceptual-framework × empirical-effect"
    "conceptual coherence does not create participant effects, lifecycle measurements or population transport"
  ∷ []

boehmeFrameworkAssertion : PNF.PredicateNormalAssertion
boehmeFrameworkAssertion = PNF.predicateNormalAssertion
  "boehme-2026-coupled-twin-transformation"
  "The conceptual framework treats sustainability/ESD and digitality as a mutually coupled twin transformation rather than independent educational agendas."
  PNF.existentialQ
  PNF.descriptiveF
  boehmeScope
  boehmePredicates
  "same-object DOI 10.3390/educsci16050721; conceptual prior-art extraction"

boehmeAudit : StudyEvidencePNFAudit
boehmeAudit = study-evidence-pnf-audit
  "boehme-2026-digitainability-framework"
  Pilot.boehmePilotProfile
  boehmeFrameworkAssertion
  "conceptual-framework source; no empirical participant n or intervention estimate applies"
  "CI/effect-size coordinates are not applicable to the conceptual claim and are not represented as missing trial reporting"
  "which empirical or institutional observations would operationally discriminate a coupled-transformation claim from rhetorical co-location?"
  "next proof-search step is operationalisation/measurement, not statistical inference over a nonexistent sample"

------------------------------------------------------------------------
-- Pinzone, Sarti & Amodeo 2026: scenario LCA with model uncertainty.
------------------------------------------------------------------------

pinzoneScope : PNF.AssertionScope
pinzoneScope = PNF.assertionScope
  "modelled educational scenarios under one declared functional unit"
  "Italian university / Politecnico di Milano assumptions"
  "face-to-face, hybrid and fully online synchronous/asynchronous delivery scenarios"
  "scenario-to-scenario comparison under the same functional-unit model"
  "ReCiPe 2016 Midpoint environmental-impact outputs including global warming"
  "functional-unit scenario model, not longitudinal educational follow-up"

pinzonePredicates : List PNF.PredicateAtom
pinzonePredicates =
  PNF.predicateAtom "functional-unit" PNF.populationPredicate "scenario × 25-hours-education-per-student"
    "each modelled scenario is evaluated for the declared functional unit of 25 hours education per student"
  ∷ PNF.predicateAtom "scenario-delivery-mode" PNF.interventionPredicate "delivery-mode × inventory"
    "delivery-mode assumptions determine transport/ICT/energy inventory inputs"
  ∷ PNF.predicateAtom "common-model-comparator" PNF.comparatorPredicate "scenario × scenario × functional-unit"
    "face-to-face, hybrid and online scenarios are compared within one model architecture"
  ∷ PNF.predicateAtom "global-warming-output" PNF.outcomePredicate "scenario × kg-CO2eq"
    "example outputs include 17.2 kg CO2eq face-to-face and 5.88 kg CO2eq fully online asynchronous per functional unit"
  ∷ PNF.predicateAtom "model-uncertainty" PNF.significancePredicate "parameter-distribution × impact-output"
    "Monte Carlo analysis supplies 95% model uncertainty intervals; hybrid scenarios are more parameter-sensitive"
  ∷ PNF.predicateAtom "boundary-assumption" PNF.contextPredicate "inventory-boundary × omitted-process"
    "results depend on transport, attendance, ICT and energy assumptions; disposal is excluded for insufficient data"
  ∷ []

pinzoneScenarioAssertion : PNF.PredicateNormalAssertion
pinzoneScenarioAssertion = PNF.predicateNormalAssertion
  "pinzone-2026-scenario-lca-comparison"
  "Under the declared LCA functional unit and model assumptions, the modelled online scenarios have lower reported global-warming outputs than the face-to-face scenario, with scenario-specific Monte Carlo uncertainty."
  PNF.boundedUniversalQ
  PNF.comparativeF
  pinzoneScope
  pinzonePredicates
  "same-object DOI 10.1007/s11367-026-02656-7; corrected publisher attribution retained"

pinzoneAudit : StudyEvidencePNFAudit
pinzoneAudit = study-evidence-pnf-audit
  "pinzone-2026-education-scenario-lca"
  Pilot.pinzonePilotProfile
  pinzoneScenarioAssertion
  "model outputs include 17.2 kg CO2eq face-to-face and 5.88 kg CO2eq fully online asynchronous per 25-hour functional unit"
  "reported 95% intervals are Monte Carlo model/parameter uncertainty, not participant sampling CIs or measured deployment intervals"
  "which deployment-specific inventory values and omitted lifecycle stages would change the scenario ordering for the target institution?"
  "next discriminator is same-object deployment inventory/boundary evidence, not additional statistical precision on the current model assumptions"

------------------------------------------------------------------------
-- Holst et al. 2024: longitudinal document/input monitoring.
------------------------------------------------------------------------

holstScope : PNF.AssertionScope
holstScope = PNF.assertionScope
  "11,061 policy/curriculum/training/assessment documents"
  "formal education sectors in Germany"
  "repeated SDG 4.7.1 input-level monitoring"
  "temporal/domain comparisons across waves and education sectors"
  "documented ESD integration depth and speed-of-change indicators"
  "approximately ten-year monitoring horizon"

holstPredicates : List PNF.PredicateAtom
holstPredicates =
  PNF.predicateAtom "document-corpus" PNF.populationPredicate "document × formal-education-sector"
    "the analytic carrier is a cumulative corpus of 11,061 documents, not 11,061 human participants"
  ∷ PNF.predicateAtom "lexical-manual-coding" PNF.contextPredicate "document × indicator-coding"
    "automated lexical retrieval is followed by manual checking and peer debriefing of ambiguous segments"
  ∷ PNF.predicateAtom "input-integration-indicator" PNF.outcomePredicate "document-corpus × SDG-4.7.1-input"
    "reported outputs concern depth/status and speed of ESD input integration"
  ∷ PNF.predicateAtom "input-not-outcome" PNF.transportPredicate "input-indicator × learner-outcome"
    "documented input integration does not establish learner outcomes or system transformation"
  ∷ []

holstMonitoringAssertion : PNF.PredicateNormalAssertion
holstMonitoringAssertion = PNF.predicateNormalAssertion
  "holst-2024-sdg47-input-monitoring"
  "Across the monitored German formal-education document corpus, ESD input integration increased over time but commonly remained at isolated mentioning to partial integration across sub-indicators."
  PNF.boundedUniversalQ
  PNF.descriptiveF
  holstScope
  holstPredicates
  "same-object DOI 10.1002/sd.2865; longitudinal document-monitoring extraction"

holstAudit : StudyEvidencePNFAudit
holstAudit = study-evidence-pnf-audit
  "holst-2024-sdg47-monitoring"
  ExtPilot.holstPilotProfile
  holstMonitoringAssertion
  "latest cumulative analytic corpus n=11,061 documents; coding reliability/validity supported through manual checks, peer debriefing and external expert evaluation"
  "participant-effect CI is not applicable; uncertainty concerns corpus coverage, coding and indicator validity"
  "do stronger documented inputs correspond to learner/process/output outcomes under matched institutional observations?"
  "next probe must connect input indicators to outcome/process evidence; more documents alone cannot close that consumer"

------------------------------------------------------------------------
-- Fishlock et al. 2023: mixed-method implementation pilot.
------------------------------------------------------------------------

fishlockScope : PNF.AssertionScope
fishlockScope = PNF.assertionScope
  "40 registered first-year engineering students with method-specific analysis slices"
  "TEDI-London specialist engineering programme"
  "ten-week project-based module teaching right-to-repair principles"
  "no untreated control group"
  "student design outputs, survey responses and focus-group accounts"
  "ten-week module; no long-term follow-up"

fishlockPredicates : List PNF.PredicateAtom
fishlockPredicates =
  PNF.predicateAtom "registered-cohort" PNF.populationPredicate "student × module"
    "40 students were registered, while survey n=14 and focus-group n=5 are separate analysis sets"
  ∷ PNF.predicateAtom "right-to-repair-pbl" PNF.interventionPredicate "student × project-based-module"
    "right-to-repair principles are embedded in the delivered first-year design module"
  ∷ PNF.predicateAtom "reported-intention" PNF.outcomePredicate "survey-respondent × future-intention"
    "100% of survey respondents reported intention to implement sustainable design practices in future projects"
  ∷ PNF.predicateAtom "method-specific-analysis-set" PNF.contextPredicate "method × analysis-n"
    "survey and focus-group evidence have different analysis populations and must not be collapsed"
  ∷ PNF.predicateAtom "intention-not-behaviour" PNF.transportPredicate "self-reported-intention × future-action"
    "reported future intention does not establish later repair behaviour or population prevalence"
  ∷ []

fishlockImplementationAssertion : PNF.PredicateNormalAssertion
fishlockImplementationAssertion = PNF.predicateNormalAssertion
  "fishlock-2023-right-to-repair-implementation"
  "In the studied first-year module, right-to-repair principles were implemented through project-based learning and the small responding student subsets reported strong engagement and future sustainable-design intentions."
  PNF.studyPopulationQ
  PNF.descriptiveF
  fishlockScope
  fishlockPredicates
  "same-object DOI 10.1002/gch2.202300158; mixed-method pilot extraction"

fishlockAudit : StudyEvidencePNFAudit
fishlockAudit = study-evidence-pnf-audit
  "fishlock-2023-right-to-repair-pbl"
  ExtPilot.fishlockPilotProfile
  fishlockImplementationAssertion
  "40 registered students; survey n=14; focus-group n=5; 100% of survey respondents endorsed future sustainable-design intention"
  "no inferential CI or standardized educational effect applies to the retained implementation claim"
  "does the implemented pedagogy change observed repair/sustainable-design behaviour under a comparator and longer follow-up?"
  "next discriminator is behavioural/comparator follow-up; increasing survey rhetoric cannot substitute for observed behaviour"

------------------------------------------------------------------------
-- UNECE 2026: regional institutional-report synthesis.
------------------------------------------------------------------------

uneceScope : PNF.AssertionScope
uneceScope = PNF.assertionScope
  "31 national implementation reports"
  "UNECE/ECE member-State ESD Strategy reporting population"
  "national ESD implementation during 2021-2025"
  "cross-country/thematic synthesis rather than untreated jurisdictional control"
  "reported policy, curriculum, professional-learning, digital-access, governance and monitoring implementation patterns"
  "2021-2025 implementation cycle"

unecePredicates : List PNF.PredicateAtom
unecePredicates =
  PNF.predicateAtom "national-report-corpus" PNF.populationPredicate "national-report × member-state"
    "31 is the size of the national-report analytic corpus, not a human participant n"
  ∷ PNF.predicateAtom "self-reported-implementation" PNF.contextPredicate "member-state × national-report"
    "country implementation evidence is mediated through national self-reporting and regional synthesis"
  ∷ PNF.predicateAtom "regional-progress-gap" PNF.outcomePredicate "regional-synthesis × implementation-domain"
    "synthesis reports progress in policy/curriculum/professional learning alongside persistent digital-infrastructure, competence, governance and monitoring gaps"
  ∷ PNF.predicateAtom "input-not-local-effect" PNF.transportPredicate "regional-input-synthesis × local-learner-effect"
    "regional institutional implementation reporting does not identify a local intervention or learner causal effect"
  ∷ []

uneceImplementationAssertion : PNF.PredicateNormalAssertion
uneceImplementationAssertion = PNF.predicateNormalAssertion
  "unece-2026-regional-esd-implementation"
  "Across 31 national implementation reports, the regional evaluation synthesised continued ESD implementation progress alongside persistent digital-access, educator-competence, governance, monitoring and outcome-assessment gaps."
  PNF.studyPopulationQ
  PNF.descriptiveF
  uneceScope
  unecePredicates
  "ECE/CEP/AC.13/2026/3; regional national-report synthesis"

uneceAudit : StudyEvidencePNFAudit
uneceAudit = study-evidence-pnf-audit
  "unece-2026-fifth-esd-evaluation"
  Institutional.uneceFifthEvaluationPilotProfile
  uneceImplementationAssertion
  "analytic corpus n=31 national implementation reports; qualitative/thematic regional synthesis"
  "no intervention-effect CI applies; uncertainty concerns country self-reporting, report coverage, synthesis and cross-country heterogeneity"
  "which reported institutional changes are independently observable and which connect to learner/process outcomes in matched jurisdictions?"
  "next probe is independent/matched implementation-outcome evidence, not treating national report agreement as causal verification"

studyEvidencePNFAudits : List StudyEvidencePNFAudit
studyEvidencePNFAudits =
  ardilaAudit
  ∷ gousetiAudit
  ∷ martinezAudit
  ∷ boehmeAudit
  ∷ pinzoneAudit
  ∷ holstAudit
  ∷ fishlockAudit
  ∷ uneceAudit
  ∷ []

studyEvidencePNFCount : Nat
studyEvidencePNFCount = 8

studyEvidencePNFReading : String
studyEvidencePNFReading =
  "PNF is carrier-neutral in this review. Human participant samples, model scenarios, document corpora, systematic-review studies and national implementation reports each expose different predicates and uncertainty semantics. CI absence is not a defect when the admissible claim is qualitative, conceptual, review-synthetic or institutional; conversely, a model 95% interval is not a participant CI. Proof search is consumer-relative: ask for the least new observation that resolves the first unpaid predicate rather than ranking study designs globally or accumulating semantically adjacent citations."
