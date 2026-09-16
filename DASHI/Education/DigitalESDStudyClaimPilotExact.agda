module DASHI.Education.DigitalESDStudyClaimPilotExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Sources
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDSourceAttributionCorrectionExact as Correction
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- PILOT EXTRACTION PROFILES
--
-- These profiles exercise the claim-ceiling method on deliberately different
-- source types already in the pre-screen snowball. They are not final inclusion
-- receipts and do not pay the manuscript's database search.
------------------------------------------------------------------------

ardilaPilotProfile : Ceiling.StudyClaimProfile
ardilaPilotProfile = Ceiling.study-claim-profile
  "ardila-2025-designing-digital-education-futures"
  Sources.ardilaDigitalFuturesSource
  "candidate empirical / qualitative case-study mechanism and implementation evidence"
  "10.3390/su17104289; Methods 3.1-3.5; Conclusions"
  "source describes a qualitative case study of two five-member HE student design teams embedded in a ten-week design-thinking module"
  (Ceiling.sourceReportedDesignUnmapped
    "qualitative case study"
    "the canonical design ontology has no exact qualitative-case-study constructor; design-based learning is the pedagogical setting, not permission to relabel the research design")
  "analytic focus: two postgraduate HE student design teams (10 student designers); 60 Year-5 children participated in co-design/test sessions and two children acted as advisors, but the paper analyses the student teams' design process"
  (Ceiling.explicitlyReportedNat 10 "two five-member HE student teams; Methods 3.1")
  (Ceiling.explicitlyReportedNat 10 "ten consenting HE student designers form the primary analytic sample")
  "no randomized treatment assignment; students participated in an existing postgraduate module"
  "two design teams/cases are compared descriptively across nature-connection and fast-fashion sustainability challenges; no causal control group"
  "GreenComp competencies and temporal design-thinking practices are interpreted from design artefacts, participant-observer field notes and documented reflections"
  "no attrition estimate promoted in this pilot; all ten student designers are described as consenting participants"
  "no causal confounding adjustment; contextual qualitative case analysis"
  "ten-week module with weekly workshops and structured pedagogical supports; fidelity is described procedurally, not estimated as an intervention-effect covariate"
  "no multiplicity-adjusted inferential testing surface promoted"
  (Ceiling.reported-surface Ceiling.notReported
    "no pooled quantitative effect size used for the claim ceiling"
    "Methods/Results"
    "findings are qualitative/process-mechanism observations rather than an estimated population effect")
  (Ceiling.reported-surface Ceiling.notReported
    "no confidence interval or inferential uncertainty interval used for the qualitative claim ceiling"
    "Methods/Results"
    "absence of CI is not treated as weak evidence; the admissible question is process/context, not population prevalence")
  "ten-week Spring 2023 postgraduate module"
  "bounded to two teams in one London-based postgraduate Education and Technology module; no universal transport receipt"
  (Ceiling.reportedEpistemicRole Design.coDesigner
    "HE students were simultaneously learners/designers; children also contributed to co-design/test activities but are not collapsed into the HE analytic population")
  Ceiling.implementationContextClaim
  "supports context-bounded claims about design-thinking practices through which sustainability competencies emerged or were hindered; does not establish universal learning effects, causal population effects or system transformation"
  "small, purposive/context-specific qualitative case; two teams; ten-week horizon; researchers were participant-observers; child contributions have a different evidentiary role from the HE student analytic focus"

gousetiPilotProfile : Ceiling.StudyClaimProfile
gousetiPilotProfile = Ceiling.study-claim-profile
  "gouseti-shaw-2026-platformisation"
  Sources.gousetiPlatformisationSource
  "candidate qualitative lived-experience and implementation-context evidence"
  "10.1080/17439884.2026.2653746; Methodology; Table 1; Conclusion"
  "qualitative study using semi-structured focus groups and interviews in two English secondary schools with reflexive thematic analysis"
  (Ceiling.sourceReportedDesignUnmapped
    "qualitative multi-method interview/focus-group study"
    "the canonical design ontology separates interviews and focus groups but has no exact combined qualitative design constructor; mapping remains unresolved")
  "two secondary schools in England: Fernbrook (rural East Yorkshire) and Maybridge (London); senior leaders, teachers, students and parents"
  (Ceiling.explicitlyReportedNat 71 "Table 1 total: 4 senior leaders + 21 teachers + 36 students + 10 parents")
  (Ceiling.explicitlyReportedNat 71 "Table 1 participant total used as the qualitative analysis population in this pilot")
  "no treatment allocation; purposive school/participant recruitment for qualitative inquiry"
  "two differently platformised schools provide contextual contrast, not a randomized or quasi-experimental comparator"
  "semi-structured focus groups/interviews; student elicitation activities; verbatim transcription where audio-recorded; reflexive thematic analysis using NVivo"
  "no attrition rate inferred; pilot retains only the 71 reported participants and does not manufacture recruitment denominators"
  "no causal confounding adjustment; situated qualitative interpretation"
  "platform practices and school contexts are described in detail; no intervention-fidelity estimate because this is not an intervention trial"
  "no multiplicity-testing surface applicable to reflexive thematic analysis"
  (Ceiling.reported-surface Ceiling.notReported
    "no quantitative effect-size estimate reported for the qualitative findings"
    "Methodology/Findings"
    "themes concern experience, platform domestication, surveillance, exclusion, communication and wellbeing")
  (Ceiling.reported-surface Ceiling.notReported
    "no confidence interval applicable to the reflexive thematic-analysis claims"
    "Methodology/Findings"
    "qualitative depth is retained without pseudo-quantitative uncertainty")
  "fieldwork April-May 2024 at Fernbrook and September-October 2024 at Maybridge"
  "specific national/two-school context; authors argue analytical transferability, not statistical population representativeness"
  (Ceiling.reportedEpistemicRole Design.informant
    "leaders, teachers, students and parents supplied situated experiential accounts; role does not imply governing authority")
  Ceiling.livedExperienceClaim
  "supports situated accounts of how platformisation is experienced and domesticated across school roles, plus context-bounded implementation implications; does not establish universal prevalence, causal effect size or transformation"
  "two schools; qualitative purposive/contextual evidence; no population prevalence estimate; no randomized comparator; broader relevance is analytical rather than statistically transported"

martinezPilotProfile : Ceiling.StudyClaimProfile
martinezPilotProfile = Ceiling.study-claim-profile
  "martinez-garcia-2026-systematic-review"
  Sources.martinezDigitalEducationSystematicReviewSource
  "candidate systematic-review synthesis evidence"
  "10.3390/su18157979; Materials and Methods; PRISMA flow; Results 3.1"
  "systematic review following PRISMA; Scopus, Web of Science and reference checking; MMAT quality appraisal; PICOS extraction"
  (Ceiling.sourceReportedDesignUnmapped
    "systematic review"
    "the generic ontology names systematicReview, but its StudyDesignReceipt currently requires a participant epistemic role that is not applicable at review level; retain source-reported design until that generic receipt can represent review-level non-applicability")
  "33 peer-reviewed empirical studies in face-to-face compulsory schooling, 2012-June 2025; 502,701 participants reported across included studies"
  (Ceiling.explicitlyReportedNat 33 "final included-study count; PRISMA flow")
  (Ceiling.explicitlyReportedNat 33 "all 33 included studies entered review synthesis; no pooled meta-analytic model")
  "not applicable at review level; included studies have heterogeneous allocations/designs"
  "PICOS comparison information extracted where present; no single review-level experimental comparator"
  "MMAT 2018 used to appraise methodological quality and potential bias across qualitative, quantitative and mixed-method studies"
  "review-level attrition not applicable; PRISMA flow retains record exclusion; included-study incomplete outcome data considered through MMAT where relevant"
  "heterogeneous included-study confounding/quality retained through design-specific MMAT appraisal rather than collapsed into a pooled causal adjustment"
  "implementation fidelity identified as a recurrent limitation in the underlying literature"
  "no pooled inferential multiplicity surface; descriptive summaries and Cohen's kappa for interrater agreement"
  (Ceiling.reported-surface Ceiling.notReported
    "no pooled effect size/meta-analysis because studies were heterogeneous"
    "Materials and Methods / Results 3.1"
    "review synthesizes patterns across heterogeneous study designs rather than estimating one common effect")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "Cohen's kappa = 0.81 for interrater agreement; this is reviewer-agreement evidence, not an educational-effect confidence interval"
    "Data Extraction, Methodological Quality Appraisal, and Interrater Reliability"
    "no educational-effect CI/meta-analytic uncertainty interval is promoted")
  "search window January 2012-June 2025; review published 2026"
  "compulsory face-to-face schooling; strong heterogeneity in design, educational stage, tools, duration, outcomes and reporting limits transport/generalization"
  (Ceiling.epistemicRoleNotApplicable
    "systematic review has no single direct-participant epistemic role at review level; roles belong to included primary studies")
  Ceiling.reviewSynthesisClaim
  "supports review-level synthesis that digital education is conceptually ambiguous and that reported benefits are conditional on pedagogy, teacher mediation, infrastructure/policy and equity; does not provide a pooled causal effect or pay this manuscript's database search"
  "review not preregistered and no separate protocol was published; no meta-analysis due heterogeneity; evidence strength limited by heterogeneous designs/samples/outcomes, context-specific samples, self-report, limited longitudinal follow-up, fidelity gaps and absent comparison groups in some included studies"

boehmePilotProfile : Ceiling.StudyClaimProfile
boehmePilotProfile = Ceiling.study-claim-profile
  "boehme-2026-digitainability-framework"
  Sources.boehmeDigitainabilitySource
  "candidate conceptual-framework / prior-art evidence"
  "10.3390/educsci16050721; conceptual framing and framework sections"
  "conceptual-synthetic framework paper coupling sustainability/ESD and digitality as a twin transformation"
  (Ceiling.sourceReportedDesignUnmapped
    "conceptual-synthetic framework"
    "the source is not an empirical participant study; no empirical design class is manufactured merely to satisfy the extraction schema")
  "DACH educational discourse / conceptual literature context; no single empirical participant population"
  (Ceiling.natNotReported "no empirical enrolled-sample size applies to this conceptual framework source")
  (Ceiling.natNotReported "no empirical analysis n applies; the analytic object is conceptual/synthetic literature and discourse")
  "not applicable: no treatment assignment"
  "not applicable: no experimental comparator"
  "conceptual distinctions and framework construction rather than participant measurement"
  "not applicable: no participant attrition surface"
  "not applicable: no causal confounding-adjustment surface"
  "not applicable: no intervention-fidelity estimate"
  "not applicable: no inferential multiplicity-testing surface"
  (Ceiling.reported-surface Ceiling.notReported
    "no empirical intervention effect-size estimate"
    "conceptual framework source"
    "absence is expected for this source role and is not treated as missing trial reporting")
  (Ceiling.reported-surface Ceiling.notReported
    "no empirical confidence interval/uncertainty interval"
    "conceptual framework source"
    "conceptual contribution is not converted into pseudo-statistical precision")
  "conceptual publication horizon; not a longitudinal follow-up study"
  "framework relevance is conceptual and discourse-bounded; no population transport claim is created"
  (Ceiling.epistemicRoleNotApplicable
    "no direct participant epistemic role at the conceptual-framework level")
  Ceiling.conceptualMechanismClaim
  "supports prior-art positioning for sustainable digitality/digital sustainability as coupled transformation and constrains novelty; does not establish empirical intervention effects, participant authority, infrastructure lifecycle measurements or the current review's evidence-payment architecture"
  "conceptual source; no empirical sample, effect estimate or causal identification; useful as antecedent/framework evidence only"

descampsPilotProfile : Ceiling.StudyClaimProfile
descampsPilotProfile = Ceiling.study-claim-profile
  "descamps-2025-digital-sobriety-scenarios"
  Acquisition.descampsDigitalSobrietySource
  "candidate experimental / bounded educational-contrast evidence"
  "10.1186/s41239-025-00569-3; Methods; Sample; Results Tables 2-6"
  "pre/post pedagogical intervention with students randomly divided between individual-action and collective-action scenario groups; non-parametric group contrasts reported"
  (Ceiling.sourceReportedDesignUnmapped
    "randomly divided two-scenario pre/post educational intervention"
    "retain the source-reported design without promoting it to a stronger generic randomized-controlled-trial class: the source reports random division, substantial incomplete pre/post data, and no separate untreated control group")
  "first-year Psychological and Educational Sciences undergraduates at the University of Mons, Belgium"
  (Ceiling.explicitlyReportedNat 164 "students participating in the learning session; Sample section")
  (Ceiling.explicitlyReportedNat 107 "students completing both pre-test and post-test and used for analysis")
  "students were reported as randomly divided at scenario allocation; analytic groups were 57 and 50"
  "individual-action charter scenario versus collective-action charter scenario; both groups received the broader digital-sobriety learning intervention"
  "EMSN pre/post maturity and collective-efficacy items; EMCE motivation scale; source describes EMSN as psychometrically validated"
  "164 participated but only 107 completed both pre and post measures; missingness/attrition is therefore material and is not erased by the group randomization statement"
  "random allocation addresses some between-group confounding, but complete-case analysis and one-institution context remain live limitations; no causal promotion beyond the bounded contrasts in this pilot"
  "intervention sequence and scenario differences are described; no independent intervention-fidelity estimate is reported"
  "multiple outcomes and motivation dimensions were tested; this pilot does not manufacture a multiplicity-adjustment receipt where none is reported"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "relative maturity gains 27.63% and 25.85%; these are normalized within-group gains, not a standardized between-group effect size"
    "Results, digital sobriety maturity"
    "Mann-Whitney group contrast W=1531, p=0.051; do not relabel relative gain as standardized effect size")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "reported Mann-Whitney p-values include p=0.051 for maturity, p=0.038 for amotivation, p=0.015 and p<0.001 for collective-efficacy contrasts; no educational-effect confidence interval is reported"
    "Results Tables 2-6"
    "p-values provide contrast evidence under the reported analysis; they do not create effect-size magnitude, confidence intervals, mechanism, transport or universal pedagogy")
  "single learning intervention/session with immediate pre/post assessment; no long-term follow-up"
  "one Belgian public university, first-year cohort, predominantly female analytic sample; no population-transport receipt"
  (Ceiling.reportedEpistemicRole Design.informant
    "students supplied self-report outcome data and participated in learning activities; this does not create governance authority")
  (Ceiling.implicationConeClaim Cone.derivesBoundedContrast)
  "supports bounded within-study scenario contrasts and pre/post descriptive gains; this pilot does not promote the source's stronger causal rhetoric to universal intervention effectiveness"
  "57 of 164 session participants lack complete pre/post data; two active scenarios but no untreated control; self-report outcomes; multiple tested outcomes; no reported educational-effect CI or standardized between-group effect size; short horizon and single institution"

pinzonePilotProfile : Ceiling.StudyClaimProfile
pinzonePilotProfile = Ceiling.study-claim-profile
  "pinzone-2026-education-scenario-lca"
  Correction.pinzoneEducationLCACorrectedSource
  "candidate model-based lifecycle / environmental-impact evidence"
  "10.1007/s11367-026-02656-7; Methods 2.1-2.3; Results 3.1-3.4; uncertainty analysis"
  "comparative life-cycle assessment of face-to-face, hybrid and online higher-education scenarios using ReCiPe 2016 Midpoint (H), sensitivity analysis and Monte Carlo uncertainty"
  (Ceiling.sourceReportedDesignUnmapped
    "comparative education-scenario life-cycle assessment"
    "this is a model/inventory study rather than a participant intervention; forcing it into an experimental participant design would destroy the evidence role")
  "modelled educational scenarios at an Italian university; functional unit = 25 hours of education per student, including 10 lecture hours and 15 independent-study hours; staff preparation/support allocations are also modelled"
  (Ceiling.natNotReported "no participant enrolment n is the estimand carrier for the LCA; one-student functional unit is not a participant sample size")
  (Ceiling.natNotReported "no empirical participant analysis n applies to the scenario LCA")
  "not applicable: scenario shares are model inputs rather than participant treatment allocation"
  "face-to-face, multiple hybrid configurations, and fully online synchronous/asynchronous configurations are modelled against the same functional-unit framework"
  "ISO-style LCA inventory/model architecture with ReCiPe 2016 Midpoint (H); parameter collection includes estimates from 10 lecturers/support staff and an average-course-size allocation of 130 students, which are model inputs rather than an analysis sample"
  "not applicable as participant attrition; uncertainty belongs to inventory/model parameters"
  "scenario conclusions depend on commuting, attendance-share, ICT, energy and other modelling assumptions; sensitivity analysis explicitly tests several of these"
  "model implementation is reported through SimaPro scenario/parameter functions and the defined functional unit; no empirical intervention-fidelity concept applies"
  "multiple impact categories and scenario/sensitivity comparisons are reported; this profile retains them as model outputs rather than inferential participant tests"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "global-warming examples: face-to-face 17.2 kg CO2eq per functional unit; hybrid variants about 14.4-14.5 kg; fully online synchronous 6.0 kg and asynchronous 5.88 kg CO2eq"
    "Results 3.1, Table 4 and scenario descriptions"
    "these are scenario-model outputs for the declared functional unit, not measured emissions for every university or digital-ESD deployment")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "Monte Carlo uncertainty analysis reports 95% intervals; face-to-face key categories have CV about 2%, while hybrid key indicators are substantially more variable (reported around 31-36% in the article discussion of uncertainty)"
    "Results 3.4, Figs 7-9 and Annex uncertainty analysis"
    "95% model uncertainty intervals quantify variability under specified parameter distributions; they do not create participant sampling CIs or same-object deployment measurements")
  "scenario model represents the declared course functional unit rather than longitudinal educational outcomes"
  "Politecnico di Milano / Italian higher-education scenario assumptions, transport mix, energy mix, course structure and modelling boundaries limit direct transport; disposal was excluded for lack of sufficient data"
  (Ceiling.epistemicRoleNotApplicable
    "the LCA has no direct participant epistemic-role coordinate at model level; surveyed lecturer/support-staff inputs do not make the model a participant-outcome study")
  Ceiling.modelBasedEnvironmentalImpactClaim
  "supports bounded comparative environmental-impact claims for the declared functional unit and model assumptions, including sensitivity/uncertainty structure; does not establish measured footprint for another deployment or pedagogical effectiveness"
  "model-based scenario evidence; disposal excluded; results depend on inventory choices and uncertain attendance/transport/ICT parameters; model confidence intervals do not create external-validity or same-object measurement receipts"

pilotProfiles : List Ceiling.StudyClaimProfile
pilotProfiles =
  ardilaPilotProfile
  ∷ gousetiPilotProfile
  ∷ martinezPilotProfile
  ∷ boehmePilotProfile
  ∷ descampsPilotProfile
  ∷ pinzonePilotProfile
  ∷ []

pilotStatus : String
pilotStatus = "method-validation pilot only: source acquisition and profile construction do not create final manuscript inclusion"
