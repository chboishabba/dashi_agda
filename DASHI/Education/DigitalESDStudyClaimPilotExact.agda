module DASHI.Education.DigitalESDStudyClaimPilotExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Sources
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design

------------------------------------------------------------------------
-- PILOT EXTRACTION PROFILES
--
-- These profiles exercise the claim-ceiling method on three deliberately
-- different source types already in the pre-screen snowball. They are not
-- final inclusion receipts and do not pay the manuscript's database search.
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

pilotProfiles : List Ceiling.StudyClaimProfile
pilotProfiles = ardilaPilotProfile ∷ gousetiPilotProfile ∷ martinezPilotProfile ∷ []

pilotStatus : String
pilotStatus = "method-validation pilot only: source acquisition and profile construction do not create final manuscript inclusion"
