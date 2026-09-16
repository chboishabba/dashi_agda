module DASHI.Education.DigitalESDStudyClaimPilotExtensionExact where

open import DASHI.Core.Prelude

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Sources
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- ADDITIONAL HETEROGENEOUS PILOT PROFILES
--
-- These remain method-validation / pre-screen fixtures. They test two evidence
-- shapes that a participant-trial-centric schema can mishandle:
--   * a large longitudinal document-monitoring corpus; and
--   * a mixed-method pilot with distinct survey and focus-group analysis Ns.
------------------------------------------------------------------------

holstPilotProfile : Ceiling.StudyClaimProfile
holstPilotProfile = Ceiling.study-claim-profile
  "holst-2024-sdg47-monitoring"
  Sources.holstSDG47MonitoringSource
  "candidate longitudinal input-monitoring evidence"
  "10.1002/sd.2865; Abstract; Methods 3.1; Results/Discussion"
  "repeated large-scale document analysis combined with external expert evaluation for SDG 4.7.1 input-level monitoring across formal education in Germany"
  (Ceiling.sourceReportedDesignUnmapped
    "longitudinal document monitoring plus expert evaluation"
    "the analytic carrier is a document corpus and indicator framework, not an enrolled participant intervention; no participant-trial design class is manufactured")
  "11,061 policy/curriculum/educator-training/student-assessment documents across early childhood, school, VET and higher education in Germany; monitoring waves accumulate prior and newly collected documents"
  (Ceiling.explicitlyReportedNat 11061 "latest cumulative monitoring corpus; Methods 3.1")
  (Ceiling.explicitlyReportedNat 11061 "document corpus entering the latest systematic lexical/qualitative analysis surface")
  "not applicable: documents are not allocated to treatment"
  "temporal/domain comparisons across monitoring waves and education sectors/sub-indicators; no experimental control group"
  "automated lexical search for ESD/sustainability-related concepts followed by manual checking; ambiguous text segments coded uncertain and peer-debriefed by three researchers; external expert evaluation supplements document analysis"
  "not participant attrition; corpus growth/update across waves is retained as sampling-frame evolution rather than human dropout"
  "no causal confounding adjustment; this is descriptive/indicator monitoring of document-level implementation inputs"
  "repeated national monitoring procedures and common indicator framework support longitudinal comparability, while changes in document coverage remain explicit"
  "not an inferential multiplicity-testing design; multiple keywords, domains and sub-indicators are part of the indicator architecture"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "input-level status/depth and speed-of-change indicators across SDG 4.7.1 domains; the source reports mostly isolated mentioning to partial integration and increasing implementation across sub-indicators"
    "Abstract / results"
    "these are indicator/monitoring results, not learner effect sizes")
  (Ceiling.reported-surface Ceiling.notReported
    "no participant-effect confidence interval is required for the document-monitoring claim ceiling"
    "Methods/results"
    "reliability/validity are addressed through coding procedures and expert evaluation rather than a participant-effect CI")
  "10-year data horizon reported by the source; latest document collection described for 2021/22"
  "Germany, formal education sectors and the operationalized SDG 4.7.1 input indicator; transport to learning outcomes or other national systems requires separate evidence"
  (Ceiling.epistemicRoleNotApplicable
    "the main analysis carrier is documents; external experts contribute evaluation but there is no single participant epistemic role for the study-level monitoring object")
  (Ceiling.implicationConeClaim Cone.restatesMeasuredResult)
  "supports longitudinal claims about documented input-level ESD integration, depth and speed of change; cannot by itself establish student learning, behavioural outcomes, digital-ESD effectiveness or system transformation"
  "document/indicator study; changing corpus coverage across waves; country-specific institutional context; expert evaluation and coding criteria do not convert input integration into output/outcome transformation"

fishlockSurveyAnalysisN : Ceiling.ReportedNat
fishlockSurveyAnalysisN =
  Ceiling.explicitlyReportedNat 14 "anonymous questionnaire respondents"

fishlockFocusGroupAnalysisN : Ceiling.ReportedNat
fishlockFocusGroupAnalysisN =
  Ceiling.explicitlyReportedNat 5 "focus-group participants"

fishlockPilotProfile : Ceiling.StudyClaimProfile
fishlockPilotProfile = Ceiling.study-claim-profile
  "fishlock-2023-right-to-repair-pbl"
  Acquisition.fishlockRightToRepairEducationSource
  "candidate mixed-method project-based-learning implementation evidence"
  "10.1002/gch2.202300158; Abstract; Results 3; Limitations 3.3"
  "first-year project-based engineering design module teaching right-to-repair principles, evaluated with student design outputs, an anonymous questionnaire and a focus group"
  (Ceiling.sourceReportedDesignUnmapped
    "mixed-method educational pilot study"
    "the study combines design-output analysis, a survey and a focus group; no single generic design constructor or single analysis population fully represents it")
  "40 registered first-year Global Design Engineering students at TEDI-London; analysis surfaces differ by method"
  (Ceiling.explicitlyReportedNat 40 "registered first-year students in the module")
  (Ceiling.natNotReported "no single study-wide analysis n: survey n=14 and focus-group n=5 are distinct typed analysis slices retained separately")
  "no random treatment assignment; whole module implemented as a teaching pilot"
  "no separate untreated/control group; evidence combines project outputs, questionnaire responses and focus-group accounts"
  "course-design/output evidence, anonymous questionnaire and focus group; source reports innovative design features and self-reported future sustainable-design intentions"
  "40 registered students but 14 survey respondents and 5 focus-group participants; response participation is therefore method-specific and must not be collapsed into one analysis n"
  "no causal confounding adjustment; one specialist institution and one cohort"
  "ten-week prototyping module described in detail; implementation evidence comes from the delivered module and student outputs rather than a standardized fidelity estimate"
  "questionnaire items are descriptive; no multiplicity-adjusted inferential-testing surface promoted"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "100% of survey respondents agreed or strongly agreed that they intended to try to implement sustainable design practices in future projects; 78.6% reported company sustainability agenda as a consideration"
    "Results 3.1-3.2 / Figures 4 and 6"
    "percentages describe the 14 questionnaire respondents and are not population effect sizes or prevalence estimates for engineering students generally")
  (Ceiling.reported-surface Ceiling.notReported
    "no inferential confidence interval or standardized educational effect estimate reported"
    "Results/limitations"
    "small mixed-method pilot provides implementation/engagement evidence rather than a population-effect estimate")
  "ten-week teaching/prototyping module; no long-term follow-up"
  "new specialist UK engineering institute, one degree programme, small cohort; authors explicitly state students do not fully represent the wider UK engineering cohort"
  (Ceiling.reportedEpistemicRole Design.informant
    "students supplied questionnaire/focus-group accounts and produced design artefacts; this supports situated learner evidence without creating population prevalence or governance authority")
  Ceiling.implementationContextClaim
  "supports context-bounded implementation evidence that right-to-repair principles can be embedded in a first-year PBL design module and that responding students reported strong engagement/future intention; does not establish causal educational effectiveness, general prevalence or actual future repair behaviour"
  "small single-institution pilot; no control group; distinct survey/focus-group analysis populations; self-report intentions are not observed future behaviour; no long-term follow-up"

extensionProfiles : List Ceiling.StudyClaimProfile
extensionProfiles = holstPilotProfile ∷ fishlockPilotProfile ∷ []

multiAnalysisNResidual : String
multiAnalysisNResidual =
  "Fishlock exposes a real extraction-shape residual: one study can have several method-specific analysis Ns. The current StudyClaimProfile retains one primary analysisN field, so this pilot keeps that field explicitly unresolved at study level while separately typing survey n=14 and focus-group n=5. Do not redesign the global schema unless additional admitted studies make a structured multi-analysis-N carrier a recurring consumer requirement."
