module DASHI.Education.DigitalESDColladoLongitudinalClaimExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- COLLADO / MORENO / MARTÍN-ALBO LONGITUDINAL CLAIM PROFILE
--
-- Exact same-object primary full text: DOI 10.1108/IJSHE-07-2021-0315.
-- The source pays a quasi-experimental intervention/control comparison with
-- immediate and one-year follow-up mixed-effects estimates and 95% CIs.
-- It does NOT pay random assignment, low attrition, objective behaviour, or
-- automatic causal/transport/system-transformation promotion.
------------------------------------------------------------------------

knowledgeT1InteractionCI : String
knowledgeT1InteractionCI = "b=1.04; 95% CI [0.65, 1.43]; t=5.19"

knowledgeT2InteractionCI : String
knowledgeT2InteractionCI = "b=0.74; 95% CI [0.35, 1.14]; t=3.72"

normT1InteractionCI : String
normT1InteractionCI = "b=0.53; 95% CI [0.21, 0.86]; t=3.22"

normT2InteractionCI : String
normT2InteractionCI = "b=0.34; 95% CI [0.02, 0.67]; t=2.06"

behaviourT1InteractionCI : String
behaviourT1InteractionCI = "b=0.83; 95% CI [0.54, 1.12]; t=5.63"

behaviourT2InteractionCI : String
behaviourT2InteractionCI = "b=0.69; 95% CI [0.40, 0.98]; t=4.70"

colladoLongitudinalProfile : Ceiling.StudyClaimProfile
colladoLongitudinalProfile = Ceiling.study-claim-profile
  "collado-moreno-martin-albo-2022-longitudinal-esd"
  Acquisition.colladoLongitudinalESDSource
  "candidate quasi-experimental longitudinal ESD contrast evidence"
  "10.1108/IJSHE-07-2021-0315; Participants/procedure; Data analysis; Results 3.1-3.3; Appendix 2"
  "quasi-experimental intervention versus non-participation control with T0, immediate T1 and one-year T2 repeated measurement; linear mixed-effects models with participant random intercept"
  (Ceiling.sourceReportedDesignUnmapped
    "quasi-experimental longitudinal intervention/control study"
    "participants self-selected into the ESD intervention rather than being randomly allocated; preserve source-reported design rather than promote to randomized trial")
  "University of Zaragoza Teruel Campus students; immediate analytic groups 120 experimental and 137 control; one-year complete longitudinal set 49 experimental and 49 control"
  (Ceiling.derivedNatWithSameObjectReceipt 257
    "120 experimental + 137 control complete T0/T1 cases"
    "same-object arithmetic from Participants and procedure")
  (Ceiling.explicitlyReportedNat 98
    "49 experimental + 49 control completed T2; final sample with all measures")
  "voluntary enrollment into the intervention; source explicitly states participants were not randomly assigned"
  "non-participation control group measured on the same outcomes; control is contemporaneous but non-randomized"
  "10-item environmental-knowledge test with expert content validation/pilot testing; personal norms and self-reported behaviour scales report internal consistency across T0/T1/T2"
  "approximately 18% of T0 respondents failed to complete the intervention/T1 requirements and were excluded; by T2 overall dropout was 61.87% (n=159), leaving 98 complete longitudinal participants"
  "baseline outcome levels were reported similar across groups, but voluntary participation leaves selection/unmeasured-confounding risk; no random assignment receipt"
  "workshop/seminar/role-play/practical intervention and final campus-sustainability project described; adherence required workshop completion, but no independent fidelity estimator is reported"
  "three dependent outcomes and multiple time-by-condition estimates are reported; no multiplicity-adjustment receipt is promoted in this profile"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "Time×Experimental coefficients: knowledge T1 1.04/T2 0.74; norm T1 0.53/T2 0.34; behaviour T1 0.83/T2 0.69"
    "Results 3.1-3.3; Appendix 2 Tables A1-A3"
    "source-reported mixed-effects interaction coefficients quantify bounded intervention/control longitudinal contrasts; they are not standardized population effect sizes")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "95% CIs: knowledge T1 [0.65,1.43], T2 [0.35,1.14]; norm T1 [0.21,0.86], T2 [0.02,0.67]; behaviour T1 [0.54,1.12], T2 [0.40,0.98]"
    "Results 3.1-3.3; Appendix 2 Tables A1-A3"
    "intervals belong to source-reported mixed-effects coefficients under this non-randomized observed sample; precision does not create randomization, attrition repair, objective behaviour, transport or system transformation")
  "T0 baseline, immediate T1 after intervention, and T2 one year after intervention"
  "single Spanish university/faculty context; mostly undergraduates; one-year complete-case retention is 98; no population-transport receipt"
  (Ceiling.reportedEpistemicRole Design.informant
    "students supplied knowledge-test and self-report norm/behaviour data; participation does not create governance authority")
  (Ceiling.implicationConeClaim Cone.derivesBoundedContrast)
  "supports bounded immediate and one-year intervention/control contrasts for measured environmental knowledge, personal environmental norms and self-reported pro-environmental behaviour; non-random allocation and substantial attrition block automatic causal-effect, universal durability, transport or system-transformation promotion"
  "voluntary/non-random allocation; substantial attrition to 98 complete T2 cases; self-reported behaviour; one institution; environmental rather than full social/economic sustainability scope; source discussion uses effectiveness language more strongly than this profile's retained claim ceiling"

colladoClaimReading : String
colladoClaimReading =
  "The Collado et al. source pays exact immediate and one-year mixed-effects contrasts with 95% confidence intervals, but those intervals are conditional on a self-selected quasi-experimental sample with substantial attrition. The review therefore retains derivesBoundedContrast rather than upgrading the source to randomized causal effect, universal long-term durability, transport, or system transformation."
