module DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooEPBC20198575OperativeMeritsRulesExact as Merits
import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative
import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact as Condition
import DASHI.Law.SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact as Counsel
import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact as File
import DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact as Post

------------------------------------------------------------------------
-- EPBC 2019/8575 LITIGATION GROUND / COUNTERGROUND CUT.
--
-- NO FALSE SAME-OBJECT PROMOTION:
--  * operative merits texts require 2025/26 transitional Act mapping;
--  * 2013 FCA 694 favorable, 2015 FCAFC 89 adverse; distinct decisions;
--  * a case quote or AGS legal analysis is not a Woogaroo holding;
--  * other-project impacts = baseline/context, not automatically the
--    statutory consequences of this proposed action;
--  * ecological concern != jurisdictional error or automatic interim stay.
--
-- Every alleged ground below is a case-research hypothesis, not a filed
-- pleading, executed test, advice, or kernel-certified theorem.
------------------------------------------------------------------------

koala2022ApprovedConservationAdvice : Source.AttributedSource
koala2022ApprovedConservationAdvice = Source.mkNoDOISource
  "Australian Government Department of Agriculture, Water and the Environment / Threatened Species Scientific Committee"
  "2022 Conservation Advice for Phascolarctos cinereus, QLD/NSW/ACT combined population"
  "Original s266B approved conservation advice, operative 12 February 2022"
  "12 February 2022"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/ca34e3c6-b216-ed11-b83e-00224818a528/2ab10dab-d681-4911-b881-cc99413f07b6?file=Att+H+-+DAWE+%282022%29+Conservation+Advice+for+Phascolarctos+cinereus+%28Koala%29.pdf"
  Source.governmentSource
  "Original Commonwealth source describes the approved species advice, not an EPBC 2019/8575 decision. Whether it was properly given to, genuinely considered by, and applied by the 15 Oct delegate is unproved until original briefing/reasons. Do not substitute old 2012 vulnerable listing advice for 2022 endangered advice."
  Source.publicAttribution

koala2022NationalRecoveryPlan : Source.AttributedSource
koala2022NationalRecoveryPlan = Source.mkNoDOISource
  "Department of Agriculture, Water and the Environment / NSW Government"
  "National Recovery Plan for Koala, QLD/NSW/ACT populations (2022)"
  "Original national koala recovery plan under EPBC Act"
  "2022"
  "https://www.dcceew.gov.au/sites/default/files/documents/recovery-plan-koala-2022.pdf"
  Source.governmentSource
  "Original 2022 plan states an objective of connected, genetically healthy koala metapopulations and improved habitat extent, quality and connectivity. Under the applicable s139(1), the decision must not act inconsistently with relevant recovery or threat-abatement plans. An ecologically contested assessment does not itself prove legal inconsistency."
  Source.publicAttribution

australianGovernmentSolicitor2024 : Source.AttributedSource
australianGovernmentSolicitor2024 = Source.mkNoDOISource
  "Australian Government Solicitor"
  "Legal Briefing No. 129: Commonwealth environment and heritage law"
  "Original 23 February 2024 government legal explanation of EPBC causation and cumulative setting"
  "23 February 2024"
  "https://www.ags.gov.au/publications/legal-briefing/lb-20240219"
  Source.practitionerSource
  "AGS explains case law: other actions' impacts may set ecological baseline and significance of THIS action, but are not automatically effects of THIS proposal. Distinguish original court judgments from this official practitioner synthesis; trace direct versus indirect consequences under s527E and the causation chain, not all regional harms merged."
  Source.publicAttribution

tarkine2013FederalCourtOriginalJudgmentSummary : Source.AttributedSource
tarkine2013FederalCourtOriginalJudgmentSummary = Source.mkNoDOISource
  "Federal Court of Australia (judgment of Marshall J; Court official annual report summary)"
  "Tarkine National Coalition Inc v Minister [2013] FCA 694 — mandatory approved conservation advice"
  "Original Federal Court 2013–14 annual report Appendix 7 summarising a judgment"
  "17 July 2013 decision; 2013–14 annual report"
  "https://www.fedcourt.gov.au/__data/assets/pdf_file/0003/25734/Annual-Report-2013-14-Appendix7.pdf"
  Source.governmentSource
  "Court's own annual-report summary records 2013 approval invalidated for missing approved Tasmanian devil conservation advice under then s139(2). Different mine, species and year; not a 2019/8575 ruling or assurance of permanent protection. Parliament reported new mine approval dated 29 July 2013."
  Source.publicAttribution

tarkine2015FullCourtAdverse : Source.AttributedSource
tarkine2015FullCourtAdverse = Source.mkNoDOISource
  "Full Federal Court (Jessup, Kenny, Middleton JJ)"
  "Tarkine National Coalition Inc v Minister for Environment [2015] FCAFC 89"
  "Original 2015 Full Court judicial ruling, contextualised in 2024 Court judgment and AGS 2024"
  "26 June 2015"
  "https://www.judgments.fedcourt.gov.au/judgments/Judgments/fca/full/2024/2024fcafc0056"
  Source.governmentSource
  "2015 FCAFC 89 is a DIFFERENT approval challenge from successful 2013 FCA 694. It rejects proposed general s136(2)(e) duty to count every other project's consequences as the assessed action's own consequences. Court original 2024 FCAFC 56 discusses its reasoning. Linked URL is to 2024 primary citation/analysis of 2015, NOT falsely labelled an accessible 2015 full-text copy."
  Source.publicAttribution

eccq2024FullCourtPrimary : Source.AttributedSource
eccq2024FullCourtPrimary = Source.mkNoDOISource
  "Full Federal Court (Mortimer CJ, Colvin and Horan JJ)"
  "Environment Council of Central Queensland Inc v Minister [2024] FCAFC 56"
  "Original Court-issued Full Court reasons and orders, 16 May 2024"
  "16 May 2024"
  "https://www.judgments.fedcourt.gov.au/judgments/Judgments/fca/full/2024/2024fcafc0056"
  Source.governmentSource
  "Official Court judgment dismissed the climate-reconsideration appeal, discusses existing protected matter baseline and action-specific s527E causation, and cites Tarkine 2015. Not a Springview Part 9 approval merits decision or a mandatory universal regional cumulative assessment duty."
  Source.publicAttribution

rainforest2025Dismissal : Source.AttributedSource
rainforest2025Dismissal = Source.mkNoDOISource
  "Federal Court of Australia (Shariff J)"
  "Rainforest Reserves Australia Inc v Minister for the Environment and Water [2025] FCA 532"
  "Federal Court 22 May 2025 decision; full text hosted by secondary legal reporter"
  "22 May 2025"
  "https://casechat.au/cases/au/rainforest-reserves-australia-inc-v-minister-for-the-environment-and-water"
  Source.practitionerSource
  "Different Queensland wind-farm Part 9 approval. Original Court judgment text reproduced by case reporter describes dismissed review: alleged authorised-action expansion, unclear trigger definitions and deferred management conditions failed. Link is a SECONDARY mirror of judicial text; original court URL not independently acquired here. It is not factual proof Springview conditions are lawful."
  Source.publicAttribution

epbcTransitionDepartmentOriginal : Source.AttributedSource
epbcTransitionDepartmentOriginal = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "EPBC reform transitional arrangements for projects already referred"
  "Original Commonwealth post-2025 reform implementation guidance"
  "28 October 2026 access"
  "https://www.dcceew.gov.au/environment/epbc/epbc-act-reform/transitional-arrangements"
  Source.governmentSource
  "Government says previously referred projects are assessed under old law while new project standards commence later. This administrative guidance does NOT itself pay paragraph-by-paragraph commencement and savings for 2019/8575. Inspect original Reform Act 2025 Part 3 Schedule 1 and August transitional rules F2026L01106."
  Source.publicAttribution

data Ground : Set where
  approvedAdviceOmitted : Ground
  recoveryPlanConflict : Ground
  actionBaselineError : Ground
  commentTransmissionOrProcedure : Ground
  scopeOrUncertainConditions : Ground
  sameStageCondition6aBreach : Ground
  improperPoliticalFinancialInfluence : Ground

data MeritsStatus : Set where
  preciseHypothesisOnly : MeritsStatus
  documentedPrimaryIssueOnly : MeritsStatus

record CaseHypothesis : Set where
  constructor case-hypothesis
  field
    proposedGround : Ground
    originalAuthority : Source.AttributedSource
    status : MeritsStatus
    hook : String
    proofNeeded : String
    bestDefence : String
    falsifier : String
    establishedSpecificBreach : Bool
    failClosed : establishedSpecificBreach ≡ false
open CaseHypothesis public

adviceGround : CaseHypothesis
adviceGround = case-hypothesis approvedAdviceOmitted tarkine2013FederalCourtOriginalJudgmentSummary preciseHypothesisOnly
  "Test transitional pre-reform s139(2): genuine consideration of 2022 endangered koala approved conservation advice where statutory significant-impact trigger applies."
  "Original decision brief/checklist, 2022 advice version, s95C report and attachments, 15 Oct signed decision/reasons, exact controlling species and finding of significant impact."
  "The advice was in the brief or genuinely considered; source-driven species impacts and conditions address it even if campaign disputes weighting."
  "Authenticated decision materials prove adequate consideration of the correct 2022 advice or the statutory trigger is not met."
  false refl

recoveryGround : CaseHypothesis
recoveryGround = case-hypothesis recoveryPlanConflict koala2022NationalRecoveryPlan preciseHypothesisOnly
  "Separate applicable pre-reform s139(1): approval must not act inconsistently with relevant recovery plan or threat-abatement plan."
  "Identify actual legally operative plan and enforceable relevant provisions, compare signed approval/conditions and stated decision grounds with the plan."
  "The broad recovery objective and local lawful conditioned development may coexist; an alleged conflict is not a contradiction without an exact provision."
  "Approved conditional action is legally reconcilable with each applicable plan provision."
  false refl

actionImpactGround : CaseHypothesis
actionImpactGround = case-hypothesis actionBaselineError eccq2024FullCourtPrimary documentedPrimaryIssueOnly
  "Assess THIS Springview clearing's marginal impact on locally diminished koala habitat, not union of all surrounding developments as consequences under s136(2)(e)."
  "Final PD Item 4.6(c) analysis, 2022 approved advice, expert before/after habitat function, s95C/reasons and direct/indirect causation, plus materially missed statutory item."
  "Tarkine 2015 and ECCC 2024 limit free-standing regional cumulative duty. Stockland publicly says retained corridors are three times the local planning minimum, staged fauna management applies, and scat/surveys do not show a large resident colony. These are publisher claims to test against the actual government decision and ecological originals."
  "Signed file gives action-specific ecological baseline, local connectivity analysis, reasoned findings and lawful offset/mitigation treatment."
  false refl

commentsGround : CaseHypothesis
commentsGround = case-hypothesis commentTransmissionOrProcedure australianGovernmentSolicitor2024 preciseHypothesisOnly
  "Test pre-reform s95B(1) actual proponent comment copies, final PD/responding summary and Secretary s95C recommendation chronological receipt."
  "QUT/QCC actual submission send/receive, all 1,786-original comments if verified, proponent 95B transmission bundle, Secretary 95C version, signed Part 9 decision."
  "The statutory materials and comments were fully transmitted/considered and the public portal merely does not show them."
  "Actual authenticated transmitted set and s95C with dates and evidence of required process."
  false refl

scopeGround : CaseHypothesis
scopeGround = case-hypothesis scopeOrUncertainConditions rainforest2025Dismissal preciseHypothesisOnly
  "A live action scope or legal certainty ground is possible only after 15 October conditions and original referred action are compared."
  "Signed final conditions, maps, definitions, referred action and expert plan approval mechanism, actual work stage and parties."
  "Rainforest Reserves [2025] FCA 532 dismissed similar action-scope/uncertainty claims where conditions were sufficiently ascertainable."
  "The approval scope matches referral; conditions define boundaries, compliance monitoring and adaptive management with lawful precision."
  false refl

localPrestartGround : CaseHypothesis
localPrestartGround = case-hypothesis sameStageCondition6aBreach epbcTransitionDepartmentOriginal preciseHypothesisOnly
  "Separate Queensland 9281/2024/OW prestart Condition 6(a) evidentiary gate; a valid federal Part 9 approval may satisfy the alternative if accepted."
  "Council original submission/receipt/acceptance, preclearance and fauna documents, stage-specific works and registered land/works polygon."
  "Council received and accepted conditions before works, or no works commenced; public silence does not prove breach."
  "Dated accepted record and valid same-stage prestart compliance before any relevant action."
  false refl

politicalTheory : CaseHypothesis
politicalTheory = case-hypothesis improperPoliticalFinancialInfluence australianGovernmentSolicitor2024 preciseHypothesisOnly
  "Historical Springfield finance, gas, portfolio and lobbying records are leads, NOT legal defects in the 15 Oct decision without actual relevant decision-channel evidence."
  "Authenticated current conflict, direct communication/recipient/duty and causally material corruption or bias under applicable review standard."
  "All source dates and projects differ, lawful policy considerations are permitted under s136, and no current improper transfer, prejudice or disqualification is shown."
  "Verified separate projects, lawful financial instruments, appropriate decision reasons and no direct conflicted decision-maker evidence."
  false refl

pleadableCut : List CaseHypothesis
pleadableCut =
  adviceGround ∷ recoveryGround ∷ actionImpactGround ∷
  commentsGround ∷ scopeGround ∷ localPrestartGround ∷
  politicalTheory ∷ []

-- Original owners, not reconstructed:
canonicalMerits139 : Merits.OperativeRule
canonicalMerits139 = Merits.s139

canonicalMerits136 : Merits.OperativeRule
canonicalMerits136 = Merits.s136

canonicalCumulativeResidual : Cumulative.CumulativeResponseResidual
canonicalCumulativeResidual = Cumulative.locatedLocalRegionalIntegrationResidual

canonicalCondition6aSubmission : Condition.Condition6aEvidenceObject
canonicalCondition6aSubmission = Condition.condition6aLiteralSubmission

canonicalCondition6aAcceptance : Condition.Condition6aEvidenceObject
canonicalCondition6aAcceptance = Condition.condition6aCouncilAcceptance

canonicalStandingUnpaid : Counsel.LitigationGate
canonicalStandingUnpaid = Counsel.organisationStanding

-- Developer's own countercase is retained as original publisher claim,
-- not as verified regulator ecological conclusion or registered land title.
canonicalStocklandFirstPartyDefence : Source.AttributedSource
canonicalStocklandFirstPartyDefence = Post.stocklandSpringview

canonicalSecretaryReportUnpaid : File.DecisionFileReceipt
canonicalSecretaryReportUnpaid = File.section95CRecommendation

-- Empty no-promotion claims. These guard source-text typing, not outcomes.
data RegionalHarmSumEqualsLegallyRequiredProjectImpact : Set where
data 2013TarkineIsSameAs2015TarkineDecision : Set where
data GovernmentLegalBriefingEqualsJudicialHolding : Set where
data RecoveryPlanGoalEqualsAutomaticApprovalProhibition : Set where
data 2022AdviceURLProvesMinisterActuallyConsideredAdvice : Set where
data AbsenceFromPublicPortalProvesSecretaryOmittedDocument : Set where
data GovernmentTransitionWebpageAloneProvesEveryOldMeritsProvision : Set where
data 2025DismissedWindFarmCaseProvesSpringviewApprovalValid : Set where
data SevenSourceWrittenGroundsAreFiledCourtPleadings : Set where
data DeveloperFAQEqualsCommonwealthScientificFinding : Set where

regionalHarmNotOwnProjectImpact :
  RegionalHarmSumEqualsLegallyRequiredProjectImpact → ⊥
regionalHarmNotOwnProjectImpact ()

distinctTarkineDecisions :
  2013TarkineIsSameAs2015TarkineDecision → ⊥
distinctTarkineDecisions ()

practitionerSummaryNotCourtJudgment :
  GovernmentLegalBriefingEqualsJudicialHolding → ⊥
practitionerSummaryNotCourtJudgment ()

recoveryAimNotAbsoluteProhibition :
  RecoveryPlanGoalEqualsAutomaticApprovalProhibition → ⊥
recoveryAimNotAbsoluteProhibition ()

adviceURLNotConsideration :
  2022AdviceURLProvesMinisterActuallyConsideredAdvice → ⊥
adviceURLNotConsideration ()

notPublicNotNecessarilyAbsent :
  AbsenceFromPublicPortalProvesSecretaryOmittedDocument → ⊥
notPublicNotNecessarilyAbsent ()

guidanceNotCommencementMatrix :
  GovernmentTransitionWebpageAloneProvesEveryOldMeritsProvision → ⊥
guidanceNotCommencementMatrix ()

differentWindFarmDoesNotDecideWoogaroo :
  2025DismissedWindFarmCaseProvesSpringviewApprovalValid → ⊥
differentWindFarmDoesNotDecideWoogaroo ()

sourceHypothesesNotFiled :
  SevenSourceWrittenGroundsAreFiledCourtPleadings → ⊥
sourceHypothesesNotFiled ()

developerClaimNotRegulatorFinding :
  DeveloperFAQEqualsCommonwealthScientificFinding → ⊥
developerClaimNotRegulatorFinding ()
