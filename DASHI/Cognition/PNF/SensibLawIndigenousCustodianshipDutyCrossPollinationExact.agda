module DASHI.Cognition.PNF.SensibLawIndigenousCustodianshipDutyCrossPollinationExact where

------------------------------------------------------------------------
-- INDIGENOUS CUSTODIANSHIP / DUTY CROSS-POLLINATION
--
-- Keeps four distinct duty/obligation surfaces:
--   * duties/responsibilities under traditional laws/customs;
--   * UNDRIP future-generation responsibility / land relation;
--   * ICCPR/HRC State remedy obligations in Billy;
--   * candidate Australian common-law negligence duties.
--
-- One does not definitionally create another.  Relational/custodial harm can be
-- highly relevant evidence to foreseeability, vulnerability, harm character and
-- remedial adequacy without automatically closing every common-law duty gate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESCountryRelationalTransmissionIrreversibilityExact as Relation
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Duty
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyHRCComplianceCalibrationV02Exact as BillyOdds
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Justice

------------------------------------------------------------------------
-- Distinct obligation kinds.
------------------------------------------------------------------------

data ObligationKind : Set where
  indigenousTraditionalLawCustodialResponsibility
  undripFutureGenerationResponsibility
  hrcEffectiveRemedyObligation
  australianNegligenceDutyCandidate
  : ObligationKind

data ObligationAuthority : Set where
  indigenousLawAndCustomAuthority
  internationalDeclarationAuthority
  treatyBodyViewsAuthority
  australianCourtAuthority
  dashiAnalyticalRoute
  : ObligationAuthority

record CustodialDutyReceipt : Set where
  constructor custodial-duty-receipt
  field
    obligationKind : ObligationKind
    authorityKind : ObligationAuthority
    proposition : String
    sourceReference : String
    legallyEstablishedAsAustralianNegligenceDuty : Bool
    legallyEstablishedAsAustralianNegligenceDutyIsFalse :
      legallyEstablishedAsAustralianNegligenceDuty ≡ false
    sourceRolePreserved : Bool
    sourceRolePreservedIsTrue : sourceRolePreserved ≡ true

open CustodialDutyReceipt public

griffithsTraditionalCustodialDuty : CustodialDutyReceipt
griffithsTraditionalCustodialDuty = custodial-duty-receipt
  indigenousTraditionalLawCustodialResponsibility
  indigenousLawAndCustomAuthority
  "The accepted evidence recorded a duty/concern to look after Country and a sense of failed responsibility under traditional laws and customs when Country was harmed."
  "Northern Territory v Griffiths [2019] HCA 7, especially [194], [200]-[206]"
  false refl
  true refl

undripFutureGenerationDuty : CustodialDutyReceipt
undripFutureGenerationDuty = custodial-duty-receipt
  undripFutureGenerationResponsibility
  internationalDeclarationAuthority
  "Article 25 recognises the right to maintain and strengthen the distinctive spiritual relationship with lands/waters/resources and to uphold responsibilities to future generations."
  "UNDRIP art 25"
  false refl
  true refl

billyEffectiveRemedyDuty : CustodialDutyReceipt
billyEffectiveRemedyDuty = custodial-duty-receipt
  hrcEffectiveRemedyObligation
  treatyBodyViewsAuthority
  "The Human Rights Committee required an effective remedy/full reparation, including adequate compensation, meaningful consultation/needs assessment, protective measures securing continued safe existence, monitoring/review, correction of deficiencies and prevention of similar violations."
  "Billy and others v Australia, CCPR/C/135/D/3624/2019, para 11"
  false refl
  true refl

------------------------------------------------------------------------
-- Relational evidence routing into the existing negligence-duty search.
------------------------------------------------------------------------

data RelationalDutyEvidenceKind : Set where
  permanentIntergenerationalLossEvidence
  custodialResponsibilityEvidence
  placeSpecificNonFungibilityEvidence
  communityDefinedHarmEvidence
  treatyBodyRemedyEvidence
  : RelationalDutyEvidenceKind

record DutyIssueEvidenceBridge : Set where
  constructor duty-issue-evidence-bridge
  field
    evidenceKind : RelationalDutyEvidenceKind
    targetIssue : Duty.DutyIssue
    sourceReference : String
    mayInformIssue : Bool
    mayInformIssueIsTrue : mayInformIssue ≡ true
    issueAutomaticallySatisfied : Bool
    issueAutomaticallySatisfiedIsFalse : issueAutomaticallySatisfied ≡ false
    bridgeIsDASHISynthesis : Bool
    bridgeIsDASHISynthesisIsTrue : bridgeIsDASHISynthesis ≡ true

open DutyIssueEvidenceBridge public

relationalLossToHarmType : DutyIssueEvidenceBridge
relationalLossToHarmType = duty-issue-evidence-bridge
  permanentIntergenerationalLossEvidence
  Duty.harmTypeDeterminacy
  "Griffiths [2019] HCA 7 cultural-loss reasoning"
  true refl
  false refl
  true refl

relationalLossToForeseeability : DutyIssueEvidenceBridge
relationalLossToForeseeability = duty-issue-evidence-bridge
  permanentIntergenerationalLossEvidence
  Duty.reasonableForeseeability
  "Griffiths + Billy relational/cultural harm sources"
  true refl
  false refl
  true refl

custodianshipToVulnerability : DutyIssueEvidenceBridge
custodianshipToVulnerability = duty-issue-evidence-bridge
  custodialResponsibilityEvidence
  Duty.vulnerability
  "Griffiths accepted evidence of responsibilities to care for Country; UNDRIP art 25 future-generation responsibility"
  true refl
  false refl
  true refl

placeSpecificityToCompensability : DutyIssueEvidenceBridge
placeSpecificityToCompensability = duty-issue-evidence-bridge
  placeSpecificNonFungibilityEvidence
  Duty.compensability
  "Griffiths rejected treating different land at another location as equivalent to Country-specific attachment for valuation purposes"
  true refl
  false refl
  true refl

------------------------------------------------------------------------
-- Pabai remains current negative calibration for its pleaded negligence route.
-- Appeal material is procedural until judgment is entered.
------------------------------------------------------------------------

pabaiDoesNotDefinitionallyCloseEveryReformulatedDuty :
  Duty.PabaiNoDutyClosesEveryPossibleClimateDuty → ⊥
pabaiDoesNotDefinitionallyCloseEveryReformulatedDuty =
  Duty.pabaiDoesNotCloseEveryReformulatedDutyByDefinition

record CurrentPabaiAppealBoundary : Set where
  constructor current-pabai-appeal-boundary
  field
    firstInstanceJudgmentExists : Bool
    firstInstanceJudgmentExistsIsTrue : firstInstanceJudgmentExists ≡ true
    appealSubmissionsAndOralOutlinePublic : Bool
    appealSubmissionsAndOralOutlinePublicIsTrue :
      appealSubmissionsAndOralOutlinePublic ≡ true
    appealJudgmentRecoveredByThisOwner : Bool
    appealJudgmentRecoveredByThisOwnerIsFalse :
      appealJudgmentRecoveredByThisOwner ≡ false
    submissionsAreJudgment : Bool
    submissionsAreJudgmentIsFalse : submissionsAreJudgment ≡ false

open CurrentPabaiAppealBoundary public

currentPabaiAppealBoundary : CurrentPabaiAppealBoundary
currentPabaiAppealBoundary = current-pabai-appeal-boundary
  true refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Billy remedy means/odds: a global treaty-body reference class now exists,
-- but case-specific probability remains open.
------------------------------------------------------------------------

billyGlobalReferenceLowerPercent : Nat
billyGlobalReferenceLowerPercent =
  BillyOdds.lowerReportedCompliancePercent BillyOdds.globalTreatyBodyReference

billyGlobalReferenceUpperPercent : Nat
billyGlobalReferenceUpperPercent =
  BillyOdds.upperReportedCompliancePercent BillyOdds.globalTreatyBodyReference

billyStrictMeanFullCompliancePercent : Nat
billyStrictMeanFullCompliancePercent =
  BillyOdds.strictFullComplianceMeanPercent BillyOdds.globalTreatyBodyReference

billyCaseSpecificProbabilityStillOpen :
  BillyOdds.billySpecificProbabilityRecovered BillyOdds.currentOddsCalibrationV02 ≡ false
billyCaseSpecificProbabilityStillOpen = refl

billyFullReparationStillOperationallyLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
billyFullReparationStillOperationallyLive = refl

------------------------------------------------------------------------
-- Realised justice: custodianship is not closed by consultation or money alone.
------------------------------------------------------------------------

landCountryControlStillOpen :
  Justice.currentOperationalJusticeState Justice.landAndCountryControl
  ≡ Justice.residualOpen
landCountryControlStillOpen = refl

culturalContinuityStillNeedsSourceOutcome :
  Justice.currentOperationalJusticeState Justice.culturalContinuity
  ≡ Justice.sourceStateUnresolved
culturalContinuityStillNeedsSourceOutcome = refl

compensationStillOpen :
  Justice.currentOperationalJusticeState Justice.compensationAndReparation
  ≡ Justice.residualOpen
compensationStillOpen = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data IndigenousCustodialDutyEqualsCommonwealthNegligenceDuty : Set where
data HRCRemedyEqualsAustralianNegligenceDuty : Set where
data ForeseeableRelationalHarmAutomaticallyCreatesDuty : Set where
data CompensationAloneRestoresCustodialRelation : Set where
data ConsultationAloneTransfersCustodialAuthority : Set where

traditionalCustodialDutyDoesNotAutoCreateNegligenceDuty :
  IndigenousCustodialDutyEqualsCommonwealthNegligenceDuty → ⊥
traditionalCustodialDutyDoesNotAutoCreateNegligenceDuty ()

hrcRemedyDoesNotBecomeNegligenceDuty : HRCRemedyEqualsAustralianNegligenceDuty → ⊥
hrcRemedyDoesNotBecomeNegligenceDuty ()

foreseeabilityDoesNotByItselfCreateDuty :
  ForeseeableRelationalHarmAutomaticallyCreatesDuty → ⊥
foreseeabilityDoesNotByItselfCreateDuty ()

moneyDoesNotReconstituteRelationByDefinition :
  CompensationAloneRestoresCustodialRelation → ⊥
moneyDoesNotReconstituteRelationByDefinition ()

consultationDoesNotTransferCustodialAuthority :
  ConsultationAloneTransfersCustodialAuthority → ⊥
consultationDoesNotTransferCustodialAuthority ()
