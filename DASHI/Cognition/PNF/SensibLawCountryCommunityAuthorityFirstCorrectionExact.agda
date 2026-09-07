module DASHI.Cognition.PNF.SensibLawCountryCommunityAuthorityFirstCorrectionExact where

------------------------------------------------------------------------
-- COUNTRY COMMUNITY-AUTHORITY-FIRST CORRECTION
--
-- Application compiler over the current Country/Mabo/Billy operational state.
-- The first corrective step is not another State-authored success report.  It
-- is an affected-community-defined outcome/authority receipt, preserving Two-
-- Eyed nonfusion and the existing Human Rights Committee remedy coordinates.
--
-- This file introduces no new treaty-body holding or empirical proposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.PluralOperationalResidualActionLoopExact as Adaptive
import DASHI.Core.PluralOperationalRealisationDiscrepancyExact as Discrepancy
import DASHI.Core.PluralOperationalEvidenceBraidBidiExact as Braid
import DASHI.Cognition.PNF.SensibLawCountryPluralEpistemicOperationalAuditExact as Audit
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- Current operational frontier.
------------------------------------------------------------------------

currentFirstLiveStep :
  Adaptive.firstOpen Audit.currentCountryOperationalSnapshot
  ≡ Adaptive.actOnCommunityOutcome
currentFirstLiveStep = refl

currentCommunityOutcomeState :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.communityDefinedOutcomeCoordinate
  ≡ Operational.coordinateOpen
currentCommunityOutcomeState = refl

currentCommunityAuthorityState :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.communityAuthorityCoordinate
  ≡ Operational.coordinateOpen
currentCommunityAuthorityState = refl

currentCorrectionResponseState :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.correctionResponseCoordinate
  ≡ Operational.coordinateOpen
currentCorrectionResponseState = refl

------------------------------------------------------------------------
-- Correction sequence: outcome -> authority -> response -> prevention.
------------------------------------------------------------------------

data CountryCorrectionStage : Set where
  obtainCommunityDefinedOutcomeStage
  establishCommunityAuthorityStage
  testInstitutionalCorrectionStage
  verifyMaterialEffectStage
  verifyPreventionStage
  operationalClosureStage
  : CountryCorrectionStage

nextCorrectionStage : CountryCorrectionStage → CountryCorrectionStage
nextCorrectionStage obtainCommunityDefinedOutcomeStage = establishCommunityAuthorityStage
nextCorrectionStage establishCommunityAuthorityStage = testInstitutionalCorrectionStage
nextCorrectionStage testInstitutionalCorrectionStage = verifyMaterialEffectStage
nextCorrectionStage verifyMaterialEffectStage = verifyPreventionStage
nextCorrectionStage verifyPreventionStage = operationalClosureStage
nextCorrectionStage operationalClosureStage = operationalClosureStage

record CommunityAuthorityFirstCorrectionPlan : Set where
  constructor community-authority-first-correction-plan
  field
    firstStage : CountryCorrectionStage
    firstStageExact : firstStage ≡ obtainCommunityDefinedOutcomeStage
    affectedCommunityOutcomeRequired : Bool
    affectedCommunityOutcomeRequiredIsTrue : affectedCommunityOutcomeRequired ≡ true
    affectedCommunityAuthorityRequired : Bool
    affectedCommunityAuthorityRequiredIsTrue : affectedCommunityAuthorityRequired ≡ true
    institutionalSelfReportSufficient : Bool
    institutionalSelfReportSufficientIsFalse : institutionalSelfReportSufficient ≡ false
    consultationCountSufficient : Bool
    consultationCountSufficientIsFalse : consultationCountSufficient ≡ false
    correctionMustChangeRealisedOperation : Bool
    correctionMustChangeRealisedOperationIsTrue :
      correctionMustChangeRealisedOperation ≡ true
    preventionMustBeObserved : Bool
    preventionMustBeObservedIsTrue : preventionMustBeObserved ≡ true
    planReference : String

open CommunityAuthorityFirstCorrectionPlan public

canonicalCommunityAuthorityFirstPlan : CommunityAuthorityFirstCorrectionPlan
canonicalCommunityAuthorityFirstPlan = community-authority-first-correction-plan
  obtainCommunityDefinedOutcomeStage refl
  true refl
  true refl
  false refl
  false refl
  true refl
  true refl
  "Current Country operational residual ordering: obtain affected-community-defined outcome, preserve authority, test whether institutional correction changes operation, then verify material effect and recurrence prevention."

------------------------------------------------------------------------
-- Two-Eyed Seeing and Indigenous-knowledge nonfusion.
------------------------------------------------------------------------

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

sharedObservationDoesNotFuseEpistemicHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory twoEyedBoundary ≡ false
sharedObservationDoesNotFuseEpistemicHistory = refl

coordinationDoesNotRequireFusion :
  TwoEyed.coordinatedUseRequiresEpistemicFusion twoEyedBoundary ≡ false
coordinationDoesNotRequireFusion = refl

extractedPropositionCannotRecoverCommunityAuthority :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    IK.extractedProposition IK.authority → ⊥
extractedPropositionCannotRecoverCommunityAuthority = IK.propositionCannotRecoverAuthority

communityOutcomeEvidenceUsesCommunityStrand :
  Braid.evidenceStrand Braid.communityOutcomePaymentCandidate
  ≡ Braid.affectedCommunityOutcomeStrand
communityOutcomeEvidenceUsesCommunityStrand = refl

communityEvidenceDoesNotTransferAuthority :
  Braid.paymentAutomaticallyTransfersAuthority Braid.communityOutcomePaymentCandidate ≡ false
communityEvidenceDoesNotTransferAuthority = refl

------------------------------------------------------------------------
-- HRC remedy means remain coordinate-specific; no fake scalar odds.
------------------------------------------------------------------------

compensationProspect : Remedy.PracticalProspectReceipt
compensationProspect = Remedy.compensationProspect

consultationProspect : Remedy.PracticalProspectReceipt
consultationProspect = Remedy.consultationProspect

safeExistenceProspect : Remedy.PracticalProspectReceipt
safeExistenceProspect = Remedy.safeExistenceProspect

compensationHasDirectMechanismButNoPublicClosureReceipt :
  Remedy.directMechanismExists compensationProspect ≡ true
compensationHasDirectMechanismButNoPublicClosureReceipt = refl

compensationPublicEvidenceDoesNotFullyCloseCoordinate :
  Remedy.publicEvidenceFullyClosesCoordinate compensationProspect ≡ false
compensationPublicEvidenceDoesNotFullyCloseCoordinate = refl

consultationPublicEvidenceDoesNotFullyCloseCoordinate :
  Remedy.publicEvidenceFullyClosesCoordinate consultationProspect ≡ false
consultationPublicEvidenceDoesNotFullyCloseCoordinate = refl

safeExistencePublicEvidenceDoesNotFullyCloseCoordinate :
  Remedy.publicEvidenceFullyClosesCoordinate safeExistenceProspect ≡ false
safeExistencePublicEvidenceDoesNotFullyCloseCoordinate = refl

compensationNextProducer :
  Remedy.nextProducer Billy.adequateCompensation
  ≡ Remedy.recoverCompensationExecutionReceipt
compensationNextProducer = refl

consultationNextProducer :
  Remedy.nextProducer Billy.meaningfulConsultation
  ≡ Remedy.recoverCommunityDefinedNeedsReceipt
consultationNextProducer = refl

monitoringNextProducer :
  Remedy.nextProducer Billy.monitoringAndReview
  ≡ Remedy.recoverCorrectionLoopReceipt
monitoringNextProducer = refl

preventionNextProducer :
  Remedy.nextProducer Billy.preventionOfSimilarViolations
  ≡ Remedy.recoverPreventionOutcomeReceipt
preventionNextProducer = refl

------------------------------------------------------------------------
-- System-is-what-it-does operational discrepancy surface.
------------------------------------------------------------------------

operationalDiscrepancyBoundary : Discrepancy.OperationalDiscrepancyBoundary
operationalDiscrepancyBoundary = Discrepancy.canonicalOperationalDiscrepancyBoundary

stateReportHasNoMetaObserverPriority :
  Discrepancy.stateReportGetsMetaObserverPriorityByDefault operationalDiscrepancyBoundary ≡ false
stateReportHasNoMetaObserverPriority = refl

repeatedOperationMayReopenDeclaredSuccess :
  Discrepancy.repeatedOperationMayReopenDeclaredSuccess operationalDiscrepancyBoundary ≡ true
repeatedOperationMayReopenDeclaredSuccess = refl

correctionResponseCountsAsSystemOperation :
  Discrepancy.correctionResponseCountsAsSystemOperation operationalDiscrepancyBoundary ≡ true
correctionResponseCountsAsSystemOperation = refl

communityOutcomeIsIndependentClosureCoordinate :
  Discrepancy.affectedCommunityOutcomeCanBeIndependentClosureCoordinate
    operationalDiscrepancyBoundary ≡ true
communityOutcomeIsIndependentClosureCoordinate = refl

------------------------------------------------------------------------
-- Current source-bounded status.
------------------------------------------------------------------------

currentFullOperationalClosureStillImpossible :
  Operational.FullOperationalClosure Audit.currentCountryOperationalSnapshot → ⊥
currentFullOperationalClosureStillImpossible = Audit.currentFullOperationalClosureImpossible

record CurrentCountryCorrectionState : Set where
  constructor current-country-correction-state
  field
    doctrinalCorrectionExists : Bool
    realisedEffectFullyClosed : Bool
    communityOutcomeClosed : Bool
    communityAuthorityClosed : Bool
    correctionResponseClosed : Bool
    recurrencePreventionClosed : Bool
    sourceBoundedReading : String

open CurrentCountryCorrectionState public

currentCountryCorrectionState : CurrentCountryCorrectionState
currentCountryCorrectionState = current-country-correction-state
  true
  false
  false
  false
  false
  false
  "Current source-bounded operational state: doctrinal correction is real, but realised effect is partial and community-defined outcome, community authority, correction response and recurrence-prevention closure remain unpaid or unresolved."

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data StateRecognitionEqualsCommunityAuthority : Set where
data StateConsultationCountEqualsMeaningfulConsultation : Set where
data HRCViewGuaranteesDomesticExecution : Set where
data DirectImplementationMechanismMeansOutcomeCertain : Set where
data DoctrinalCorrectionMeansOperationalClosure : Set where
data CommunityAuthorityMeansEpistemicFusion : Set where

stateRecognitionDoesNotEqualCommunityAuthority : StateRecognitionEqualsCommunityAuthority → ⊥
stateRecognitionDoesNotEqualCommunityAuthority ()

consultationCountDoesNotEqualMeaningfulConsultation :
  StateConsultationCountEqualsMeaningfulConsultation → ⊥
consultationCountDoesNotEqualMeaningfulConsultation ()

hrcViewDoesNotGuaranteeDomesticExecution : HRCViewGuaranteesDomesticExecution → ⊥
hrcViewDoesNotGuaranteeDomesticExecution ()

directMechanismDoesNotMakeOutcomeCertain : DirectImplementationMechanismMeansOutcomeCertain → ⊥
directMechanismDoesNotMakeOutcomeCertain ()

doctrinalCorrectionDoesNotMeanOperationalClosure : DoctrinalCorrectionMeansOperationalClosure → ⊥
doctrinalCorrectionDoesNotMeanOperationalClosure ()

communityAuthorityDoesNotRequireEpistemicFusion : CommunityAuthorityMeansEpistemicFusion → ⊥
communityAuthorityDoesNotRequireEpistemicFusion ()
