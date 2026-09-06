module DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact where

------------------------------------------------------------------------
-- COUNTRY / SYSTEM / REALISED JUSTICE BIDI
--
-- Cross-pollinates current-master owners rather than duplicating them:
--   * relation-indexed terra-nullius juridical erasure;
--   * Native Title recognition/domination residual;
--   * Billy effective-remedy implementation;
--   * POSIWID operational semantics;
--   * Two-Eyed Seeing / Indigenous knowledge provenance and authority.
--
-- The resulting trajectory is a DASHI/SensibLaw synthesis. Individual source
-- authors are not credited with the combined system model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Personhood
import DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionDominationResidualExact as NativeTitle
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- System trajectory coordinates.
------------------------------------------------------------------------

data SystemMoment : Set where
  terraNulliusFoundationalOperation
  maboDoctrinalCorrection
  nativeTitleMediatedRecognition
  effectiveRemedyImplementation
  : SystemMoment

data JuridicalRelationState : Set where
  foundationalJuridicalErasure
  doctrinalRecognitionWithoutEqualSovereignty
  crownMediatedRecognitionResidual
  materialJusticeResidualLive
  relationTransformed
  : JuridicalRelationState

data CorrectionDepth : Set where
  noCorrection
  doctrinalCorrection
  implementationPartialCorrection
  materialRelationTransformation
  : CorrectionDepth

relationState : SystemMoment → JuridicalRelationState
relationState terraNulliusFoundationalOperation = foundationalJuridicalErasure
relationState maboDoctrinalCorrection = doctrinalRecognitionWithoutEqualSovereignty
relationState nativeTitleMediatedRecognition = crownMediatedRecognitionResidual
relationState effectiveRemedyImplementation = materialJusticeResidualLive

correctionDepth : SystemMoment → CorrectionDepth
correctionDepth terraNulliusFoundationalOperation = noCorrection
correctionDepth maboDoctrinalCorrection = doctrinalCorrection
correctionDepth nativeTitleMediatedRecognition = doctrinalCorrection
correctionDepth effectiveRemedyImplementation = implementationPartialCorrection

------------------------------------------------------------------------
-- Exact current-master anchors.
------------------------------------------------------------------------

terraNulliusWasFoundationalJuridicalErasure :
  Personhood.personhoodState Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ Personhood.juridicallyErasedActor
terraNulliusWasFoundationalJuridicalErasure = refl

nativeTitleWasMajorDoctrinalAdvance :
  NativeTitle.NativeTitleWasMajorLegalAdvance NativeTitle.canonicalNativeTitleCriticalBoundary ≡ true
nativeTitleWasMajorDoctrinalAdvance = refl

nativeTitleDidNotCreateEqualSovereignRelation :
  NativeTitle.equalSovereignRelationCreated NativeTitle.currentNativeTitleInstitutionalRelationState ≡ false
nativeTitleDidNotCreateEqualSovereignRelation = refl

nativeTitleDidNotCompleteLandReturn :
  NativeTitle.landReturnCompleted NativeTitle.currentNativeTitleInstitutionalRelationState ≡ false
nativeTitleDidNotCompleteLandReturn = refl

nativeTitleDidNotCompleteMaterialRepair :
  NativeTitle.materialRepairCompleted NativeTitle.currentNativeTitleInstitutionalRelationState ≡ false
nativeTitleDidNotCompleteMaterialRepair = refl

nativeTitleDidNotCompleteInstitutionalRelationTransformation :
  NativeTitle.relationTransformationCompleted NativeTitle.currentNativeTitleInstitutionalRelationState ≡ false
nativeTitleDidNotCompleteInstitutionalRelationTransformation = refl

billyFullReparationResidualStillLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
billyFullReparationResidualStillLive = refl

------------------------------------------------------------------------
-- A system's correction response is itself part of the system's operation.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

correctionResponseIsObservableSystemBehaviour :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
correctionResponseIsObservableSystemBehaviour = refl

declaredPurposeCannotOverrideRepeatedRealizedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeCannotOverrideRepeatedRealizedEffect = refl

------------------------------------------------------------------------
-- Doctrinal correction is real correction, but not identical to material repair.
------------------------------------------------------------------------

record CorrectionWithoutFullRepair : Set where
  constructor correction-without-full-repair
  field
    doctrinalCorrectionOccurred : Bool
    doctrinalCorrectionOccurredIsTrue : doctrinalCorrectionOccurred ≡ true
    foundationalDoctrineRejected : Bool
    foundationalDoctrineRejectedIsTrue : foundationalDoctrineRejected ≡ true
    equalSovereignRelationRealised : Bool
    equalSovereignRelationRealisedIsFalse : equalSovereignRelationRealised ≡ false
    landReturnRealised : Bool
    landReturnRealisedIsFalse : landReturnRealised ≡ false
    materialRepairRealised : Bool
    materialRepairRealisedIsFalse : materialRepairRealised ≡ false
    fullEffectiveRemedyPubliclyClosed : Bool
    fullEffectiveRemedyPubliclyClosedIsFalse : fullEffectiveRemedyPubliclyClosed ≡ false
    systemReading : String

open CorrectionWithoutFullRepair public

currentCorrectionWithoutFullRepair : CorrectionWithoutFullRepair
currentCorrectionWithoutFullRepair = correction-without-full-repair
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  "Operational synthesis: the legal system made a major doctrinal correction in Mabo, while equal sovereign standing, land return, material repair and the currently tracked Billy full-reparation consumer remain unclosed. Correction is part of what the system does; so are the residuals it continues to produce or fail to repair."

------------------------------------------------------------------------
-- Two-Eyed Seeing: State implementation reports and affected-community realised
-- outcomes remain distinct strands with distinct authority/provenance.
------------------------------------------------------------------------

data RemedyKnowledgeStrand : Set where
  stateImplementationStrand
  affectedCommunityOutcomeStrand
  independentMonitoringStrand
  treatyBodyAssessmentStrand
  : RemedyKnowledgeStrand

record BraidedRemedyAssessment : Set where
  constructor braided-remedy-assessment
  field
    stateStrand : RemedyKnowledgeStrand
    communityStrand : RemedyKnowledgeStrand
    monitoringStrand : RemedyKnowledgeStrand
    stateObservationExhaustsCommunityOutcome : Bool
    stateObservationExhaustsCommunityOutcomeIsFalse :
      stateObservationExhaustsCommunityOutcome ≡ false
    sharedObservationFusesAuthority : Bool
    sharedObservationFusesAuthorityIsFalse : sharedObservationFusesAuthority ≡ false
    communityOutcomeCanReopenImplementation : Bool
    communityOutcomeCanReopenImplementationIsTrue :
      communityOutcomeCanReopenImplementation ≡ true
    correctionLoopRequiredForOperationalClosure : Bool
    correctionLoopRequiredForOperationalClosureIsTrue :
      correctionLoopRequiredForOperationalClosure ≡ true

open BraidedRemedyAssessment public

canonicalBraidedRemedyAssessment : BraidedRemedyAssessment
canonicalBraidedRemedyAssessment = braided-remedy-assessment
  stateImplementationStrand
  affectedCommunityOutcomeStrand
  independentMonitoringStrand
  false refl
  false refl
  true refl
  true refl

sharedObservationStillDoesNotFuseProvenance :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationStillDoesNotFuseProvenance = refl

extractedPropositionDoesNotRecoverAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionDoesNotRecoverAuthority = IK.propositionCannotRecoverAuthority

administrativeConsultationDoesNotRecoverCommunityOutcome :
  INF.FactorsThrough
    Remedy.administrativeConsultationObserver Remedy.communityConsultationOutcome → ⊥
administrativeConsultationDoesNotRecoverCommunityOutcome =
  Remedy.administrativeConsultationCannotRecoverCommunityOutcome

------------------------------------------------------------------------
-- Operational justice consumer: what must be realised, not merely declared.
------------------------------------------------------------------------

data OperationalJusticeCoordinate : Set where
  juridicalHumanityAndStanding
  indigenousLawAuthorityContinuity
  equalSovereignRelation
  landAndCountryControl
  materialSafety
  culturalContinuity
  compensationAndReparation
  communityDefinedNeedSatisfaction
  correctionAndPrevention
  : OperationalJusticeCoordinate

data OperationalJusticeState : Set where
  realised
  partiallyRealised
  residualOpen
  sourceStateUnresolved
  : OperationalJusticeState

currentOperationalJusticeState : OperationalJusticeCoordinate → OperationalJusticeState
currentOperationalJusticeState juridicalHumanityAndStanding = partiallyRealised
currentOperationalJusticeState indigenousLawAuthorityContinuity = partiallyRealised
currentOperationalJusticeState equalSovereignRelation = residualOpen
currentOperationalJusticeState landAndCountryControl = residualOpen
currentOperationalJusticeState materialSafety = sourceStateUnresolved
currentOperationalJusticeState culturalContinuity = sourceStateUnresolved
currentOperationalJusticeState compensationAndReparation = residualOpen
currentOperationalJusticeState communityDefinedNeedSatisfaction = residualOpen
currentOperationalJusticeState correctionAndPrevention = sourceStateUnresolved

equalSovereigntyRemainsOperationalResidual :
  currentOperationalJusticeState equalSovereignRelation ≡ residualOpen
equalSovereigntyRemainsOperationalResidual = refl

landAndCountryControlRemainsOperationalResidual :
  currentOperationalJusticeState landAndCountryControl ≡ residualOpen
landAndCountryControlRemainsOperationalResidual = refl

materialSafetyOutcomeRemainsUnresolved :
  currentOperationalJusticeState materialSafety ≡ sourceStateUnresolved
materialSafetyOutcomeRemainsUnresolved = refl

culturalContinuityOutcomeRemainsUnresolved :
  currentOperationalJusticeState culturalContinuity ≡ sourceStateUnresolved
culturalContinuityOutcomeRemainsUnresolved = refl

compensationRemainsOperationalResidual :
  currentOperationalJusticeState compensationAndReparation ≡ residualOpen
compensationRemainsOperationalResidual = refl

------------------------------------------------------------------------
-- BIDI route from operational residual to producer/action.
------------------------------------------------------------------------

data OperationalJusticeProducer : Set where
  indigenousSovereigntyRelationProducer
  landReturnOrControlProducer
  compensationExecutionProducer
  communityDefinedNeedsProducer
  realisedSafetyOutcomeProducer
  culturalContinuityOutcomeProducer
  correctionLoopProducer
  : OperationalJusticeProducer

producerFor : OperationalJusticeCoordinate → OperationalJusticeProducer
producerFor juridicalHumanityAndStanding = indigenousSovereigntyRelationProducer
producerFor indigenousLawAuthorityContinuity = indigenousSovereigntyRelationProducer
producerFor equalSovereignRelation = indigenousSovereigntyRelationProducer
producerFor landAndCountryControl = landReturnOrControlProducer
producerFor materialSafety = realisedSafetyOutcomeProducer
producerFor culturalContinuity = culturalContinuityOutcomeProducer
producerFor compensationAndReparation = compensationExecutionProducer
producerFor communityDefinedNeedSatisfaction = communityDefinedNeedsProducer
producerFor correctionAndPrevention = correctionLoopProducer

landResidualRoutesToLandControlProducer :
  producerFor landAndCountryControl ≡ landReturnOrControlProducer
landResidualRoutesToLandControlProducer = refl

compensationResidualRoutesToExecutionProducer :
  producerFor compensationAndReparation ≡ compensationExecutionProducer
compensationResidualRoutesToExecutionProducer = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DoctrinalCorrectionEqualsMaterialRepair : Set where
data RecognitionEqualsEqualSovereignty : Set where
data StateImplementationReportEqualsCommunityDefinedSuccess : Set where
data ConsultationEqualsAuthorityTransfer : Set where
data MonitoringWithoutCorrectionClosesOperationalRemedy : Set where
data HistoricalCorrectionErasesHistoricalOperation : Set where

doctrinalCorrectionDoesNotEqualMaterialRepair : DoctrinalCorrectionEqualsMaterialRepair → ⊥
doctrinalCorrectionDoesNotEqualMaterialRepair ()

recognitionDoesNotEqualEqualSovereignty : RecognitionEqualsEqualSovereignty → ⊥
recognitionDoesNotEqualEqualSovereignty ()

stateReportDoesNotEqualCommunityDefinedSuccess :
  StateImplementationReportEqualsCommunityDefinedSuccess → ⊥
stateReportDoesNotEqualCommunityDefinedSuccess ()

consultationDoesNotTransferAuthority : ConsultationEqualsAuthorityTransfer → ⊥
consultationDoesNotTransferAuthority ()

monitoringWithoutCorrectionDoesNotCloseRemedy :
  MonitoringWithoutCorrectionClosesOperationalRemedy → ⊥
monitoringWithoutCorrectionDoesNotCloseRemedy ()

laterCorrectionDoesNotErasePriorSystemOperation :
  HistoricalCorrectionErasesHistoricalOperation → ⊥
laterCorrectionDoesNotErasePriorSystemOperation ()
