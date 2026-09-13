module DASHI.Cognition.PNF.SensibLawCountryPluralEpistemicOperationalAuditExact where

------------------------------------------------------------------------
-- COUNTRY / PLURAL EPISTEMIC OPERATIONAL AUDIT
--
-- This owner compiles current-master SensibLaw residuals into the generic
-- plural operational closure machinery.  It does not create new historical or
-- empirical source propositions.  Existing Mabo, Billy, Two-Eyed Seeing,
-- Indigenous-knowledge and POSIWID source attributions remain upstream.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Cognition.PNF.SensibLawCountrySystemFunctionTwoEyedRemedyRealisationExact as Function
import DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact as Continuity
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek

------------------------------------------------------------------------
-- Current-master source/state anchors.
------------------------------------------------------------------------

maboCorrectionWasRealButIncomplete : Country.CorrectionWithoutFullRepair
maboCorrectionWasRealButIncomplete = Country.currentCorrectionWithoutFullRepair

nativeTitleDidNotCompleteEqualSovereignty :
  Country.currentOperationalJusticeState Country.equalSovereignRelation
  ≡ Country.residualOpen
nativeTitleDidNotCompleteEqualSovereignty = refl

landCountryControlStillOpen :
  Country.currentOperationalJusticeState Country.landAndCountryControl
  ≡ Country.residualOpen
landCountryControlStillOpen = refl

compensationStillOpen :
  Country.currentOperationalJusticeState Country.compensationAndReparation
  ≡ Country.residualOpen
compensationStillOpen = refl

communityDefinedNeedStillOpen :
  Country.currentOperationalJusticeState Country.communityDefinedNeedSatisfaction
  ≡ Country.residualOpen
communityDefinedNeedStillOpen = refl

materialSafetyStillSourceUnresolved :
  Country.currentOperationalJusticeState Country.materialSafety
  ≡ Country.sourceStateUnresolved
materialSafetyStillSourceUnresolved = refl

culturalContinuityStillSourceUnresolved :
  Country.currentOperationalJusticeState Country.culturalContinuity
  ≡ Country.sourceStateUnresolved
culturalContinuityStillSourceUnresolved = refl

billyFullReparationResidualStillLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
billyFullReparationResidualStillLive = refl

------------------------------------------------------------------------
-- Current plural operational closure snapshot.
------------------------------------------------------------------------

currentStateFor : Operational.OperationalClosureCoordinate → Operational.OperationalClosureState
currentStateFor Operational.declaredCommitmentCoordinate = Operational.coordinatePaid
currentStateFor Operational.realisedEffectCoordinate = Operational.coordinatePartial
currentStateFor Operational.communityDefinedOutcomeCoordinate = Operational.coordinateOpen
currentStateFor Operational.communityAuthorityCoordinate = Operational.coordinateOpen
currentStateFor Operational.independentMonitoringCoordinate = Operational.coordinatePartial
currentStateFor Operational.correctionResponseCoordinate = Operational.coordinateOpen
currentStateFor Operational.preventionOfRecurrenceCoordinate = Operational.coordinateSourceUnresolved

currentCountryOperationalSnapshot : Operational.OperationalClosureSnapshot
currentCountryOperationalSnapshot = Operational.operational-closure-snapshot
  currentStateFor
  "Current-master Country/Mabo/Billy operational closure snapshot compiled from existing source-bounded residual owners; no new historical proposition is introduced here."

currentCommunityOutcomeOpen :
  Operational.stateFor currentCountryOperationalSnapshot
    Operational.communityDefinedOutcomeCoordinate
  ≡ Operational.coordinateOpen
currentCommunityOutcomeOpen = refl

currentCommunityAuthorityOpen :
  Operational.stateFor currentCountryOperationalSnapshot
    Operational.communityAuthorityCoordinate
  ≡ Operational.coordinateOpen
currentCommunityAuthorityOpen = refl

currentCorrectionResponseOpen :
  Operational.stateFor currentCountryOperationalSnapshot
    Operational.correctionResponseCoordinate
  ≡ Operational.coordinateOpen
currentCorrectionResponseOpen = refl

currentPreventionSourceUnresolved :
  Operational.stateFor currentCountryOperationalSnapshot
    Operational.preventionOfRecurrenceCoordinate
  ≡ Operational.coordinateSourceUnresolved
currentPreventionSourceUnresolved = refl

currentFullOperationalClosureImpossible :
  Operational.FullOperationalClosure currentCountryOperationalSnapshot → ⊥
currentFullOperationalClosureImpossible closure with
  Operational.communityAuthorityPaid closure
... | ()

------------------------------------------------------------------------
-- Operational system classification: real doctrinal correction can coexist
-- with a still-untransformed or partially transformed material relation.
------------------------------------------------------------------------

currentOperationalRelation : Operational.OperationalRelationReceipt
currentOperationalRelation = Operational.operational-relation-receipt
  true
  true
  false
  false
  false
  true
  Operational.partialOperationalCorrection
  false refl
  "Current-master synthesis: major doctrinal correction and implementation activity are real; the tracked equal-sovereignty, land/Country-control, compensation, community-authority and correction/prevention consumers are not all closed. Classification is operational and does not prove private motive."

currentClassificationIsPartialOperationalCorrection :
  Operational.classification currentOperationalRelation
  ≡ Operational.partialOperationalCorrection
currentClassificationIsPartialOperationalCorrection = refl

currentClassificationDoesNotProvePrivateIntent :
  Operational.privateIntentProved currentOperationalRelation ≡ false
currentClassificationDoesNotProvePrivateIntent = refl

------------------------------------------------------------------------
-- Two-Eyed Seeing / Indigenous knowledge: State observation and community
-- outcome/authority stay separate strands.
------------------------------------------------------------------------

pluralAssessment : Operational.PluralEvidenceAssessment
pluralAssessment = Operational.canonicalPluralEvidenceAssessment

stateObservationDoesNotExhaustCommunityOutcome :
  Operational.institutionalObservationExhaustsCommunityOutcome pluralAssessment ≡ false
stateObservationDoesNotExhaustCommunityOutcome = refl

communityOutcomeMayReopenInstitutionalAssessment :
  Operational.communityOutcomeMayReopenInstitutionalAssessment pluralAssessment ≡ true
communityOutcomeMayReopenInstitutionalAssessment = refl

sharedObservationDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistory = refl

extractedPropositionCannotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionCannotRecoverCommunityAuthority = IK.propositionCannotRecoverAuthority

consultationSurfaceCannotRecoverCommunityOutcome :
  INF.FactorsThrough
    Remedy.administrativeConsultationObserver
    Remedy.communityConsultationOutcome → ⊥
consultationSurfaceCannotRecoverCommunityOutcome =
  Remedy.administrativeConsultationCannotRecoverCommunityOutcome

------------------------------------------------------------------------
-- Structural continuity: rejecting terra nullius is not enough to prove that
-- the relation by which the State defines and corrects Indigenous authority has
-- materially transformed.
------------------------------------------------------------------------

doctrineRejectedButLandControlOpen :
  Continuity.currentCoordinateState Continuity.doctrineRejected ≡ Continuity.paid
doctrineRejectedButLandControlOpen = refl

landControlResidualSurvivesDoctrinalRejection :
  Continuity.currentCoordinateState Continuity.landCountryControl ≡ Continuity.open
landControlResidualSurvivesDoctrinalRejection = refl

communityAuthorityResidualSurvivesDoctrinalRejection :
  Continuity.currentCoordinateState Continuity.communityAuthorityBearing ≡ Continuity.open
communityAuthorityResidualSurvivesDoctrinalRejection = refl

doctrinalRejectionOnlyCanStillCarryStructuralContinuityRisk :
  Continuity.classifyTransformation Continuity.doctrinalRejectionOnlyFixture
  ≡ Continuity.structuralContinuityRisk
doctrinalRejectionOnlyCanStillCarryStructuralContinuityRisk = refl

------------------------------------------------------------------------
-- BIDI routing from open operational coordinate to next producer.
------------------------------------------------------------------------

data CountryOperationalResidual : Set where
  landCountryControlResidual
  communityAuthorityResidual
  compensationResidual
  correctionLoopResidual
  preventionEvidenceResidual
  : CountryOperationalResidual

producerForResidual : CountryOperationalResidual → Operational.OperationalProducer
producerForResidual landCountryControlResidual = Operational.realisedOutcomeProducer
producerForResidual communityAuthorityResidual = Operational.communityAuthorityProducer
producerForResidual compensationResidual = Operational.realisedOutcomeProducer
producerForResidual correctionLoopResidual = Operational.correctionLoopProducer
producerForResidual preventionEvidenceResidual = Operational.recurrencePreventionProducer

landResidualRoutesToRealisedOutcome :
  producerForResidual landCountryControlResidual ≡ Operational.realisedOutcomeProducer
landResidualRoutesToRealisedOutcome = refl

communityAuthorityRoutesToAuthorityProducer :
  producerForResidual communityAuthorityResidual ≡ Operational.communityAuthorityProducer
communityAuthorityRoutesToAuthorityProducer = refl

correctionResidualRoutesToCorrectionLoop :
  producerForResidual correctionLoopResidual ≡ Operational.correctionLoopProducer
correctionResidualRoutesToCorrectionLoop = refl

------------------------------------------------------------------------
-- Correction-channel / Amalek frontier remains a separate, stronger test.
------------------------------------------------------------------------

amalekClosedLoop : Amalek.ClosedAuthorityLoop
amalekClosedLoop = Amalek.canonicalClosedAuthorityRisk

amalekClosedLoopHasNoIndependentCorrection :
  Amalek.correctionChannelIndependent amalekClosedLoop ≡ false
amalekClosedLoopHasNoIndependentCorrection = refl

currentTerraNulliusClosureEvidenceNotPaidByDefault :
  Continuity.currentTerraNulliusClosureEvidence Continuity.independentCorrectionClosed
  ≡ Continuity.notYetPaid
currentTerraNulliusClosureEvidenceNotPaidByDefault = refl

------------------------------------------------------------------------
-- Dominant-chart cross-pollination: a State-authored success surface can be a
-- locally useful observer without carrying the full Country/community outcome.
------------------------------------------------------------------------

data StateSuccessSurface : Set where stateReportsProgress : StateSuccessSurface
data CountryOutcomeState : Set where
  sameStateReportResidualOpen
  sameStateReportMateriallyTransformed
  : CountryOutcomeState
data CountryMaterialOutcome : Set where
  materialRelationResidual
  materialRelationTransformed
  : CountryMaterialOutcome

stateSuccessObserver : CountryOutcomeState → StateSuccessSurface
stateSuccessObserver _ = stateReportsProgress

countryMaterialOutcome : CountryOutcomeState → CountryMaterialOutcome
countryMaterialOutcome sameStateReportResidualOpen = materialRelationResidual
countryMaterialOutcome sameStateReportMateriallyTransformed = materialRelationTransformed

countryOutcomesDiffer :
  countryMaterialOutcome sameStateReportResidualOpen
  ≡ countryMaterialOutcome sameStateReportMateriallyTransformed → ⊥
countryOutcomesDiffer ()

stateSuccessCannotRecoverCountryOutcomeWitness :
  INF.NonFactorabilityWitness stateSuccessObserver countryMaterialOutcome
stateSuccessCannotRecoverCountryOutcomeWitness = INF.nonFactorabilityWitness
  sameStateReportResidualOpen
  sameStateReportMateriallyTransformed
  refl
  countryOutcomesDiffer

stateSuccessCompression :
  Compression.ProjectionInadequacyReceipt stateSuccessObserver countryMaterialOutcome
stateSuccessCompression = Compression.projection-inadequacy-receipt
  Compression.juridicalRecognitionCompression
  "State-authored success/progress report surface"
  "Country/community material-justice consumer"
  "same institutional success surface can coexist with open or transformed Country/material relation"
  stateSuccessCannotRecoverCountryOutcomeWitness
  true refl
  false refl
  false refl
  false refl

stateSuccessSurfaceCannotCarryCountryOutcome :
  INF.FactorsThrough stateSuccessObserver countryMaterialOutcome → ⊥
stateSuccessSurfaceCannotCarryCountryOutcome =
  Compression.projectionCannotFactorTarget stateSuccessCompression

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data MaboCorrectionEqualsOperationalDecolonisation : Set where
data StateProgressReportClosesCountryOutcome : Set where
data ConsultationTransfersCommunityAuthority : Set where
data TwoEyedCoordinationMeansStateEpistemicSupremacy : Set where
data OpenCorrectionResidualProvesAmalekClosure : Set where
data CommunityDisagreementAutomaticallyInvalidatesStateEvidence : Set where

maboCorrectionDoesNotEqualOperationalDecolonisation :
  MaboCorrectionEqualsOperationalDecolonisation → ⊥
maboCorrectionDoesNotEqualOperationalDecolonisation ()

stateProgressDoesNotCloseCountryOutcome : StateProgressReportClosesCountryOutcome → ⊥
stateProgressDoesNotCloseCountryOutcome ()

consultationDoesNotTransferCommunityAuthority : ConsultationTransfersCommunityAuthority → ⊥
consultationDoesNotTransferCommunityAuthority ()

twoEyedCoordinationDoesNotCreateStateSupremacy :
  TwoEyedCoordinationMeansStateEpistemicSupremacy → ⊥
twoEyedCoordinationDoesNotCreateStateSupremacy ()

openCorrectionResidualDoesNotByItselfProveAmalekClosure :
  OpenCorrectionResidualProvesAmalekClosure → ⊥
openCorrectionResidualDoesNotByItselfProveAmalekClosure ()

communityDisagreementDoesNotAutomaticallyEraseStateEvidence :
  CommunityDisagreementAutomaticallyInvalidatesStateEvidence → ⊥
communityDisagreementDoesNotAutomaticallyEraseStateEvidence ()
