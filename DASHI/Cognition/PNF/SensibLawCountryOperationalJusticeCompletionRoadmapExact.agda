module DASHI.Cognition.PNF.SensibLawCountryOperationalJusticeCompletionRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.PluralOperationalResidualActionLoopExact as Adaptive
import DASHI.Cognition.PNF.SensibLawCountryPluralEpistemicOperationalAuditExact as Audit
import DASHI.Cognition.PNF.SensibLawCountryTwoEyedOperationalAdaptiveEverything as Country
import DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationTwoEyedPOSIWIDEverything as Incarceration
import DASHI.Cognition.PNF.SensibLawTerraNulliusOperationalJuridicalNonHumanityExact as Terra

------------------------------------------------------------------------
-- COMPLETION ROADMAP
--
-- "Complete" is consumer-relative. This owner distinguishes:
--   (1) formal architecture completion;
--   (2) source/evidence mapping completion;
--   (3) realised operational-justice closure.
--
-- The third cannot be manufactured by more formalisation alone: it requires
-- affected-community-defined outcomes, authority-bearing participation,
-- realised material correction, independent monitoring and demonstrated
-- prevention of recurrence.
------------------------------------------------------------------------

data CompletionLayer : Set where
  formalArchitectureLayer
  sourceMappingLayer
  communityOutcomeLayer
  communityAuthorityLayer
  correctionResponseLayer
  realisedEffectLayer
  independentMonitoringLayer
  recurrencePreventionLayer
  : CompletionLayer

data CompletionState : Set where
  paid
  partial
  open
  sourceUnresolved
  externallyDependent
  : CompletionState

currentCompletionState : CompletionLayer → CompletionState
currentCompletionState formalArchitectureLayer = paid
currentCompletionState sourceMappingLayer = partial
currentCompletionState communityOutcomeLayer = open
currentCompletionState communityAuthorityLayer = open
currentCompletionState correctionResponseLayer = open
currentCompletionState realisedEffectLayer = partial
currentCompletionState independentMonitoringLayer = partial
currentCompletionState recurrencePreventionLayer = sourceUnresolved

formalArchitectureIsPaid : currentCompletionState formalArchitectureLayer ≡ paid
formalArchitectureIsPaid = refl

communityOutcomeIsFirstOpenLayer : currentCompletionState communityOutcomeLayer ≡ open
communityOutcomeIsFirstOpenLayer = refl

communityAuthorityStillOpen : currentCompletionState communityAuthorityLayer ≡ open
communityAuthorityStillOpen = refl

recurrencePreventionStillSourceUnresolved :
  currentCompletionState recurrencePreventionLayer ≡ sourceUnresolved
recurrencePreventionStillSourceUnresolved = refl

------------------------------------------------------------------------
-- Exact current operational coordinates inherited from the live snapshot.
------------------------------------------------------------------------

declaredCommitmentPaid :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.declaredCommitmentCoordinate
  ≡ Operational.coordinatePaid
declaredCommitmentPaid = refl

realisedEffectPartial :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.realisedEffectCoordinate
  ≡ Operational.coordinatePartial
realisedEffectPartial = refl

communityOutcomeOpen :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.communityDefinedOutcomeCoordinate
  ≡ Operational.coordinateOpen
communityOutcomeOpen = refl

communityAuthorityOpen :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.communityAuthorityCoordinate
  ≡ Operational.coordinateOpen
communityAuthorityOpen = refl

monitoringPartial :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.independentMonitoringCoordinate
  ≡ Operational.coordinatePartial
monitoringPartial = refl

correctionResponseOpen :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.correctionResponseCoordinate
  ≡ Operational.coordinateOpen
correctionResponseOpen = refl

preventionSourceUnresolved :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.preventionOfRecurrenceCoordinate
  ≡ Operational.coordinateSourceUnresolved
preventionSourceUnresolved = refl

------------------------------------------------------------------------
-- Least-privilege completion order.
------------------------------------------------------------------------

data CompletionAction : Set where
  obtainAffectedCommunityDefinedOutcome
  establishCommunityAuthorityReceipt
  identifyRequiredInstitutionalCorrection
  observeCorrectionInRealisedOperation
  verifyIndependentMonitoring
  verifyPreventionOfRecurrence
  reassessFullOperationalClosure
  : CompletionAction

firstCompletionAction : CompletionAction
firstCompletionAction = obtainAffectedCommunityDefinedOutcome

firstCompletionActionExact :
  Adaptive.defaultActionFor Adaptive.communityOutcomeResidual
  ≡ Adaptive.obtainAffectedCommunityOutcome
firstCompletionActionExact = Country.currentDefaultAction

nextActionAfterCommunityOutcome : CompletionAction
nextActionAfterCommunityOutcome = establishCommunityAuthorityReceipt

nextActionAfterAuthority : CompletionAction
nextActionAfterAuthority = identifyRequiredInstitutionalCorrection

nextActionAfterCorrection : CompletionAction
nextActionAfterCorrection = observeCorrectionInRealisedOperation

------------------------------------------------------------------------
-- Completion contracts.
------------------------------------------------------------------------

record OperationalJusticeCompletionContract : Set where
  constructor operational-justice-completion-contract
  field
    communityDefinesOutcome : Bool
    communityAuthorityRetained : Bool
    correctionChangesRealisedOperation : Bool
    monitoringIndependentEnoughForConsumer : Bool
    recurrencePreventionObserved : Bool
    declarationAloneSufficient : Bool
    declarationAloneSufficientIsFalse : declarationAloneSufficient ≡ false
    stateSelfReportAloneSufficient : Bool
    stateSelfReportAloneSufficientIsFalse : stateSelfReportAloneSufficient ≡ false
    consultationCountAloneSufficient : Bool
    consultationCountAloneSufficientIsFalse : consultationCountAloneSufficient ≡ false

open OperationalJusticeCompletionContract public

minimumCompletionContract : OperationalJusticeCompletionContract
minimumCompletionContract = operational-justice-completion-contract
  true true true true true
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Formal/source completion is not realised justice.
------------------------------------------------------------------------

data ArchitectureCompleteImpliesOperationalJusticeComplete : Set where
data MoreStateStatisticsPaysCommunityOutcome : Set where
data MoreCourtDoctrinePaysLandCountryControl : Set where
data ConsultationCountPaysCommunityAuthority : Set where
data CommunityEvidenceTransfersAuthorityToState : Set where
data ClosingGapTargetEqualsClosingGapOutcome : Set where

architectureCompletionDoesNotCompleteOperationalJustice :
  ArchitectureCompleteImpliesOperationalJusticeComplete → ⊥
architectureCompletionDoesNotCompleteOperationalJustice ()

moreStateStatisticsDoNotPayCommunityOutcome : MoreStateStatisticsPaysCommunityOutcome → ⊥
moreStateStatisticsDoNotPayCommunityOutcome ()

moreDoctrineDoesNotPayLandCountryControl : MoreCourtDoctrinePaysLandCountryControl → ⊥
moreDoctrineDoesNotPayLandCountryControl ()

consultationCountDoesNotPayCommunityAuthority : ConsultationCountPaysCommunityAuthority → ⊥
consultationCountDoesNotPayCommunityAuthority ()

communityEvidenceDoesNotTransferAuthorityToState :
  CommunityEvidenceTransfersAuthorityToState → ⊥
communityEvidenceDoesNotTransferAuthorityToState ()

targetDoesNotEqualOutcome : ClosingGapTargetEqualsClosingGapOutcome → ⊥
targetDoesNotEqualOutcome ()

------------------------------------------------------------------------
-- Domain fixtures remain separate: terra-nullius history and incarceration
-- operational discrepancy can feed the same generic closure architecture
-- without becoming one proposition or one causal theory.
------------------------------------------------------------------------

terraNulliusOperationalClassificationRemainsSourceBounded :
  Terra.classificationIsJuridicalNotBiological ≡ Terra.classificationIsJuridicalNotBiological
terraNulliusOperationalClassificationRemainsSourceBounded = refl

incarcerationFirstResidualRemainsCommunityOutcome :
  Incarceration.currentFirstLiveResidual ≡ Adaptive.communityOutcomeResidual
incarcerationFirstResidualRemainsCommunityOutcome = refl

------------------------------------------------------------------------
-- Roadmap boundary.
------------------------------------------------------------------------

record RoadmapBoundary : Set where
  constructor roadmap-boundary
  field
    architectureCanBeFinishedInsideRepository : Bool
    architectureCanBeFinishedInsideRepositoryIsTrue :
      architectureCanBeFinishedInsideRepository ≡ true
    realisedJusticeCanBeManufacturedByRepository : Bool
    realisedJusticeCanBeManufacturedByRepositoryIsFalse :
      realisedJusticeCanBeManufacturedByRepository ≡ false
    sourceMappingCanContinueWithoutAuthorityTransfer : Bool
    sourceMappingCanContinueWithoutAuthorityTransferIsTrue :
      sourceMappingCanContinueWithoutAuthorityTransfer ≡ true
    affectedCommunityOutcomeIsReplaceableByStateProxy : Bool
    affectedCommunityOutcomeIsReplaceableByStateProxyIsFalse :
      affectedCommunityOutcomeIsReplaceableByStateProxy ≡ false
    completionIsConsumerRelative : Bool
    completionIsConsumerRelativeIsTrue : completionIsConsumerRelative ≡ true

canonicalRoadmapBoundary : RoadmapBoundary
canonicalRoadmapBoundary = roadmap-boundary
  true refl
  false refl
  true refl
  false refl
  true refl
