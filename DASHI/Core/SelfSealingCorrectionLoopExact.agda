module DASHI.Core.SelfSealingCorrectionLoopExact where

------------------------------------------------------------------------
-- SELF-SEALING CORRECTION LOOP
--
-- A stronger failure than ordinary observer loss occurs when evidence intended
-- to expose a blind spot is itself transformed into confirming evidence for the
-- chart that generated the blind spot.  This is the generic correction-channel
-- form later instantiated by the repository's Amalek terminalisation boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic finite correction system.
------------------------------------------------------------------------

record CorrectionLoopSystem
    (State Challenge Reading Revision : Set) : Set₁ where
  constructor correction-loop-system
  field
    challenge : State → Challenge
    institutionalReading : State → Reading
    revision : State → Revision

open CorrectionLoopSystem public

data LoopState : Set where
  ordinaryConfirmation
  blindSpotDisclosure
  : LoopState

data Challenge : Set where
  confirmingInput
  correctiveDisclosure
  : Challenge

data Reading : Set where
  confirmsExistingChart
  : Reading

data Revision : Set where
  chartUnchanged
  : Revision

loopChallenge : LoopState → Challenge
loopChallenge ordinaryConfirmation = confirmingInput
loopChallenge blindSpotDisclosure = correctiveDisclosure

loopReading : LoopState → Reading
loopReading ordinaryConfirmation = confirmsExistingChart
loopReading blindSpotDisclosure = confirmsExistingChart

loopRevision : LoopState → Revision
loopRevision ordinaryConfirmation = chartUnchanged
loopRevision blindSpotDisclosure = chartUnchanged

canonicalLoop : CorrectionLoopSystem LoopState Challenge Reading Revision
canonicalLoop = correction-loop-system loopChallenge loopReading loopRevision

challengesAreDifferent :
  loopChallenge ordinaryConfirmation ≡ loopChallenge blindSpotDisclosure → ⊥
challengesAreDifferent ()

readingsCollapseCorrectionAndConfirmation :
  loopReading ordinaryConfirmation ≡ loopReading blindSpotDisclosure
readingsCollapseCorrectionAndConfirmation = refl

revisionRemainsClosedUnderDisclosure :
  loopRevision blindSpotDisclosure ≡ chartUnchanged
revisionRemainsClosedUnderDisclosure = refl

------------------------------------------------------------------------
-- Self-sealing receipt.
------------------------------------------------------------------------

record SelfSealingCorrectionWitness
    {State Challenge Reading Revision : Set}
    (system : CorrectionLoopSystem State Challenge Reading Revision) : Set where
  constructor self-sealing-correction-witness
  field
    confirmationState disclosureState : State
    challengeDifference :
      challenge system confirmationState ≡ challenge system disclosureState → ⊥
    readingCollision :
      institutionalReading system confirmationState ≡
      institutionalReading system disclosureState
    disclosureLeavesRevisionUnchanged :
      revision system disclosureState ≡ revision system confirmationState

open SelfSealingCorrectionWitness public

canonicalSelfSealingWitness : SelfSealingCorrectionWitness canonicalLoop
canonicalSelfSealingWitness = self-sealing-correction-witness
  ordinaryConfirmation
  blindSpotDisclosure
  challengesAreDifferent
  refl
  refl

------------------------------------------------------------------------
-- The correction channel is non-separating: disclosure and confirmation become
-- observationally identical downstream.
------------------------------------------------------------------------

record CorrectionChannelBoundary : Set where
  constructor correction-channel-boundary
  field
    correctiveDisclosureCanBeCollapsedIntoConfirmation : Bool
    correctiveDisclosureCanBeCollapsedIntoConfirmationIsTrue :
      correctiveDisclosureCanBeCollapsedIntoConfirmation ≡ true
    collapsedDisclosureForcesRevision : Bool
    collapsedDisclosureForcesRevisionIsFalse :
      collapsedDisclosureForcesRevision ≡ false
    disagreementAutomaticallyMeansFault : Bool
    disagreementAutomaticallyMeansFaultIsFalse :
      disagreementAutomaticallyMeansFault ≡ false
    independentCorrectionRequiredForOpenRevision : Bool
    independentCorrectionRequiredForOpenRevisionIsTrue :
      independentCorrectionRequiredForOpenRevision ≡ true
    selfSealingPatternProvesBadIntent : Bool
    selfSealingPatternProvesBadIntentIsFalse :
      selfSealingPatternProvesBadIntent ≡ false

open CorrectionChannelBoundary public

canonicalCorrectionChannelBoundary : CorrectionChannelBoundary
canonicalCorrectionChannelBoundary = correction-channel-boundary
  true refl
  false refl
  false refl
  true refl
  false refl

------------------------------------------------------------------------
-- Exact statement of the dark epistemic possibility.
------------------------------------------------------------------------

record BlindSpotConfirmationLoop : Set where
  constructor blind-spot-confirmation-loop
  field
    chartHasBlindSpot : Bool
    chartHasBlindSpotIsTrue : chartHasBlindSpot ≡ true
    disclosureOfBlindSpotReadAsChartConfirmation : Bool
    disclosureOfBlindSpotReadAsChartConfirmationIsTrue :
      disclosureOfBlindSpotReadAsChartConfirmation ≡ true
    disclosureCausesAutomaticRevision : Bool
    disclosureCausesAutomaticRevisionIsFalse :
      disclosureCausesAutomaticRevision ≡ false
    externalCorrectionChannelIndependent : Bool
    externalCorrectionChannelIndependentIsFalse :
      externalCorrectionChannelIndependent ≡ false

open BlindSpotConfirmationLoop public

canonicalBlindSpotConfirmationLoop : BlindSpotConfirmationLoop
canonicalBlindSpotConfirmationLoop = blind-spot-confirmation-loop
  true refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- No-promotion laws.
------------------------------------------------------------------------

data SelfSealingImpliesEveryInstitutionIsMalicious : Set where
data DissentIsActuallyFault : Set where
data BlindSpotDisclosureShouldBeSuppressed : Set where
data ClosedLoopProvesUnderlyingChartTrue : Set where

selfSealingDoesNotProveUniversalMalice : SelfSealingImpliesEveryInstitutionIsMalicious → ⊥
selfSealingDoesNotProveUniversalMalice ()

dissentDoesNotBecomeFaultByReclassification : DissentIsActuallyFault → ⊥
dissentDoesNotBecomeFaultByReclassification ()

disclosureMustNotBeSuppressedByTheorem : BlindSpotDisclosureShouldBeSuppressed → ⊥
disclosureMustNotBeSuppressedByTheorem ()

closedLoopDoesNotProveChartTrue : ClosedLoopProvesUnderlyingChartTrue → ⊥
closedLoopDoesNotProveChartTrue ()
