module DASHI.Education.DigitalESDContributionPositioningRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDContributionPositioningExact as Position

reverseAntecedentPaidRegression :
  Position.ContributionPositionBoundary.reverseSustainabilityAntecedentPaid
    Position.canonicalContributionPositionBoundary
  ≡ true
reverseAntecedentPaidRegression = refl

reciprocalIntegrationNotPaidByChughRegression :
  Position.ContributionPositionBoundary.chughPaysReciprocalESDCapacityIntegration
    Position.canonicalContributionPositionBoundary
  ≡ false
reciprocalIntegrationNotPaidByChughRegression = refl

sameObjectDisciplineNotPaidByChughRegression :
  Position.ContributionPositionBoundary.chughPaysSameObjectPaymentDiscipline
    Position.canonicalContributionPositionBoundary
  ≡ false
sameObjectDisciplineNotPaidByChughRegression = refl

participantAuthorityNotPaidByChughRegression :
  Position.ContributionPositionBoundary.chughPaysParticipantAuthorityBoundary
    Position.canonicalContributionPositionBoundary
  ≡ false
participantAuthorityNotPaidByChughRegression = refl

noveltyStillOpenRegression :
  Position.ContributionPositionBoundary.globalNoveltyClaimPaid
    Position.canonicalContributionPositionBoundary
  ≡ false
noveltyStillOpenRegression = refl

antecedentDoesNotMakeDuplicateRegression :
  Position.CloseAntecedentAutomaticallyMakesDuplicate → ⊥
antecedentDoesNotMakeDuplicateRegression =
  Position.closeAntecedentDoesNotAutomaticallyMakeDuplicate

differenceDoesNotMakeNovelRegression :
  Position.FormalDifferenceAutomaticallyCreatesPublicationNovelty → ⊥
differenceDoesNotMakeNovelRegression =
  Position.formalDifferenceDoesNotAutomaticallyCreatePublicationNovelty
