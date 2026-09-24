module DASHI.Law.SensibLawPersonalWorldProfessionalHandoffRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawPersonalWorldProfessionalHandoffExact as H

privateHypothesisStillPersonalOnly :
  H.privateHypothesisAutomaticallyShared
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ false
privateHypothesisStillPersonalOnly = refl

notReadyStillPersonalOnly :
  H.notReadyMaterialAutomaticallyShared
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ false
notReadyStillPersonalOnly = refl

lawyerStillGetsReviewedSelectedCoordinates :
  H.lawyerReceivesReviewedSelectedCoordinates
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ true
lawyerStillGetsReviewedSelectedCoordinates = refl

doctorStillHasDistinctSlice :
  H.doctorReceivesDistinctSlice
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ true
doctorStillHasDistinctSlice = refl

advocateStillHasDistinctSlice :
  H.advocateReceivesDistinctSlice
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ true
advocateStillHasDistinctSlice = refl

regulatorStillHasDistinctSlice :
  H.regulatorReceivesDistinctSlice
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ true
regulatorStillHasDistinctSlice = refl

handoffStillDoesNotCreateTruth :
  H.handoffCreatesClaimTruth
    H.canonicalPersonalWorldProfessionalHandoffBoundary
  ≡ false
handoffStillDoesNotCreateTruth = refl

regulatorStillDoesNotRecomputeFromEventWithoutDependency :
  H.Recompute H.regulator H.reviewedEvent → ⊥
regulatorStillDoesNotRecomputeFromEventWithoutDependency =
  H.eventDoesNotRecomputeRegulator
