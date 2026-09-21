module DASHI.Law.ReviewedWorkFrontierClosureRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ReviewedWorkFrontierClosureExact as Closure

boundary : Closure.ReviewedWorkFrontierClosureBoundary
boundary = Closure.canonicalReviewedWorkFrontierClosureBoundary

identityDoesNotResurrect :
  Closure.acceptedReviewedIdentityMayReopenItselfAsFreshSource boundary ≡ false
identityDoesNotResurrect =
  Closure.acceptedReviewedIdentityMayReopenItselfAsFreshSourceIsFalse boundary

treatmentDoesNotResurrect :
  Closure.acceptedReviewedTreatmentMayReopenItselfAsFreshTreatment boundary ≡ false
treatmentDoesNotResurrect =
  Closure.acceptedReviewedTreatmentMayReopenItselfAsFreshTreatmentIsFalse boundary

secondaryConsequencesRemainPossible :
  Closure.paidWorkMayExposeSecondaryConsequences boundary ≡ true
secondaryConsequencesRemainPossible =
  Closure.paidWorkMayExposeSecondaryConsequencesIsTrue boundary

emptyFrontierMeansClosed :
  Closure.noSelectableResidualMeansCurrentFrontierClosed boundary ≡ true
emptyFrontierMeansClosed =
  Closure.noSelectableResidualMeansCurrentFrontierClosedIsTrue boundary

closureIsNotFormalAdequacy :
  Closure.currentFrontierClosedImpliesConsumerAdequacyProved boundary ≡ false
closureIsNotFormalAdequacy =
  Closure.currentFrontierClosedImpliesConsumerAdequacyProvedIsFalse boundary

closureCreatesNoAuthority :
  Closure.currentFrontierClosedCreatesLegalAuthority boundary ≡ false
closureCreatesNoAuthority =
  Closure.currentFrontierClosedCreatesLegalAuthorityIsFalse boundary

closureCreatesNoCurrentLawConclusion :
  Closure.currentFrontierClosedCreatesCurrentLawConclusion boundary ≡ false
closureCreatesNoCurrentLawConclusion =
  Closure.currentFrontierClosedCreatesCurrentLawConclusionIsFalse boundary
