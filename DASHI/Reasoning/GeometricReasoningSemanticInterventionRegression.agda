module DASHI.Reasoning.GeometricReasoningSemanticInterventionRegression where

-- RED-first integration surface for the geometric-reasoning tranche.
-- Production owners are added in subsequent commits.  This file intentionally
-- imports the final public interfaces so the tranche has one focused kernel root.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.SemanticInterventionEquivarianceExact as Equivariance
import DASHI.Reasoning.GeometricReasoningCandidateSelectionExact as Candidates
import DASHI.Reasoning.T5E8RelativeComplementCandidateExact as E8Relative
import DASHI.Reasoning.LilaMonsterGeometricReasoningCrossPollinationExact as Cross

regressionRepresentationToModelEquivariancePaid : Bool
regressionRepresentationToModelEquivariancePaid =
  Equivariance.representationToModelEquivarianceTheoremAvailable

regressionRepresentationToModelEquivariancePaidIsTrue :
  regressionRepresentationToModelEquivariancePaid ≡ true
regressionRepresentationToModelEquivariancePaidIsTrue = refl

regressionT5Count243Paid : Bool
regressionT5Count243Paid = E8Relative.kernel5Count243Paid

regressionT5Count243PaidIsTrue :
  regressionT5Count243Paid ≡ true
regressionT5Count243PaidIsTrue = refl

regressionE8RecognitionNotAutoPromoted : Bool
regressionE8RecognitionNotAutoPromoted =
  E8Relative.e8RelativeComplementSameObjectRecognized

regressionE8RecognitionNotAutoPromotedIsFalse :
  regressionE8RecognitionNotAutoPromoted ≡ false
regressionE8RecognitionNotAutoPromotedIsFalse = refl

regressionMonster3BActionLawConsumed : Bool
regressionMonster3BActionLawConsumed = Cross.monster3BFullActionLawConsumed

regressionMonster3BActionLawConsumedIsTrue :
  regressionMonster3BActionLawConsumed ≡ true
regressionMonster3BActionLawConsumedIsTrue = refl

regressionCandidateFitDoesNotSelectMechanism : Bool
regressionCandidateFitDoesNotSelectMechanism =
  Candidates.successfulFitAutomaticallySelectsMechanism

regressionCandidateFitDoesNotSelectMechanismIsFalse :
  regressionCandidateFitDoesNotSelectMechanism ≡ false
regressionCandidateFitDoesNotSelectMechanismIsFalse = refl
