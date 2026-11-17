module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewMechanismCrossPollinationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewMechanismCrossPollinationExact as Cross

exactReviewBindingRequired :
  Cross.exactReviewBindingRequired ≡ true
exactReviewBindingRequired = refl

genericMechanismDoesNotPayLocalCausality :
  Cross.genericMechanismPaysLocalCausality ≡ false
genericMechanismDoesNotPayLocalCausality = refl

localMechanismFitRequired :
  Cross.localMechanismFitRequired ≡ true
localMechanismFitRequired = refl

causalBridgeDoesNotPayCounterfactual :
  Cross.causalBridgePaysCounterfactual ≡ false
causalBridgeDoesNotPayCounterfactual = refl

reviewDoesNotCreateTruth :
  Cross.reviewCreatesClaimTruth ≡ false
reviewDoesNotCreateTruth = refl
