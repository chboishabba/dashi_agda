module DASHI.Cognition.Teleodynamics.E6Minuscule27WeightActionRegression where

import DASHI.Cognition.Teleodynamics.E6Minuscule27WeightActionExact as W

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

weightCountPaid : W.projectedWeightCount W.canonicalExecutionReceipt ≡ 27
weightCountPaid = refl

reflectionIntertwiningPaidAtExecutionGrade :
  W.projectionIntertwinesAllE6RootReflections W.canonicalExecutionReceipt ≡ true
reflectionIntertwiningPaidAtExecutionGrade = refl

weylActionTransitiveAtExecutionGrade :
  W.weightOrbitTransitive W.canonicalExecutionReceipt ≡ true
weylActionTransitiveAtExecutionGrade = refl

notAlbertCarrierEquality :
  W.weightOrbitIsAlbertCarrier W.canonicalBoundary ≡ false
notAlbertCarrierEquality = refl
