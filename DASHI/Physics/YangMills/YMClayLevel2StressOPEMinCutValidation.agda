{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2StressOPEMinCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2StressOPEMinCutExact as L2

r129PaysWeldAndStressDerivative :
  L2.r129RecoveryPaysR127AndStressDerivative ≡ true
r129PaysWeldAndStressDerivative = refl

globalAFNotChargedAgain :
  L2.globalAsymptoticFreedomTrajectoryIndependentInLevel2 ≡ false
globalAFNotChargedAgain = refl

finiteWardAlgebraNotChargedAgain :
  L2.finiteWardSliceConservationIndependentInLevel2 ≡ false
finiteWardAlgebraNotChargedAgain = refl

generatedActionStressProvenanceNotChargedAgain :
  L2.generatedActionStressProvenanceIndependentInLevel2 ≡ false
generatedActionStressProvenanceNotChargedAgain = refl

dyadicDecayNotIndependent :
  L2.dyadicOPERemainderDecayIndependentAfterCompositeTailIdentification ≡ false
dyadicDecayNotIndependent = refl

allDepthCoefficientEqualityNotIndependent :
  L2.allDepthOPECoefficientEqualityIndependentAfterOneStepLaw ≡ false
allDepthCoefficientEqualityNotIndependent = refl

stressChargeNotLevel2Primitive :
  L2.stressChargeEqualsOSHamiltonianPartOfLevel2ClayMinCut ≡ false
stressChargeNotLevel2Primitive = refl

promotionFailClosed :
  L2.clayPromotion ≡ false
promotionFailClosed = refl
