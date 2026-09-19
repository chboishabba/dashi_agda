{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2WardRGReuseValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLevel2WardRGReuseExact as Reuse

globalAFIsNotChargedAgain :
  Reuse.globalAsymptoticFreedomTrajectoryIndependentInLevel2D ≡ false
globalAFIsNotChargedAgain =
  Reuse.globalAsymptoticFreedomTrajectoryIndependentInLevel2DIsFalse

finiteWardAlgebraIsNotChargedAgain :
  Reuse.finiteWardSliceConservationIndependentInLevel2D ≡ false
finiteWardAlgebraIsNotChargedAgain =
  Reuse.finiteWardSliceConservationIndependentInLevel2DIsFalse

stressProvenanceIsNotChargedAfterR136 :
  Reuse.generatedActionStressProvenanceIndependentAfterR136 ≡ false
stressProvenanceIsNotChargedAfterR136 =
  Reuse.generatedActionStressProvenanceIndependentAfterR136IsFalse

localizedD1AssemblyIsNotChargedAfterR144 :
  Reuse.localizedStressFirstVariationAssemblyIndependentAfterR144 ≡ false
localizedD1AssemblyIsNotChargedAfterR144 =
  Reuse.localizedStressFirstVariationAssemblyIndependentAfterR144IsFalse

allDepthCoefficientEqualityIsCompilerOwned :
  Reuse.allDepthOPECoefficientEqualityIndependent ≡ false
allDepthCoefficientEqualityIsCompilerOwned =
  Reuse.allDepthOPECoefficientEqualityIndependentIsFalse

dyadicRemainderDecayIsCompilerOwned :
  Reuse.dyadicOPERemainderDecayIndependent ≡ false
dyadicRemainderDecayIsCompilerOwned =
  Reuse.dyadicOPERemainderDecayIndependentIsFalse

noClayPromotion :
  Reuse.clayPromotion ≡ false
noClayPromotion = Reuse.clayPromotionIsFalse
