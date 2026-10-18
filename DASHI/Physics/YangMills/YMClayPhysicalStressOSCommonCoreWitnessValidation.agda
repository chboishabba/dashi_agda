module DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact as F4

evolutionEqualityIsDerivedNotPrimitive :
  F4.evolutionEqualityPrimitivePhysicalInput ≡ false
evolutionEqualityIsDerivedNotPrimitive =
  F4.evolutionEqualityPrimitivePhysicalInputIsFalse

commonCoreDataIsPrimitiveBoundary :
  F4.commonCoreDataIsPrimitivePhysicalInput ≡ true
commonCoreDataIsPrimitiveBoundary =
  F4.commonCoreDataIsPrimitivePhysicalInputIsTrue
