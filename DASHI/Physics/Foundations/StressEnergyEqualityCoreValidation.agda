{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.StressEnergyEqualityCoreValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.StressEnergyEqualityCoreExact as E
import DASHI.Physics.Foundations.CMP119GRAnchoredStressEqualityCoreExact as C

aggregationNotEqualityPremise :
  E.qftAggregationIsPremiseOfCrossSectorEquality ≡ false
aggregationNotEqualityPremise = refl

legacyAggregationNotPhysicalEqualityPremise :
  C.legacyQFTAggregationNeededForPhysicalStressEquality ≡ false
legacyAggregationNotPhysicalEqualityPremise = refl

selectedTotalStillPhysical :
  C.selectedSectorTotalEqualityStillPhysical ≡ true
selectedTotalStillPhysical = refl
